"""Intrinsic and extrinsic differential geometry in local coordinates."""

from __future__ import annotations

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry.manifolds import RiemannianManifold, euclidean_space
from riemannian_fluids.geometry.submanifolds import (
    EmbeddedSubmanifold,
    embedding_jacobian,
    normal_frame,
)
from riemannian_fluids.types import Array, Embedding

type Geometry = Embedding | RiemannianManifold | EmbeddedSubmanifold


def dimension(geometry: Geometry, q: Array) -> int:
    if isinstance(geometry, (RiemannianManifold, EmbeddedSubmanifold)):
        return geometry.dimension
    return int(q.shape[0])


def metric(geometry: Geometry, q: Array) -> Array:
    if isinstance(geometry, (RiemannianManifold, EmbeddedSubmanifold)):
        return geometry.metric(q)
    tangents = embedding_jacobian(geometry, q)
    return tangents.T @ tangents


def christoffel_symbols(geometry: Geometry, q: Array) -> Array:
    """Return ``Gamma[k,i,j] = Gamma^k_ij``."""

    g = metric(geometry, q)
    inverse = jnp.linalg.inv(g)
    derivative = jax.jacfwd(lambda point: metric(geometry, point))(q)
    n = dimension(geometry, q)
    first_kind = jnp.empty((n, n, n), dtype=q.dtype)
    for i in range(n):
        for j in range(n):
            for ell in range(n):
                first_kind = first_kind.at[i, j, ell].set(
                    0.5 * (derivative[j, ell, i] + derivative[i, ell, j] - derivative[i, j, ell])
                )
    return jnp.einsum("kl,ijl->kij", inverse, first_kind)


def riemann_curvature_tensor(geometry: Geometry, q: Array) -> Array:
    """Return ``R[i,j,k,l] = R^i_jkl``."""

    gamma = christoffel_symbols(geometry, q)
    derivative = jax.jacfwd(lambda point: christoffel_symbols(geometry, point))(q)
    return (
        jnp.swapaxes(derivative, 2, 3)
        - derivative
        + jnp.einsum("imk,mjl->ijkl", gamma, gamma)
        - jnp.einsum("iml,mjk->ijkl", gamma, gamma)
    )


def intrinsic_ricci_tensor(geometry: Geometry, q: Array) -> Array:
    """Compute the covariant Ricci tensor from the Levi-Civita connection."""

    gamma = christoffel_symbols(geometry, q)
    derivative = jax.jacfwd(lambda point: christoffel_symbols(geometry, point))(q)
    return (
        jnp.einsum("kijk->ij", derivative)
        - jnp.einsum("kikj->ij", derivative)
        + jnp.einsum("kij,lkl->ij", gamma, gamma)
        - jnp.einsum("kil,ljk->ij", gamma, gamma)
    )


def scalar_curvature(geometry: Geometry, q: Array) -> Array:
    return jnp.einsum(
        "ij,ij->", jnp.linalg.inv(metric(geometry, q)), intrinsic_ricci_tensor(geometry, q)
    )


def intrinsic_gaussian_curvature(geometry: Geometry, q: Array) -> Array:
    if dimension(geometry, q) != 2:
        raise ValueError("Gaussian curvature is defined here only in intrinsic dimension two")
    return 0.5 * scalar_curvature(geometry, q)


def second_fundamental_form_vector(
    geometry: Embedding | EmbeddedSubmanifold,
    q: Array,
) -> Array:
    """Return the ambient-coordinate vector-valued second fundamental form."""

    if isinstance(geometry, EmbeddedSubmanifold):
        embedding = geometry.embedding
        ambient = geometry.ambient
    else:
        embedding = geometry
        ambient = euclidean_space(int(embedding(q).shape[0]))

    tangent = embedding_jacobian(geometry, q)
    second = jax.jacfwd(jax.jacfwd(embedding))(q)
    ambient_gamma = christoffel_symbols(ambient, embedding(q))
    intrinsic_gamma = christoffel_symbols(geometry, q)
    ambient_connection = jnp.einsum("abc,bi,cj->aij", ambient_gamma, tangent, tangent)
    tangential_connection = jnp.einsum("kij,ak->aij", intrinsic_gamma, tangent)
    return second + ambient_connection - tangential_connection


def second_fundamental_forms(
    geometry: Embedding | EmbeddedSubmanifold,
    q: Array,
) -> Array:
    """Return scalar second fundamental forms, one per normal direction."""

    vector_form = second_fundamental_form_vector(geometry, q)
    frame = normal_frame(geometry, q)
    if isinstance(geometry, EmbeddedSubmanifold):
        ambient_metric = geometry.ambient.metric(geometry.embedding(q))
    else:
        ambient_metric = jnp.eye(frame.shape[0], dtype=q.dtype)
    return jnp.einsum("ac,ab,bij->cij", frame, ambient_metric, vector_form)


def second_fundamental_form(
    geometry: Embedding | EmbeddedSubmanifold,
    q: Array,
) -> Array:
    forms = second_fundamental_forms(geometry, q)
    if forms.shape[0] != 1:
        raise ValueError("use second_fundamental_forms for higher-codimension embeddings")
    return forms[0]


def shape_operators(geometry: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    inverse = jnp.linalg.inv(metric(geometry, q))
    return jnp.einsum("ij,ajk->aik", inverse, second_fundamental_forms(geometry, q))


def shape_operator(geometry: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    shapes = shape_operators(geometry, q)
    if shapes.shape[0] != 1:
        raise ValueError("use shape_operators for higher-codimension embeddings")
    return shapes[0]


def mean_curvature_vector(geometry: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    """Return the ambient mean-curvature vector using normalized trace."""

    traces = jnp.trace(shape_operators(geometry, q), axis1=1, axis2=2)
    coefficients = traces / dimension(geometry, q)
    return normal_frame(geometry, q) @ coefficients


def mean_curvature(geometry: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    """Return signed mean curvature for a hypersurface."""

    shapes = shape_operators(geometry, q)
    if shapes.shape[0] != 1:
        raise ValueError("mean_curvature is scalar only for a hypersurface")
    return jnp.trace(shapes[0]) / dimension(geometry, q)


def extrinsic_gaussian_curvature(
    geometry: Embedding | EmbeddedSubmanifold,
    q: Array,
) -> Array:
    if dimension(geometry, q) != 2:
        raise ValueError("Gaussian curvature is defined here only in intrinsic dimension two")
    return jnp.sum(jax.vmap(jnp.linalg.det)(shape_operators(geometry, q)))


def gauss_ricci_tensor(geometry: Embedding | EmbeddedSubmanifold, q: Array) -> Array:
    """Return the Euclidean-submanifold Ricci tensor from the Gauss equation."""

    forms = second_fundamental_forms(geometry, q)
    shapes = shape_operators(geometry, q)
    first = jnp.einsum("a,aij->ij", jnp.trace(shapes, axis1=1, axis2=2), forms)
    second = jnp.einsum("aik,akj->ij", forms, shapes)
    return first - second


def tangent_coordinates(
    geometry: Embedding | EmbeddedSubmanifold,
    ambient_vector: Array,
    q: Array,
) -> Array:
    """Return coordinates of an ambient vector's tangent projection."""

    tangents = embedding_jacobian(geometry, q)
    if isinstance(geometry, EmbeddedSubmanifold):
        ambient_metric = geometry.ambient.metric(geometry.embedding(q))
    else:
        ambient_metric = jnp.eye(tangents.shape[0], dtype=q.dtype)
    return jnp.linalg.solve(metric(geometry, q), tangents.T @ ambient_metric @ ambient_vector)


def vector_squared_norm(geometry: Geometry, vector: Array, q: Array) -> Array:
    return jnp.maximum(vector @ metric(geometry, q) @ vector, 0.0)


def vector_norm(geometry: Geometry, vector: Array, q: Array) -> Array:
    return jnp.sqrt(vector_squared_norm(geometry, vector, q))


def covariant_tensor_norm(geometry: Geometry, tensor: Array, q: Array) -> Array:
    inverse = jnp.linalg.inv(metric(geometry, q))
    squared = jnp.einsum("ik,jl,ij,kl->", inverse, inverse, tensor, tensor)
    return jnp.sqrt(jnp.maximum(squared, 0.0))
