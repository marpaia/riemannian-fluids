"""Analysis-positive rough, Hodge, and deformation viscosity operators."""

from __future__ import annotations

from collections.abc import Callable
from enum import StrEnum

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry import (
    EmbeddedSubmanifold,
    Geometry,
    christoffel_symbols,
    dimension,
    intrinsic_ricci_tensor,
    metric,
    shape_operator,
)
from riemannian_fluids.tensors import (
    covariant_derivative_vector,
    deformation_tensor,
    divergence,
    exterior_derivative_one_form,
)
from riemannian_fluids.types import Array, Embedding, VectorField

VectorOperator = Callable[[Geometry, VectorField, Array], Array]


class ViscosityModel(StrEnum):
    ROUGH = "rough"
    HODGE = "hodge"
    DEFORMATION = "deformation"


def rough_laplacian(geometry: Geometry, field: VectorField, q: Array) -> Array:
    """Return the positive connection Laplacian ``-tr_g(nabla^2 u)``."""

    inverse = jnp.linalg.inv(metric(geometry, q))
    gamma = christoffel_symbols(geometry, q)
    first = covariant_derivative_vector(geometry, field, q)
    partial_first = jax.jacfwd(lambda point: covariant_derivative_vector(geometry, field, point))(q)
    n = dimension(geometry, q)
    second = jnp.empty((n, n, n), dtype=q.dtype)
    for component in range(n):
        for first_index in range(n):
            for second_index in range(n):
                value = partial_first[component, second_index, first_index]
                value += jnp.einsum(
                    "l,l->", gamma[component, first_index, :], first[:, second_index]
                )
                value -= jnp.einsum(
                    "l,l->", gamma[:, first_index, second_index], first[component, :]
                )
                second = second.at[component, second_index, first_index].set(value)
    return -jnp.einsum("ij,kji->k", inverse, second)


def ricci_action(geometry: Geometry, field: VectorField, q: Array) -> Array:
    inverse = jnp.linalg.inv(metric(geometry, q))
    return inverse @ intrinsic_ricci_tensor(geometry, q) @ field(q)


def deformation_laplacian(geometry: Geometry, field: VectorField, q: Array) -> Array:
    """Return the positive operator ``2 Def* Def``."""

    inverse = jnp.linalg.inv(metric(geometry, q))
    gamma = christoffel_symbols(geometry, q)
    tensor = deformation_tensor(geometry, field, q)
    derivative = jax.jacfwd(lambda point: deformation_tensor(geometry, field, point))(q)
    n = dimension(geometry, q)
    covariant = jnp.empty((n, n, n), dtype=q.dtype)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                value = derivative[i, j, k]
                value -= jnp.einsum("l,l->", gamma[:, k, i], tensor[:, j])
                value -= jnp.einsum("l,l->", gamma[:, k, j], tensor[i, :])
                covariant = covariant.at[i, j, k].set(value)
    divergence_covector = jnp.einsum("ik,ijk->j", inverse, covariant)
    return -2.0 * inverse @ divergence_covector


def hodge_laplacian(geometry: Geometry, field: VectorField, q: Array) -> Array:
    """Return ``sharp((d delta + delta d)(u-flat))``."""

    inverse = jnp.linalg.inv(metric(geometry, q))
    gamma = christoffel_symbols(geometry, q)

    def delta_one_form(point: Array) -> Array:
        return -divergence(geometry, field, point)

    d_delta = jax.jacfwd(delta_one_form)(q)
    two_form = exterior_derivative_one_form(geometry, field, q)
    derivative = jax.jacfwd(lambda point: exterior_derivative_one_form(geometry, field, point))(q)
    n = dimension(geometry, q)
    covariant = jnp.empty((n, n, n), dtype=q.dtype)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                value = derivative[i, j, k]
                value -= jnp.einsum("l,l->", gamma[:, k, i], two_form[:, j])
                value -= jnp.einsum("l,l->", gamma[:, k, j], two_form[i, :])
                covariant = covariant.at[i, j, k].set(value)
    delta_two_form = -jnp.einsum("jk,jik->i", inverse, covariant)
    return inverse @ (d_delta + delta_two_form)


def shape_square_action(
    geometry: Embedding | EmbeddedSubmanifold,
    field: VectorField,
    q: Array,
) -> Array:
    shape = shape_operator(geometry, q)
    return shape @ shape @ field(q)


def interpolating_viscosity(
    geometry: Embedding | EmbeddedSubmanifold,
    field: VectorField,
    q: Array,
    alpha: float,
) -> Array:
    """Return ``L_Def + 2 alpha Ric + 4 alpha(1-alpha) S^2``."""

    return (
        deformation_laplacian(geometry, field, q)
        + 2.0 * alpha * ricci_action(geometry, field, q)
        + 4.0 * alpha * (1.0 - alpha) * shape_square_action(geometry, field, q)
    )


def viscosity_operator(model: ViscosityModel | str) -> VectorOperator:
    return {
        ViscosityModel.ROUGH: rough_laplacian,
        ViscosityModel.HODGE: hodge_laplacian,
        ViscosityModel.DEFORMATION: deformation_laplacian,
    }[ViscosityModel(model)]
