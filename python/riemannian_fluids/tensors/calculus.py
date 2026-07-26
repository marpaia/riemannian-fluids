"""Coordinate expressions for covariant differential calculus."""

from __future__ import annotations

from collections.abc import Callable

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry import Geometry, christoffel_symbols, dimension, metric
from riemannian_fluids.types import Array, ScalarField, VectorField


def lower_index(geometry: Geometry, vector: Array, q: Array) -> Array:
    return metric(geometry, q) @ vector


def raise_index(geometry: Geometry, covector: Array, q: Array) -> Array:
    return jnp.linalg.solve(metric(geometry, q), covector)


def stream_vector_field(geometry: Geometry, stream: ScalarField) -> VectorField:
    """Construct ``sharp(*d psi)`` on an oriented two-manifold."""

    def field(q: Array) -> Array:
        if dimension(geometry, q) != 2:
            raise ValueError("a scalar stream function represents velocity only in dimension two")
        derivative = jax.jacfwd(stream)(q)
        area_density = jnp.sqrt(jnp.linalg.det(metric(geometry, q)))
        return jnp.asarray((derivative[1], -derivative[0])) / area_density

    return field


def covariant_derivative_vector(
    geometry: Geometry,
    field: VectorField,
    q: Array,
) -> Array:
    """Return ``nabla_u[k,i] = nabla_i u^k``."""

    value = field(q)
    derivative = jax.jacfwd(field)(q)
    gamma = christoffel_symbols(geometry, q)
    return derivative + jnp.einsum("kil,l->ki", gamma, value)


def divergence(geometry: Geometry, field: VectorField, q: Array) -> Array:
    return jnp.trace(covariant_derivative_vector(geometry, field, q))


def gradient(geometry: Geometry, scalar: ScalarField, q: Array) -> Array:
    return raise_index(geometry, jax.jacfwd(scalar)(q), q)


def covariant_derivative_covector(
    geometry: Geometry,
    covector: Callable[[Array], Array],
    q: Array,
) -> Array:
    """Return ``nabla_alpha[j,i] = nabla_i alpha_j``."""

    value = covector(q)
    derivative = jax.jacfwd(covector)(q)
    gamma = christoffel_symbols(geometry, q)
    return derivative - jnp.einsum("kij,k->ji", gamma, value)


def deformation_tensor(geometry: Geometry, field: VectorField, q: Array) -> Array:
    def lowered(point: Array) -> Array:
        return lower_index(geometry, field(point), point)

    derivative = covariant_derivative_covector(geometry, lowered, q)
    return 0.5 * (derivative + derivative.T)


def lie_derivative_metric(geometry: Geometry, field: VectorField, q: Array) -> Array:
    g = metric(geometry, q)
    dg = jax.jacfwd(lambda point: metric(geometry, point))(q)
    value = field(q)
    derivative = jax.jacfwd(field)(q)
    transport = jnp.einsum("k,ijk->ij", value, dg)
    first_slot = jnp.einsum("kj,ki->ij", g, derivative)
    second_slot = jnp.einsum("ik,kj->ij", g, derivative)
    return transport + first_slot + second_slot


def exterior_derivative_one_form(geometry: Geometry, field: VectorField, q: Array) -> Array:
    def lowered(point: Array) -> Array:
        return lower_index(geometry, field(point), point)

    derivative = jax.jacfwd(lowered)(q)
    return derivative.T - derivative


def lie_bracket(first: VectorField, second: VectorField, q: Array) -> Array:
    derivative_first = jax.jacfwd(first)(q)
    derivative_second = jax.jacfwd(second)(q)
    return derivative_second @ first(q) - derivative_first @ second(q)


def covariant_advection(
    geometry: Geometry,
    advecting: VectorField,
    field: VectorField,
    q: Array,
) -> Array:
    """Return ``nabla_advecting field``."""

    return covariant_derivative_vector(geometry, field, q) @ advecting(q)


def raised_lie_derivative_one_form(
    geometry: Geometry,
    generator: VectorField,
    field: VectorField,
    q: Array,
) -> Array:
    """Return ``sharp(L_generator(field-flat))`` in local coordinates."""

    def one_form(point: Array) -> Array:
        return lower_index(geometry, field(point), point)

    covector = one_form(q)
    covector_derivative = jax.jacfwd(one_form)(q)
    generator_derivative = jax.jacfwd(generator)(q)
    lie_covector = covector_derivative @ generator(q) + generator_derivative.T @ covector
    return raise_index(geometry, lie_covector, q)
