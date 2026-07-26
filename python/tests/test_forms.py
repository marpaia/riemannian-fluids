from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.geometry import euclidean_space
from riemannian_fluids.tensors import (
    DifferentialFormField,
    codifferential,
    exterior_derivative,
    hodge_laplacian,
    hodge_star,
)


def test_exterior_derivative_squares_to_zero() -> None:
    plane = euclidean_space(2)
    scalar = DifferentialFormField(plane, 0, lambda q: q[0] ** 2 * q[1])
    q = jnp.asarray((0.3, -0.7), dtype=jnp.float64)
    assert jnp.allclose(exterior_derivative(exterior_derivative(scalar))(q), 0.0)


def test_hodge_star_and_codifferential_on_plane() -> None:
    plane = euclidean_space(2)
    dx = DifferentialFormField(plane, 1, lambda q: jnp.asarray((1.0, 0.0), dtype=q.dtype))
    radial = DifferentialFormField(plane, 1, lambda q: jnp.asarray((q[0], 0.0)))
    q = jnp.asarray((0.3, -0.7), dtype=jnp.float64)
    assert jnp.allclose(hodge_star(dx)(q), jnp.asarray((0.0, 1.0)))
    assert jnp.allclose(hodge_star(hodge_star(dx))(q), -dx(q))
    assert jnp.isclose(codifferential(radial)(q), -1.0)


def test_hodge_laplacian_of_scalar_is_positive_laplacian() -> None:
    plane = euclidean_space(2)
    scalar = DifferentialFormField(plane, 0, lambda q: q @ q)
    q = jnp.asarray((0.3, -0.7), dtype=jnp.float64)
    assert jnp.isclose(hodge_laplacian(scalar)(q), -4.0)
