from __future__ import annotations

import jax.numpy as jnp
import pytest

from experiments.surfaces import surface_cases
from riemannian_fluids.geometry import shape_operator
from riemannian_fluids.shells import (
    asymptotic_wall_jets,
    solenoidal_corrector_amplitude,
    solve_two_wall_tangential_field,
    wall_residual,
)
from riemannian_fluids.tensors import stream_vector_field


@pytest.mark.parametrize("alpha", [0.0, 0.5, 1.0])
def test_quadratic_profile_satisfies_both_wall_laws(alpha: float) -> None:
    shape = jnp.asarray(((-0.7, 0.1), (0.0, 0.4)), dtype=jnp.float64)
    u0 = jnp.asarray((0.8, -0.3), dtype=jnp.float64)
    wall_field = solve_two_wall_tangential_field(shape, u0, 0.1, alpha)

    for sign in (-1, 1):
        assert jnp.linalg.norm(wall_residual(shape, wall_field, 0.1, alpha, sign)) < 1.0e-12


def test_finite_thickness_coefficients_converge_to_matched_jets() -> None:
    shape = jnp.asarray(((-0.7, 0.1), (0.0, 0.4)), dtype=jnp.float64)
    u0 = jnp.asarray((0.8, -0.3), dtype=jnp.float64)
    alpha = 0.5
    expected_u1, expected_u2 = asymptotic_wall_jets(shape, u0, alpha)

    coarse = solve_two_wall_tangential_field(shape, u0, 0.2, alpha)
    fine = solve_two_wall_tangential_field(shape, u0, 0.05, alpha)

    assert jnp.linalg.norm(fine.u1 - expected_u1) < jnp.linalg.norm(coarse.u1 - expected_u1)
    assert jnp.linalg.norm(fine.u2 - expected_u2) < jnp.linalg.norm(coarse.u2 - expected_u2)


def test_spherical_solenoidal_corrector_vanishes() -> None:
    sphere = surface_cases()[0]
    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)
    field = stream_vector_field(sphere.embedding, sphere.stream_function)

    assert abs(float(solenoidal_corrector_amplitude(sphere.embedding, field, q, 0.5))) < 1.0e-12
    shape = shape_operator(sphere.embedding, q)
    assert jnp.linalg.norm(shape - 0.5 * jnp.trace(shape) * jnp.eye(2)) < 1.0e-12
