from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.function_spaces import integrate
from riemannian_fluids.geometry import (
    CoordinateDomain,
    euclidean_submanifold,
    gauss_ricci_tensor,
    hyperbolic_geodesic_polar,
    hyperbolic_poincare_ball,
    hyperbolic_upper_half_space,
    intrinsic_ricci_tensor,
    scalar_curvature,
)


def test_hyperbolic_models_have_prescribed_curvature() -> None:
    for manifold, q in (
        (hyperbolic_upper_half_space(3, curvature=-2.25), jnp.asarray((0.2, -0.1, 1.3))),
        (hyperbolic_poincare_ball(3, curvature=-2.25), jnp.asarray((0.1, -0.2, 0.15))),
    ):
        assert jnp.isclose(scalar_curvature(manifold, q), -13.5, atol=1.0e-10)


def test_gauss_ricci_supports_codimension_two() -> None:
    def clifford_torus(q):
        return jnp.asarray((jnp.cos(q[0]), jnp.sin(q[0]), jnp.cos(q[1]), jnp.sin(q[1])))

    surface = euclidean_submanifold("Clifford torus", 2, 4, clifford_torus)
    q = jnp.asarray((0.7, 1.1), dtype=jnp.float64)
    assert jnp.allclose(
        intrinsic_ricci_tensor(surface, q),
        gauss_ricci_tensor(surface, q),
        atol=1.0e-12,
    )


def test_hyperbolic_polar_domain_and_coordinate_quadrature() -> None:
    manifold = hyperbolic_geodesic_polar(curvature=-1.0)
    domain = CoordinateDomain("annulus", manifold, ((0.2, 0.7), (0.0, 2.0 * jnp.pi)))
    area = integrate(domain, lambda q: jnp.asarray(1.0, dtype=q.dtype), order=8)
    expected = 2.0 * jnp.pi * (jnp.cosh(0.7) - jnp.cosh(0.2))
    assert jnp.isclose(area, expected, atol=1.0e-10)
