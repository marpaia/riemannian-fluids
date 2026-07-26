from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.geometry import (
    extrinsic_gaussian_curvature,
    intrinsic_gaussian_curvature,
    mean_curvature,
    metric,
    shape_operator,
)
from riemannian_fluids.types import Array


def sphere(q: Array) -> Array:
    theta, phi = q
    return jnp.asarray(
        (
            jnp.sin(theta) * jnp.cos(phi),
            jnp.sin(theta) * jnp.sin(phi),
            jnp.cos(theta),
        )
    )


def test_unit_sphere_geometry() -> None:
    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)

    assert jnp.allclose(metric(sphere, q), jnp.diag(jnp.asarray((1.0, jnp.sin(q[0]) ** 2))))
    assert jnp.allclose(shape_operator(sphere, q), -jnp.eye(2), atol=1.0e-12)
    assert jnp.isclose(mean_curvature(sphere, q), -1.0, atol=1.0e-12)
    assert jnp.isclose(extrinsic_gaussian_curvature(sphere, q), 1.0, atol=1.0e-12)
    assert jnp.isclose(intrinsic_gaussian_curvature(sphere, q), 1.0, atol=1.0e-12)
