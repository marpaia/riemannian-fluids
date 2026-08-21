"""Canonical Euclidean, spherical, and hyperbolic coordinate models."""

from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.geometry.manifolds import RiemannianManifold
from riemannian_fluids.geometry.submanifolds import EmbeddedSubmanifold, euclidean_submanifold
from riemannian_fluids.types import Array


def hyperbolic_upper_half_space(
    dimension: int = 2,
    *,
    curvature: float = -1.0,
) -> RiemannianManifold:
    """Return ``H^n`` with sectional curvature ``curvature < 0``."""

    if dimension < 2:
        raise ValueError("hyperbolic space dimension must be at least two")
    if curvature >= 0.0:
        raise ValueError("hyperbolic curvature must be negative")
    scale = jnp.sqrt(-curvature)

    def metric(q: Array) -> Array:
        return jnp.eye(dimension, dtype=q.dtype) / (scale * q[-1]) ** 2

    bounds = ((None, None),) * (dimension - 1) + ((0.0, None),)
    return RiemannianManifold(
        f"H^{dimension}({curvature:g})",
        dimension,
        metric,
        bounds,
    )


def hyperbolic_poincare_ball(
    dimension: int = 2,
    *,
    curvature: float = -1.0,
) -> RiemannianManifold:
    if dimension < 2:
        raise ValueError("hyperbolic space dimension must be at least two")
    if curvature >= 0.0:
        raise ValueError("hyperbolic curvature must be negative")
    scale_squared = -curvature

    def metric(q: Array) -> Array:
        conformal = 2.0 / (jnp.sqrt(scale_squared) * (1.0 - q @ q))
        return conformal**2 * jnp.eye(dimension, dtype=q.dtype)

    return RiemannianManifold(f"B^{dimension}({curvature:g})", dimension, metric)


def hyperbolic_geodesic_polar(*, curvature: float = -1.0) -> RiemannianManifold:
    """Return ``H^2`` in geodesic-polar coordinates ``(r, theta)``."""

    if curvature >= 0.0:
        raise ValueError("hyperbolic curvature must be negative")
    scale = jnp.sqrt(-curvature)

    def metric(q: Array) -> Array:
        radial = jnp.sinh(scale * q[0]) / scale
        return jnp.diag(jnp.asarray((1.0, radial**2)))

    return RiemannianManifold(
        f"H^2_polar({curvature:g})",
        2,
        metric,
        ((0.0, None), (0.0, 2.0 * float(jnp.pi))),
    )


def sphere(radius: float = 1.0) -> EmbeddedSubmanifold:
    if radius <= 0.0:
        raise ValueError("radius must be positive")

    def embedding(q: Array) -> Array:
        theta, phi = q
        return radius * jnp.asarray(
            (
                jnp.sin(theta) * jnp.cos(phi),
                jnp.sin(theta) * jnp.sin(phi),
                jnp.cos(theta),
            )
        )

    return euclidean_submanifold(
        f"S^2({radius:g})",
        2,
        3,
        embedding,
        coordinate_bounds=((0.0, float(jnp.pi)), (0.0, 2.0 * float(jnp.pi))),
    )


def torus_of_revolution(major_radius: float = 1.8, minor_radius: float = 0.55) -> EmbeddedSubmanifold:
    """Return the torus swept by a circle of radius ``minor_radius`` about the axis."""

    if minor_radius <= 0.0 or major_radius <= minor_radius:
        raise ValueError("torus radii must satisfy 0 < minor_radius < major_radius")

    def embedding(q: Array) -> Array:
        theta, phi = q
        radial = major_radius + minor_radius * jnp.cos(theta)
        return jnp.asarray(
            (
                radial * jnp.cos(phi),
                radial * jnp.sin(phi),
                minor_radius * jnp.sin(theta),
            )
        )

    return euclidean_submanifold(
        "torus of revolution",
        2,
        3,
        embedding,
        coordinate_bounds=((0.0, 2.0 * float(jnp.pi)), (0.0, 2.0 * float(jnp.pi))),
    )


def spheroid(equatorial_radius: float = 1.5, polar_radius: float = 1.0) -> EmbeddedSubmanifold:
    if equatorial_radius <= 0.0 or polar_radius <= 0.0:
        raise ValueError("spheroid radii must be positive")

    def embedding(q: Array) -> Array:
        theta, phi = q
        return jnp.asarray(
            (
                equatorial_radius * jnp.sin(theta) * jnp.cos(phi),
                equatorial_radius * jnp.sin(theta) * jnp.sin(phi),
                polar_radius * jnp.cos(theta),
            )
        )

    return euclidean_submanifold(
        "spheroid",
        2,
        3,
        embedding,
        coordinate_bounds=((0.0, float(jnp.pi)), (0.0, 2.0 * float(jnp.pi))),
    )
