"""Surface patches and divergence-free fields used by the numerical studies."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.types import Array, Embedding, ScalarField


@dataclass(frozen=True)
class SurfaceCase:
    name: str
    embedding: Embedding
    stream_function: ScalarField
    first_range: tuple[float, float]
    second_range: tuple[float, float]


def surface_cases() -> tuple[SurfaceCase, ...]:
    def sphere(q: Array) -> Array:
        theta, phi = q
        return jnp.asarray(
            (
                jnp.sin(theta) * jnp.cos(phi),
                jnp.sin(theta) * jnp.sin(phi),
                jnp.cos(theta),
            )
        )

    def ellipsoid(q: Array) -> Array:
        return sphere(q) * jnp.asarray((1.5, 1.5, 1.0))

    def torus(q: Array) -> Array:
        theta, phi = q
        major_radius = 1.8
        minor_radius = 0.55
        radial = major_radius + minor_radius * jnp.cos(theta)
        return jnp.asarray(
            (
                radial * jnp.cos(phi),
                radial * jnp.sin(phi),
                minor_radius * jnp.sin(theta),
            )
        )

    def perturbed_sphere(q: Array) -> Array:
        theta, phi = q
        radius = 1.0 + 0.11 * jnp.sin(2.0 * theta) * jnp.cos(3.0 * phi)
        return radius * sphere(q)

    def spherical_stream(q: Array) -> Array:
        theta, phi = q
        return jnp.sin(theta) ** 2 * jnp.cos(2.0 * phi) + 0.17 * jnp.sin(3.0 * theta) * jnp.sin(phi)

    def torus_stream(q: Array) -> Array:
        theta, phi = q
        return jnp.sin(theta) + 0.31 * jnp.cos(2.0 * phi) + 0.19 * jnp.sin(theta + phi)

    spherical_patch = (0.35, jnp.pi - 0.35)
    angular_patch = (0.17, 2.0 * jnp.pi - 0.17)
    return (
        SurfaceCase("sphere", sphere, spherical_stream, spherical_patch, angular_patch),
        SurfaceCase("ellipsoid", ellipsoid, spherical_stream, spherical_patch, angular_patch),
        SurfaceCase("torus_of_revolution", torus, torus_stream, angular_patch, angular_patch),
        SurfaceCase(
            "perturbed_sphere",
            perturbed_sphere,
            spherical_stream,
            spherical_patch,
            angular_patch,
        ),
    )


def sample_points(case: SurfaceCase, count: int) -> Array:
    first = jnp.linspace(case.first_range[0], case.first_range[1], count)
    second = jnp.linspace(case.second_range[0], case.second_range[1], count + 1)
    grid_first, grid_second = jnp.meshgrid(first, second, indexing="ij")
    return jnp.stack((grid_first.ravel(), grid_second.ravel()), axis=1)
