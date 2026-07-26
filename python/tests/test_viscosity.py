from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.geometry import vector_norm
from riemannian_fluids.operators import (
    deformation_laplacian,
    hodge_laplacian,
    ricci_action,
    rough_laplacian,
)
from riemannian_fluids.tensors import divergence, stream_vector_field
from riemannian_fluids.types import Array


def ellipsoid(q: Array) -> Array:
    theta, phi = q
    return jnp.asarray(
        (
            1.5 * jnp.sin(theta) * jnp.cos(phi),
            1.5 * jnp.sin(theta) * jnp.sin(phi),
            jnp.cos(theta),
        )
    )


def stream(q: Array) -> Array:
    theta, phi = q
    return jnp.sin(theta) ** 2 * jnp.cos(2.0 * phi) + 0.17 * jnp.sin(3.0 * theta) * jnp.sin(phi)


def test_divergence_free_weizenbock_and_deformation_identities() -> None:
    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)
    field = stream_vector_field(ellipsoid, stream)
    rough = rough_laplacian(ellipsoid, field, q)
    ricci = ricci_action(ellipsoid, field, q)
    hodge = hodge_laplacian(ellipsoid, field, q)
    deformation = deformation_laplacian(ellipsoid, field, q)

    assert abs(float(divergence(ellipsoid, field, q))) < 1.0e-12
    assert float(vector_norm(ellipsoid, hodge - rough - ricci, q)) < 1.0e-11
    assert float(vector_norm(ellipsoid, deformation - hodge + 2.0 * ricci, q)) < 1.0e-11
