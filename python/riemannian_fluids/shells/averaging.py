"""Transverse averaging on tubular coordinates."""

from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.types import Array


def tubular_jacobian(shape: Array, r: Array | float) -> Array:
    """Return ``det(I-rS)`` relative to surface measure."""

    return jnp.linalg.det(jnp.eye(shape.shape[0], dtype=shape.dtype) - r * shape)


def transverse_average(values: Array, weights: Array, jacobians: Array | None = None) -> Array:
    """Average samples along the normal direction using supplied quadrature weights."""

    effective = weights if jacobians is None else weights * jacobians
    return jnp.einsum("r,r...->...", effective, values) / jnp.sum(effective)
