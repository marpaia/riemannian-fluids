"""Linear incompressibility, tangency, and gauge constraints."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.types import Array


@dataclass(frozen=True)
class ConstraintDiagnostics:
    divergence: float
    tangency: float = 0.0
    pressure_mean: float = 0.0


def weighted_norm(value: Array, mass: Array) -> Array:
    return jnp.sqrt(jnp.maximum(value @ mass @ value, 0.0))


def pressure_mean(pressure: Array, weights: Array) -> Array:
    return weights @ pressure / jnp.sum(weights)


def project_linear_constraint(value: Array, constraint: Array, mass: Array) -> Array:
    """Return the mass-orthogonal projection onto ``ker(constraint)``."""

    inverse_constraint = jnp.linalg.solve(mass, constraint.T)
    multiplier = jnp.linalg.lstsq(
        constraint @ inverse_constraint,
        constraint @ value,
        rcond=None,
    )[0]
    return value - inverse_constraint @ multiplier
