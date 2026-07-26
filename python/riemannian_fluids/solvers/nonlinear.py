"""Minimal Newton solver for stationary nonlinear residuals."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import jax
import jax.numpy as jnp

from riemannian_fluids.types import Array


@dataclass(frozen=True)
class NewtonResult:
    value: Array
    converged: bool
    iterations: int
    residual_norm: float


def newton_solve(
    residual: Callable[[Array], Array],
    initial: Array,
    *,
    tolerance: float = 1.0e-10,
    max_iterations: int = 25,
) -> NewtonResult:
    value = initial
    for iteration in range(max_iterations + 1):
        residual_value = residual(value)
        norm = float(jnp.linalg.norm(residual_value))
        if norm <= tolerance:
            return NewtonResult(value, True, iteration, norm)
        if iteration == max_iterations:
            break
        jacobian = jax.jacfwd(residual)(value)
        update = jnp.linalg.lstsq(jacobian, -residual_value, rcond=None)[0]
        value = value + update
    return NewtonResult(value, False, max_iterations, norm)
