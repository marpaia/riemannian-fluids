"""Implicit time stepping for finite-dimensional flow residuals."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from riemannian_fluids.solvers.nonlinear import NewtonResult, newton_solve
from riemannian_fluids.types import Array


@dataclass(frozen=True)
class ImplicitEulerStep:
    previous: Array
    current: Array
    time_step: float
    nonlinear_result: NewtonResult


def implicit_euler_step(
    mass: Array,
    spatial_residual: Callable[[Array], Array],
    previous: Array,
    time_step: float,
    *,
    initial: Array | None = None,
    tolerance: float = 1.0e-10,
    max_iterations: int = 25,
) -> ImplicitEulerStep:
    if time_step <= 0.0:
        raise ValueError("time_step must be positive")

    def residual(current: Array) -> Array:
        return mass @ (current - previous) / time_step + spatial_residual(current)

    result = newton_solve(
        residual,
        previous if initial is None else initial,
        tolerance=tolerance,
        max_iterations=max_iterations,
    )
    return ImplicitEulerStep(previous, result.value, time_step, result)


def discrete_energy(mass: Array, value: Array) -> Array:
    return 0.5 * value @ mass @ value
