"""Minimal Newton solver for stationary nonlinear residuals."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import jax
import jax.numpy as jnp

from riemannian_fluids.discrete import FlowSolveResult, FlowState, SemiDiscreteFlowSystem
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
    if tolerance <= 0.0:
        raise ValueError("tolerance must be positive")
    if max_iterations < 0:
        raise ValueError("max_iterations must be nonnegative")
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


def solve_semidiscrete_flow(
    system: SemiDiscreteFlowSystem,
    *,
    initial: FlowState | None = None,
    velocity_rate: Callable[[Array], Array] | None = None,
    tolerance: float = 1.0e-10,
    max_iterations: int = 25,
) -> FlowSolveResult:
    """Solve a gauged nonlinear velocity-pressure system with dense Newton."""

    initial_state = system.zero_state() if initial is None else initial
    initial_value = jnp.concatenate((system.pack(initial_state), jnp.zeros((1,), dtype=system.velocity_operator.dtype)))
    gauge_vector = jnp.concatenate(
        (
            jnp.zeros((system.velocity_count,), dtype=system.velocity_operator.dtype),
            system.gauge_weights,
        )
    )

    def augmented_residual(value: Array) -> Array:
        state = system.unpack(value[:-1])
        rate = None if velocity_rate is None else velocity_rate(state.velocity)
        residual = system.residual(state, velocity_rate=rate)
        gauge_residual = system.gauge_weights @ state.pressure
        return jnp.concatenate((residual + value[-1] * gauge_vector, jnp.asarray((gauge_residual,))))

    nonlinear = newton_solve(
        augmented_residual,
        initial_value,
        tolerance=tolerance,
        max_iterations=max_iterations,
    )
    state = system.unpack(nonlinear.value[:-1])
    rate = None if velocity_rate is None else velocity_rate(state.velocity)
    return FlowSolveResult(
        state=state,
        diagnostics=system.diagnostics(state, velocity_rate=rate),
        converged=nonlinear.converged,
        iterations=nonlinear.iterations,
        backend="jax-dense",
        metadata={"system": system.name, "nonlinear_residual_norm": nonlinear.residual_norm},
    )


def solve_stationary_flow(
    system: SemiDiscreteFlowSystem,
    *,
    initial: FlowState | None = None,
    tolerance: float = 1.0e-10,
    max_iterations: int = 25,
) -> FlowSolveResult:
    """Solve the stationary constrained Stokes or Navier--Stokes equations."""

    return solve_semidiscrete_flow(
        system,
        initial=initial,
        tolerance=tolerance,
        max_iterations=max_iterations,
    )
