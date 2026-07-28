"""Implicit time stepping for finite-dimensional flow residuals."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.discrete import FlowSolveResult, FlowState, SemiDiscreteFlowSystem
from riemannian_fluids.solvers.nonlinear import NewtonResult, newton_solve, solve_semidiscrete_flow
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


@dataclass(frozen=True)
class FlowTrajectory:
    """States and diagnostics from a transient incompressible solve."""

    initial_state: FlowState
    mass: Array
    times: Array
    results: tuple[FlowSolveResult, ...]

    @property
    def energies(self) -> Array:
        return jnp.asarray(tuple(result.diagnostics.kinetic_energy for result in self.results))

    @property
    def incompressibility_norms(self) -> Array:
        return jnp.asarray(tuple(result.diagnostics.incompressibility_norm for result in self.results))

    @property
    def energy_history(self) -> Array:
        initial_energy = discrete_energy(self.mass, self.initial_state.velocity)
        return jnp.concatenate((jnp.asarray((initial_energy,)), self.energies))


def integrate_incompressible_flow(
    system: SemiDiscreteFlowSystem,
    initial_velocity: Array,
    time_step: float,
    steps: int,
    *,
    tolerance: float = 1.0e-10,
    max_iterations: int = 25,
) -> FlowTrajectory:
    """Integrate a semidiscrete velocity-pressure system with implicit Euler."""

    if time_step <= 0.0:
        raise ValueError("time_step must be positive")
    if steps < 1:
        raise ValueError("steps must be positive")
    if initial_velocity.shape != (system.velocity_count,):
        raise ValueError("initial velocity has the wrong size")

    pressure = jnp.zeros((system.pressure_count,), dtype=initial_velocity.dtype)
    previous = FlowState(initial_velocity, pressure)
    initial_constraint = jnp.linalg.norm(system.incompressibility_residual(previous))
    if float(initial_constraint) > tolerance:
        raise ValueError("initial velocity does not satisfy the incompressibility constraint")
    results = []
    for _ in range(steps):
        previous_velocity = previous.velocity
        result = solve_semidiscrete_flow(
            system,
            initial=previous,
            velocity_rate=lambda velocity, reference=previous_velocity: (velocity - reference) / time_step,
            tolerance=tolerance,
            max_iterations=max_iterations,
        )
        results.append(result)
        previous = result.state
    return FlowTrajectory(
        initial_state=FlowState(initial_velocity, pressure),
        mass=system.mass_matrix,
        times=time_step * jnp.arange(1, steps + 1, dtype=initial_velocity.dtype),
        results=tuple(results),
    )
