"""Validate constrained stationary and transient semidiscrete Navier--Stokes."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence

import jax.numpy as jnp

from riemannian_fluids.discrete import FlowState
from riemannian_fluids.discretization.manufactured import (
    stationary_navier_stokes_reference,
    transient_dissipative_reference,
)
from riemannian_fluids.solvers import integrate_incompressible_flow, solve_stationary_flow


def run_study(*, time_step: float, steps: int) -> dict[str, object]:
    reference = stationary_navier_stokes_reference()
    exact = reference.exact_state
    stationary = solve_stationary_flow(
        reference.system,
        initial=FlowState(0.5 * exact.velocity, jnp.zeros_like(exact.pressure)),
    )
    transient_system = transient_dissipative_reference()
    trajectory = integrate_incompressible_flow(
        transient_system,
        exact.velocity,
        time_step,
        steps,
    )
    velocity_error = float(jnp.linalg.norm(stationary.state.velocity - exact.velocity))
    pressure_error = float(jnp.linalg.norm(stationary.state.pressure - exact.pressure))
    energies = tuple(float(value) for value in trajectory.energy_history)
    incompressibility = tuple(float(value) for value in trajectory.incompressibility_norms)
    return {
        "evidence_class": "manufactured finite-dimensional nonlinear solve",
        "stationary": {
            "converged": stationary.converged,
            "iterations": stationary.iterations,
            "velocity_error": velocity_error,
            "pressure_error": pressure_error,
            "momentum_residual": stationary.diagnostics.momentum_residual_norm,
            "incompressibility_residual": stationary.diagnostics.incompressibility_norm,
            "pressure_mean": stationary.diagnostics.pressure_mean,
            "convection_power": float(reference.convection.power(exact.velocity)),
        },
        "transient": {
            "time_step": time_step,
            "steps": steps,
            "all_steps_converged": all(result.converged for result in trajectory.results),
            "energies": energies,
            "max_incompressibility_residual": max(incompressibility),
            "energy_is_strictly_decreasing": all(right < left for left, right in zip(energies, energies[1:], strict=False)),
        },
    }


def validate_results(result: dict[str, object], *, tolerance: float) -> None:
    stationary = result["stationary"]
    transient = result["transient"]
    assert isinstance(stationary, dict)
    assert isinstance(transient, dict)
    failures = []
    if not stationary["converged"]:
        failures.append("stationary Newton solve did not converge")
    for key in ("velocity_error", "pressure_error", "momentum_residual", "incompressibility_residual", "pressure_mean", "convection_power"):
        if abs(float(stationary[key])) > tolerance:
            failures.append(f"stationary {key} exceeded tolerance")
    if not transient["all_steps_converged"]:
        failures.append("a transient nonlinear solve did not converge")
    if float(transient["max_incompressibility_residual"]) > tolerance:
        failures.append("transient incompressibility residual exceeded tolerance")
    if not transient["energy_is_strictly_decreasing"]:
        failures.append("unforced transient energy did not decrease")
    if failures:
        raise AssertionError("Navier--Stokes validation failed:\n  " + "\n  ".join(failures))


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--time-step", type=float, default=0.05)
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    if args.time_step <= 0.0 or args.steps < 2 or args.tolerance <= 0.0:
        parser.error("time step and tolerance must be positive; steps must be at least two")
    result = run_study(time_step=args.time_step, steps=args.steps)
    validate_results(result, tolerance=args.tolerance)
    if args.as_json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return
    stationary = result["stationary"]
    transient = result["transient"]
    assert isinstance(stationary, dict)
    assert isinstance(transient, dict)
    print("manufactured semidiscrete Navier--Stokes")
    print(f"stationary velocity error: {float(stationary['velocity_error']):.3e}")
    print(f"stationary pressure error: {float(stationary['pressure_error']):.3e}")
    print(f"maximum transient divergence: {float(transient['max_incompressibility_residual']):.3e}")
    print(f"transient energies: {transient['energies']}")


if __name__ == "__main__":
    main()
