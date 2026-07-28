"""Small manufactured systems for solver-level Navier--Stokes validation."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.discrete import FlowState, QuadraticConvection, SemiDiscreteFlowSystem


@dataclass(frozen=True)
class ManufacturedFlow:
    """A semidiscrete system with a known stationary state."""

    system: SemiDiscreteFlowSystem
    exact_state: FlowState
    convection: QuadraticConvection


def energy_preserving_convection() -> QuadraticConvection:
    """Return a nonzero quadratic map satisfying ``u . N(u) = 0``."""

    tensor = jnp.zeros((3, 3, 3), dtype=jnp.float64)
    tensor = tensor.at[0, 1, 2].set(0.2)
    tensor = tensor.at[2, 1, 0].set(-0.2)
    tensor = tensor.at[1, 2, 0].set(-0.1)
    tensor = tensor.at[0, 2, 1].set(0.1)
    return QuadraticConvection(tensor)


def pressure_gauged_divergence() -> jnp.ndarray:
    """Return a rank-one constraint with a one-dimensional pressure gauge."""

    row = jnp.asarray((1.0, 1.0, 1.0), dtype=jnp.float64)
    return jnp.stack((row, -row))


def stationary_navier_stokes_reference() -> ManufacturedFlow:
    """Construct a nonlinear constrained system with a prescribed solution."""

    convection = energy_preserving_convection()
    velocity = jnp.asarray((1.0, -2.0, 1.0), dtype=jnp.float64)
    pressure = jnp.asarray((0.3, -0.3), dtype=jnp.float64)
    operator = jnp.diag(jnp.asarray((2.0, 3.0, 4.0), dtype=jnp.float64))
    divergence = pressure_gauged_divergence()
    force = operator @ velocity + convection(velocity) + divergence.T @ pressure
    system = SemiDiscreteFlowSystem(
        operator,
        divergence,
        force,
        jnp.zeros((2,), dtype=jnp.float64),
        jnp.ones((2,), dtype=jnp.float64),
        convection=convection,
        name="manufactured-stationary-navier-stokes",
    )
    return ManufacturedFlow(system, FlowState(velocity, pressure), convection)


def transient_dissipative_reference() -> SemiDiscreteFlowSystem:
    """Construct an unforced constrained flow with energy-preserving advection."""

    return SemiDiscreteFlowSystem(
        jnp.eye(3, dtype=jnp.float64),
        pressure_gauged_divergence(),
        jnp.zeros((3,), dtype=jnp.float64),
        jnp.zeros((2,), dtype=jnp.float64),
        jnp.ones((2,), dtype=jnp.float64),
        mass=jnp.eye(3, dtype=jnp.float64),
        convection=energy_preserving_convection(),
        name="transient-incompressible-reference",
    )
