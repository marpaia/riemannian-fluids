"""Typed dense semidiscrete systems for incompressible reference flows."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, field

import jax.numpy as jnp

from riemannian_fluids.types import Array

ConvectionOperator = Callable[[Array], Array]


@dataclass(frozen=True)
class FlowState:
    """Velocity and pressure coefficients in a discrete incompressible system."""

    velocity: Array
    pressure: Array


@dataclass(frozen=True)
class FlowDiagnostics:
    """Norms whose meaning is shared by stationary and transient solvers."""

    momentum_residual_norm: float
    incompressibility_norm: float
    pressure_mean: float
    kinetic_energy: float


@dataclass(frozen=True)
class FlowSolveResult:
    """A solved state together with numerical and provenance metadata."""

    state: FlowState
    diagnostics: FlowDiagnostics
    converged: bool
    iterations: int
    backend: str
    metadata: Mapping[str, float | int | str] = field(default_factory=dict)


@dataclass(frozen=True)
class QuadraticConvection:
    """Dense quadratic convection ``N_i(u)=C_ijk u_j u_k``."""

    tensor: Array

    def __post_init__(self) -> None:
        if self.tensor.ndim != 3 or len(set(self.tensor.shape)) != 1:
            raise ValueError("convection tensor must have shape (n, n, n)")

    def __call__(self, velocity: Array) -> Array:
        if velocity.shape != (self.tensor.shape[0],):
            raise ValueError("velocity has the wrong size for the convection tensor")
        return jnp.einsum("ijk,j,k->i", self.tensor, velocity, velocity)

    def power(self, velocity: Array) -> Array:
        return velocity @ self(velocity)


@dataclass(frozen=True)
class SemiDiscreteFlowSystem:
    """Dense reference realization of an incompressible semidiscrete flow.

    The equations are

    ``M u_dot + A u + N(u) + B^T p = f`` and ``B u = g``.

    The field order intentionally begins with the historical mixed-Stokes data
    so ``MixedStokesSystem(A, B, f, g, weights)`` remains source compatible.
    """

    velocity_operator: Array
    divergence: Array
    force: Array
    constraint: Array
    pressure_weights: Array | None = None
    mass: Array | None = None
    convection: ConvectionOperator | None = None
    name: str = "dense-incompressible-flow"

    def __post_init__(self) -> None:
        if self.velocity_operator.ndim != 2:
            raise ValueError("velocity operator must be a matrix")
        if self.divergence.ndim != 2:
            raise ValueError("divergence must be a matrix")
        velocity_count = self.velocity_operator.shape[0]
        pressure_count = self.divergence.shape[0]
        if velocity_count < 1 or pressure_count < 1:
            raise ValueError("flow systems need velocity and pressure degrees of freedom")
        if self.velocity_operator.shape != (velocity_count, velocity_count):
            raise ValueError("velocity operator must be square")
        if self.divergence.shape[1] != velocity_count:
            raise ValueError("divergence and velocity operator sizes disagree")
        if self.force.shape != (velocity_count,):
            raise ValueError("force must contain one value per velocity degree of freedom")
        if self.constraint.shape != (pressure_count,):
            raise ValueError("constraint must contain one value per pressure degree of freedom")
        if self.mass is not None and self.mass.shape != self.velocity_operator.shape:
            raise ValueError("mass and velocity operator sizes disagree")
        if self.pressure_weights is not None and self.pressure_weights.shape != (pressure_count,):
            raise ValueError("pressure weights must contain one value per pressure degree of freedom")
        if float(jnp.abs(jnp.sum(self.gauge_weights))) == 0.0:
            raise ValueError("pressure weights must define a nonzero gauge")

    @property
    def velocity_count(self) -> int:
        return self.velocity_operator.shape[0]

    @property
    def pressure_count(self) -> int:
        return self.divergence.shape[0]

    @property
    def mass_matrix(self) -> Array:
        if self.mass is None:
            return jnp.eye(self.velocity_count, dtype=self.velocity_operator.dtype)
        return self.mass

    @property
    def gauge_weights(self) -> Array:
        if self.pressure_weights is None:
            return jnp.ones((self.pressure_count,), dtype=self.velocity_operator.dtype)
        return self.pressure_weights

    def block_matrix(self) -> Array:
        zero = jnp.zeros((self.pressure_count, self.pressure_count), dtype=self.velocity_operator.dtype)
        return jnp.block([[self.velocity_operator, self.divergence.T], [self.divergence, zero]])

    def right_hand_side(self) -> Array:
        return jnp.concatenate((self.force, self.constraint))

    def pack(self, state: FlowState) -> Array:
        return jnp.concatenate((state.velocity, state.pressure))

    def unpack(self, value: Array) -> FlowState:
        expected = self.velocity_count + self.pressure_count
        if value.shape != (expected,):
            raise ValueError(f"state vector has shape {value.shape}; expected {(expected,)}")
        return FlowState(value[: self.velocity_count], value[self.velocity_count :])

    def zero_state(self) -> FlowState:
        dtype = self.velocity_operator.dtype
        return FlowState(jnp.zeros((self.velocity_count,), dtype=dtype), jnp.zeros((self.pressure_count,), dtype=dtype))

    def convection_action(self, velocity: Array) -> Array:
        if self.convection is None:
            return jnp.zeros_like(velocity)
        return self.convection(velocity)

    def momentum_residual(
        self,
        state: FlowState,
        *,
        velocity_rate: Array | None = None,
    ) -> Array:
        rate = jnp.zeros_like(state.velocity) if velocity_rate is None else velocity_rate
        return (
            self.mass_matrix @ rate
            + self.velocity_operator @ state.velocity
            + self.convection_action(state.velocity)
            + self.divergence.T @ state.pressure
            - self.force
        )

    def incompressibility_residual(self, state: FlowState) -> Array:
        return self.divergence @ state.velocity - self.constraint

    def residual(self, state: FlowState, *, velocity_rate: Array | None = None) -> Array:
        return jnp.concatenate(
            (
                self.momentum_residual(state, velocity_rate=velocity_rate),
                self.incompressibility_residual(state),
            )
        )

    def pressure_mean(self, pressure: Array) -> Array:
        weights = self.gauge_weights
        return weights @ pressure / jnp.sum(weights)

    def diagnostics(self, state: FlowState, *, velocity_rate: Array | None = None) -> FlowDiagnostics:
        momentum = self.momentum_residual(state, velocity_rate=velocity_rate)
        incompressibility = self.incompressibility_residual(state)
        energy = 0.5 * state.velocity @ self.mass_matrix @ state.velocity
        return FlowDiagnostics(
            momentum_residual_norm=float(jnp.linalg.norm(momentum)),
            incompressibility_norm=float(jnp.linalg.norm(incompressibility)),
            pressure_mean=float(self.pressure_mean(state.pressure)),
            kinetic_energy=float(energy),
        )


# Compatibility name for callers that only use the linear specialization.
MixedStokesSystem = SemiDiscreteFlowSystem
