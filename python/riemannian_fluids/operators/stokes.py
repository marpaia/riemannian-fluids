"""Coordinate and algebraic forms of incompressible Riemannian Stokes flow."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.geometry import Geometry, metric
from riemannian_fluids.operators.viscosity import ViscosityModel, viscosity_operator
from riemannian_fluids.tensors import deformation_tensor, divergence, gradient
from riemannian_fluids.types import Array, ScalarField, VectorField


@dataclass(frozen=True)
class SurfaceStokesProblem:
    """Strong-form data for ``nu L u + grad p = f, div u = 0``."""

    geometry: Geometry
    force: VectorField
    viscosity: float = 1.0
    model: ViscosityModel = ViscosityModel.DEFORMATION

    def momentum_residual(
        self,
        velocity: VectorField,
        pressure: ScalarField,
        q: Array,
    ) -> Array:
        operator = viscosity_operator(self.model)
        return self.viscosity * operator(self.geometry, velocity, q) + gradient(self.geometry, pressure, q) - self.force(q)

    def incompressibility_residual(self, velocity: VectorField, q: Array) -> Array:
        return divergence(self.geometry, velocity, q)


def kinetic_energy_density(geometry: Geometry, velocity: VectorField, q: Array) -> Array:
    value = velocity(q)
    return 0.5 * value @ metric(geometry, q) @ value


def deformation_dissipation_density(
    geometry: Geometry,
    velocity: VectorField,
    q: Array,
    viscosity: float = 1.0,
) -> Array:
    deformation = deformation_tensor(geometry, velocity, q)
    inverse = jnp.linalg.inv(metric(geometry, q))
    squared_norm = jnp.einsum("ia,jb,ij,ab->", inverse, inverse, deformation, deformation)
    return 2.0 * viscosity * squared_norm


@dataclass(frozen=True)
class MixedStokesSystem:
    """Discrete saddle system ``[A B^T; B 0][u,p]=[f,g]``."""

    velocity_operator: Array
    divergence: Array
    force: Array
    constraint: Array
    pressure_weights: Array | None = None

    def block_matrix(self) -> Array:
        pressure_count = self.divergence.shape[0]
        zero = jnp.zeros((pressure_count, pressure_count), dtype=self.velocity_operator.dtype)
        return jnp.block([[self.velocity_operator, self.divergence.T], [self.divergence, zero]])

    def right_hand_side(self) -> Array:
        return jnp.concatenate((self.force, self.constraint))
