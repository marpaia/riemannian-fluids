"""Strong-form Riemannian Navier--Stokes equations."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.geometry import Geometry, metric
from riemannian_fluids.operators.stokes import SurfaceStokesProblem
from riemannian_fluids.operators.viscosity import viscosity_operator
from riemannian_fluids.tensors import covariant_advection, gradient
from riemannian_fluids.types import Array, ScalarField, VectorField


@dataclass(frozen=True)
class SurfaceNavierStokesProblem(SurfaceStokesProblem):
    """Strong-form data for incompressible surface Navier--Stokes flow."""

    def momentum_residual(
        self,
        velocity: VectorField,
        pressure: ScalarField,
        q: Array,
        *,
        time_derivative: Array | None = None,
    ) -> Array:
        unsteady = jnp.zeros_like(velocity(q)) if time_derivative is None else time_derivative
        return (
            unsteady
            + covariant_advection(self.geometry, velocity, velocity, q)
            + self.viscosity * viscosity_operator(self.model)(self.geometry, velocity, q)
            + gradient(self.geometry, pressure, q)
            - self.force(q)
        )


def convective_power_density(geometry: Geometry, velocity: VectorField, q: Array) -> Array:
    """Return ``<nabla_u u,u>`` for local energy-balance diagnostics."""

    value = velocity(q)
    advection = covariant_advection(geometry, velocity, velocity, q)
    return value @ metric(geometry, q) @ advection
