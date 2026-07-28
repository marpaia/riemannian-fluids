"""Global vector-spherical-harmonic Galerkin models on the round sphere."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

import jax.numpy as jnp

from riemannian_fluids.discrete import SemiDiscreteFlowSystem
from riemannian_fluids.operators import ViscosityModel
from riemannian_fluids.types import Array


class OneFormFamily(StrEnum):
    EXACT = "exact"
    COEXACT = "coexact"


@dataclass(frozen=True)
class SphereOneFormMode:
    degree: int
    order: int
    family: OneFormFamily

    @property
    def scalar_eigenvalue(self) -> int:
        return self.degree * (self.degree + 1)


@dataclass(frozen=True)
class SphereStokesBasis:
    """Mass-orthonormal exact/coexact one-form modes through degree ``L``."""

    maximum_degree: int

    def __post_init__(self) -> None:
        if self.maximum_degree < 1:
            raise ValueError("maximum_degree must be at least one")

    @property
    def scalar_modes(self) -> tuple[tuple[int, int], ...]:
        return tuple((degree, order) for degree in range(1, self.maximum_degree + 1) for order in range(-degree, degree + 1))

    @property
    def velocity_modes(self) -> tuple[SphereOneFormMode, ...]:
        return tuple(SphereOneFormMode(degree, order, family) for degree, order in self.scalar_modes for family in (OneFormFamily.EXACT, OneFormFamily.COEXACT))

    def divergence_matrix(self) -> Array:
        """Map one-form coefficients to scalar divergence, including pressure's constant mode."""

        matrix = jnp.zeros((1 + len(self.scalar_modes), len(self.velocity_modes)))
        for index, (degree, _) in enumerate(self.scalar_modes):
            eigenvalue = degree * (degree + 1)
            matrix = matrix.at[1 + index, 2 * index].set(-jnp.sqrt(float(eigenvalue)))
        return matrix

    def viscosity_eigenvalues(self, model: ViscosityModel | str) -> Array:
        selected = ViscosityModel(model)
        values = []
        for mode in self.velocity_modes:
            eigenvalue = float(mode.scalar_eigenvalue)
            if selected is ViscosityModel.HODGE:
                values.append(eigenvalue)
            elif selected is ViscosityModel.ROUGH:
                values.append(eigenvalue - 1.0)
            elif mode.family is OneFormFamily.COEXACT:
                values.append(eigenvalue - 2.0)
            else:
                values.append(2.0 * eigenvalue - 2.0)
        return jnp.asarray(values)

    def killing_mode_indices(self) -> tuple[int, ...]:
        return tuple(index for index, mode in enumerate(self.velocity_modes) if mode.degree == 1 and mode.family is OneFormFamily.COEXACT)

    def interpolating_viscosity_eigenvalues(self, alpha: float) -> Array:
        """Eigenvalues of the wall-selected family on the unit sphere."""

        if not 0.0 <= alpha <= 1.0:
            raise ValueError("alpha must lie in [0, 1]")
        extrinsic_shift = 2.0 * alpha + 4.0 * alpha * (1.0 - alpha)
        return self.viscosity_eigenvalues(ViscosityModel.DEFORMATION) + extrinsic_shift

    def stokes_system(
        self,
        force: Array,
        *,
        model: ViscosityModel | str = ViscosityModel.DEFORMATION,
        viscosity: float = 1.0,
        reaction: float = 0.0,
    ) -> SemiDiscreteFlowSystem:
        if force.shape != (len(self.velocity_modes),):
            raise ValueError("force must contain one coefficient per velocity mode")
        if viscosity <= 0.0 or reaction < 0.0:
            raise ValueError("viscosity must be positive and reaction nonnegative")
        operator = viscosity * jnp.diag(self.viscosity_eigenvalues(model)) + reaction * jnp.eye(len(self.velocity_modes))
        divergence = self.divergence_matrix()
        pressure_weights = jnp.zeros((divergence.shape[0],), dtype=force.dtype).at[0].set(1.0)
        return SemiDiscreteFlowSystem(
            operator,
            divergence,
            force,
            jnp.zeros((divergence.shape[0],), dtype=force.dtype),
            pressure_weights,
            name="sphere-spectral-stokes",
        )
