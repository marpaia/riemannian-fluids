"""Problem and resolution contracts for resolved thin-shell studies."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from riemannian_fluids.geometry import EmbeddedSubmanifold
from riemannian_fluids.types import VectorField


class WallLaw(StrEnum):
    NAVIER = "navier"
    HODGE = "hodge"
    PARTIAL_SLIP = "partial-slip"


@dataclass(frozen=True)
class ShellResolution:
    """Independent tangential and normal resolution of a volume shell."""

    tangential_size: float
    normal_layers: int

    def __post_init__(self) -> None:
        if self.tangential_size <= 0.0:
            raise ValueError("tangential_size must be positive")
        if self.normal_layers < 2:
            raise ValueError("normal_layers must be at least two")

    def h_over_thickness(self, thickness: float) -> float:
        if thickness <= 0.0:
            raise ValueError("thickness must be positive")
        return self.tangential_size / thickness


@dataclass(frozen=True)
class ResolvedShellProblem:
    """A three-dimensional incompressible Stokes problem in a tubular shell."""

    surface: EmbeddedSubmanifold
    thickness: float
    force: VectorField
    wall_law: WallLaw = WallLaw.NAVIER
    alpha: float = 0.0
    viscosity: float = 1.0

    def __post_init__(self) -> None:
        if self.surface.dimension != 2 or self.surface.ambient_dimension != 3:
            raise ValueError("the current resolved-shell contract is for surfaces in R^3")
        if self.thickness <= 0.0:
            raise ValueError("thickness must be positive")
        if self.viscosity <= 0.0:
            raise ValueError("viscosity must be positive")
        if self.wall_law is WallLaw.PARTIAL_SLIP and not 0.0 <= self.alpha <= 1.0:
            raise ValueError("partial-slip alpha must lie in [0, 1]")


@dataclass(frozen=True)
class ShellSolveDiagnostics:
    thickness: float
    tangential_size: float
    normal_layers: int
    divergence_l2: float
    wall_residual_l2: float
    pressure_mean: float
    averaged_surface_error_l2: float

    @property
    def h_over_thickness(self) -> float:
        return self.tangential_size / self.thickness
