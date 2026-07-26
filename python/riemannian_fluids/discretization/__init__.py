"""Backend capability declarations and optional numerical realizations."""

from riemannian_fluids.discretization.capabilities import (
    FENICSX_CAPABILITIES,
    JAX_CAPABILITIES,
    SPHERE_SPECTRAL_CAPABILITIES,
    BackendCapabilities,
)
from riemannian_fluids.discretization.fenicsx import solve_normal_fibre
from riemannian_fluids.discretization.sphere_spectral import (
    OneFormFamily,
    SphereOneFormMode,
    SphereStokesBasis,
)

__all__ = (
    "FENICSX_CAPABILITIES",
    "JAX_CAPABILITIES",
    "SPHERE_SPECTRAL_CAPABILITIES",
    "BackendCapabilities",
    "OneFormFamily",
    "SphereOneFormMode",
    "SphereStokesBasis",
    "solve_normal_fibre",
)
