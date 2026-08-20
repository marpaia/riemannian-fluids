"""Energy-integral solver: domains, symmetry reduction, and certified radial integration."""

from riemannian_fluids.symbolic.energy.domains import (
    DomainSpec,
    ExteriorOfBall,
    FullManifold,
    GeodesicBall,
    RadialAnnulus,
    radial_interval,
)
from riemannian_fluids.symbolic.energy.reduce import RadialIntegral, reduce_to_radial
from riemannian_fluids.symbolic.energy.solve import (
    EnergyIntegralResult,
    deformation_energy_density,
    dirichlet_energy_density,
    energy_integral,
    verify_numerically,
)

__all__ = [
    "DomainSpec",
    "EnergyIntegralResult",
    "ExteriorOfBall",
    "FullManifold",
    "GeodesicBall",
    "RadialAnnulus",
    "RadialIntegral",
    "deformation_energy_density",
    "dirichlet_energy_density",
    "energy_integral",
    "radial_interval",
    "reduce_to_radial",
    "verify_numerically",
]
