"""Geometric fluid operators and equation data."""

from riemannian_fluids.operators.navier_stokes import (
    SurfaceNavierStokesProblem,
    convective_power_density,
)
from riemannian_fluids.operators.scaling import (
    ellipsoid_2025_candidates,
    ellipsoid_scaling_generator,
)
from riemannian_fluids.operators.stokes import (
    MixedStokesSystem,
    SurfaceStokesProblem,
    deformation_dissipation_density,
    kinetic_energy_density,
)
from riemannian_fluids.operators.viscosity import (
    ViscosityModel,
    deformation_laplacian,
    hodge_laplacian,
    interpolating_viscosity,
    ricci_action,
    rough_laplacian,
    shape_square_action,
    viscosity_operator,
)

__all__ = (
    "MixedStokesSystem",
    "SurfaceNavierStokesProblem",
    "SurfaceStokesProblem",
    "ViscosityModel",
    "convective_power_density",
    "deformation_dissipation_density",
    "deformation_laplacian",
    "ellipsoid_2025_candidates",
    "ellipsoid_scaling_generator",
    "hodge_laplacian",
    "interpolating_viscosity",
    "kinetic_energy_density",
    "ricci_action",
    "rough_laplacian",
    "shape_square_action",
    "viscosity_operator",
)
