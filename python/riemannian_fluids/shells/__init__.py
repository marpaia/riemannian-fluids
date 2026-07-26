"""Tubular geometry, wall fields, averaging, and resolved-shell contracts."""

from riemannian_fluids.shells.averaging import transverse_average, tubular_jacobian
from riemannian_fluids.shells.fermi import (
    AmbientJets,
    TwoWallTangentialField,
    ambient_cartesian_field,
    ambient_positive_laplacian_cartesian,
    ambient_positive_laplacian_tangent,
    ambient_restriction_formula,
    asymptotic_wall_jets,
    fermi_divergence,
    fermi_map,
    fermi_metric,
    finite_thickness_jets,
    matched_wall_jets,
    parallel_shape,
    solenoidal_corrector_amplitude,
    solve_two_wall_tangential_field,
    wall_residual,
)
from riemannian_fluids.shells.problems import (
    ResolvedShellProblem,
    ShellResolution,
    ShellSolveDiagnostics,
    WallLaw,
)

__all__ = (
    "AmbientJets",
    "ResolvedShellProblem",
    "ShellResolution",
    "ShellSolveDiagnostics",
    "TwoWallTangentialField",
    "WallLaw",
    "ambient_cartesian_field",
    "ambient_positive_laplacian_cartesian",
    "ambient_positive_laplacian_tangent",
    "ambient_restriction_formula",
    "asymptotic_wall_jets",
    "fermi_divergence",
    "fermi_map",
    "fermi_metric",
    "finite_thickness_jets",
    "matched_wall_jets",
    "parallel_shape",
    "solenoidal_corrector_amplitude",
    "solve_two_wall_tangential_field",
    "transverse_average",
    "tubular_jacobian",
    "wall_residual",
)
