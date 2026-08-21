"""Thin-shell solver: tube charts, wall-typed ansatz fields, and epsilon-graded limits."""

from riemannian_fluids.symbolic.shells.ansatz import RotationalShellField, two_wall_rotational_field
from riemannian_fluids.symbolic.shells.limits import (
    interpolating_operator,
    pairing_eigenvalue,
    rotational_mode_eigenvalue,
    transverse_average,
)
from riemannian_fluids.symbolic.shells.recovery import (
    CanonicalTorusSolenoidalField,
    NavierTorusRecoveryCertificate,
    RecoveryConstructionError,
    RecoveryEndpoint,
    TorusEndpointRecoveryCertificate,
    TorusRecoveryRateCertificate,
    canonical_navier_torus_recovery,
    canonical_torus_smooth_recovery,
    canonical_torus_smooth_recovery_rate,
    canonical_torus_smooth_solenoidal_field,
)
from riemannian_fluids.symbolic.shells.tube import ShellChart, sphere_shell_chart, torus_shell_chart

__all__ = [
    "RotationalShellField",
    "CanonicalTorusSolenoidalField",
    "NavierTorusRecoveryCertificate",
    "RecoveryEndpoint",
    "RecoveryConstructionError",
    "ShellChart",
    "TorusEndpointRecoveryCertificate",
    "TorusRecoveryRateCertificate",
    "canonical_navier_torus_recovery",
    "canonical_torus_smooth_recovery",
    "canonical_torus_smooth_recovery_rate",
    "canonical_torus_smooth_solenoidal_field",
    "interpolating_operator",
    "pairing_eigenvalue",
    "rotational_mode_eigenvalue",
    "sphere_shell_chart",
    "torus_shell_chart",
    "transverse_average",
    "two_wall_rotational_field",
]
