"""Worked examples for the symbolic thin-shell solver.

The sections build the normal shell of the unit sphere, construct the two-wall
rotational profile for a symbolic wall parameter alpha, and extract the
wall-selected surface eigenvalue from the transverse-averaged operator
pairing.  The limit reproduces the interpolating viscosity family
``L_Def + 2 alpha Ric + 4 alpha (1 - alpha) S^2`` on the rotational mode.
The final sections construct the arbitrary smooth-core recovery at both
endpoint laws and retain an exactly integrated Navier regression mode.

Run from the repository root with ``pixi run --locked symbolic-examples``.
"""

from __future__ import annotations

import sympy

from riemannian_fluids.symbolic import positive_symbols, sphere_chart
from riemannian_fluids.symbolic.shells import (
    RecoveryEndpoint,
    canonical_navier_torus_recovery,
    canonical_torus_smooth_recovery,
    pairing_eigenvalue,
    rotational_mode_eigenvalue,
    sphere_shell_chart,
    transverse_average,
    two_wall_rotational_field,
)

EPS = positive_symbols("varepsilon")[0]
ALPHA = sympy.Symbol("alpha", nonnegative=True)


def _banner(title: str) -> None:
    print(f"\n{'=' * 88}\n{title}\n{'=' * 88}")


def shell_geometry() -> None:
    _banner("1. The tube chart: exact geometry of the spherical shell")
    chart = sphere_shell_chart(1)
    print(f"shell chart: {chart.shell.name} with coordinates {chart.shell.coords}")
    print(f"shell metric:\n{sympy.pretty(chart.shell.metric)}")
    print(f"shape operator of the level sphere at distance sigma:\n{sympy.pretty(chart.shape_operator)}")
    print(f"tube jacobian det(I - sigma S) = {chart.jacobian}   (terminating polynomial, not a truncation)")


def transverse_averaging() -> None:
    _banner("2. Transverse averaging with tracked truncation")
    chart = sphere_shell_chart(1)
    averaged = transverse_average(sympy.Integer(1), chart, EPS, order=2)
    print(f"per-unit-thickness average of 1 over the shell: {averaged.as_expr()} + O({EPS}**3)")
    print("reading a coefficient beyond the tracked order raises TruncationError; dropped terms are unrepresentable")


def wall_selected_eigenvalue() -> None:
    _banner("3. The wall-selected eigenvalue: lambda_alpha = 6*alpha - 4*alpha**2")
    chart = sphere_shell_chart(1)
    field = two_wall_rotational_field(chart, ALPHA, EPS)
    print(f"two-wall rotational profile (wall law d_sigma U = 2*alpha*S(sigma)*U at sigma = +-{EPS}):")
    print(f"  p(sigma) = {sympy.expand(field.profile)}")

    eigenvalue = pairing_eigenvalue(field, order=1)
    limit = sympy.expand(eigenvalue.coeff(0))
    print(f"\ntransverse-averaged pairing <L_Def U, U> / |U|^2 as {EPS} -> 0:")
    print(f"  lambda(alpha) = {limit}")
    print(
        f"  endpoints: alpha=0 (Navier/stress-free) -> {limit.subs(ALPHA, 0)}, "
        f"alpha=1 (Hodge/vorticity-free) -> {limit.subs(ALPHA, 1)}"
    )


def interpolating_family() -> None:
    _banner("4. Agreement with the surface family L_Def + 2*alpha*Ric + 4*alpha*(1-alpha)*S^2")
    surface = sphere_chart(1)
    shape = sympy.ImmutableMatrix([[-1, 0], [0, -1]])
    surface_eigenvalue = rotational_mode_eigenvalue(surface, ALPHA, shape)
    print(f"rotational-mode eigenvalue of L(alpha) on the unit sphere: {sympy.expand(surface_eigenvalue)}")

    chart = sphere_shell_chart(1)
    shell_limit = pairing_eigenvalue(two_wall_rotational_field(chart, ALPHA, EPS), order=1).coeff(0)
    print(f"thin-shell limit minus surface family: {sympy.expand(shell_limit - surface_eigenvalue)}")
    print("\nalpha      thin-shell limit    surface family")
    for alpha in (0, sympy.Rational(1, 4), sympy.Rational(1, 2), sympy.Rational(3, 4), 1):
        row = (str(alpha), str(shell_limit.subs(ALPHA, alpha)), str(surface_eigenvalue.subs(ALPHA, alpha)))
        print(f"{row[0]:<10} {row[1]:<19} {row[2]}")


def smooth_core_recovery() -> None:
    _banner("5. Every smooth solenoidal torus field: exact recovery at both endpoints")
    for endpoint in RecoveryEndpoint:
        certificate = canonical_torus_smooth_recovery(endpoint, EPS)
        print(f"{endpoint.value}:")
        print(f"  surface field: stream-plus-flux components {certificate.surface_field.components}")
        print(f"  surface/shell divergence: {certificate.surface_divergence}, {certificate.shell_divergence}")
        print(f"  inner/outer normal traces: {certificate.wall_normal_traces}")
        print(f"  inner/outer wall residuals: {certificate.wall_law_residuals}")
        print(f"  transverse identification: {certificate.transverse_flux_average}")
        print(f"  scope: {certificate.scope}")


def integrated_recovery_regression() -> None:
    _banner("6. Closed mass and energy for the Navier regression mode")
    certificate = canonical_navier_torus_recovery(EPS)
    print(f"surface field: {certificate.surface_components}")
    print(f"shell field:   {certificate.shell_components},  |sigma| < {EPS}")
    print(f"surface/shell divergence: {certificate.surface_divergence}, {certificate.shell_divergence}")
    print(f"inner/outer normal traces: {certificate.wall_normal_traces}")
    print(f"inner/outer stress residuals: {certificate.wall_stress_residuals}")
    print(f"normalized transverse average: {certificate.weighted_transverse_average}")
    print(f"surface L2 norm squared: {certificate.surface_l2_norm_squared}")
    print(f"normalized shell L2 norm squared: {certificate.normalized_shell_l2_norm_squared}")
    print(f"quadratic norm-defect coefficient: {certificate.norm_error_coefficient}")
    print(f"surface deformation energy: {certificate.surface_energy}")
    print(f"normalized shell deformation energy: {certificate.normalized_shell_energy}")
    print(f"quadratic energy-defect coefficient: {certificate.energy_error_coefficient}")
    print(f"scope: {certificate.scope}")


def main() -> None:
    shell_geometry()
    transverse_averaging()
    wall_selected_eigenvalue()
    interpolating_family()
    smooth_core_recovery()
    integrated_recovery_regression()


if __name__ == "__main__":
    main()
