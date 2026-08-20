"""Worked examples for the symbolic energy-integral solver.

Each section is one complete workflow: construct a structured field on a
chart, build its energy density, solve the integral over a domain, and read
the certificate, the derivation ledger, and the numeric verification.  The
examples mirror the hyperbolic exterior-domain energy computations of the
Chan--Czubak program.

Run from the repository root with ``pixi run --locked symbolic-examples``.
"""

from __future__ import annotations

import sympy

from riemannian_fluids.symbolic import (
    coexact_field,
    hyperbolic_polar_chart,
    positive_symbols,
    sphere_chart,
    torus_chart,
)
from riemannian_fluids.symbolic.energy import (
    ExteriorOfBall,
    deformation_energy_density,
    energy_integral,
    verify_numerically,
)
from riemannian_fluids.symbolic.energy.identities import deformation_energy_identity, verify_divfree_def_hodge


def _banner(title: str) -> None:
    print(f"\n{'=' * 88}\n{title}\n{'=' * 88}")


def exact_exterior_energy() -> None:
    _banner("1. Exact closed form: deformation energy on the hyperbolic exterior domain")
    a, r0 = positive_symbols("a R0")
    chart = hyperbolic_polar_chart(-(a**2))
    r = chart.coords[0]
    field = coexact_field(chart, sympy.exp(-2 * a * r))
    print(f"chart: {chart.name} with coordinates {chart.coords}")
    print(f"field: u = sharp(*d psi), psi = exp(-2*a*r)  ->  components {field.components()}")

    density = deformation_energy_density(field)
    print(f"\nenergy density 2|Def u|^2 = {density}")

    result = energy_integral(density, chart, ExteriorOfBall(r0))
    print(f"\ndomain: {result.domain.describe()}")
    print(f"radial integrand: {result.radial.integrand}")
    print(f"closed form:\n{sympy.pretty(result.closed_form)}")
    print(f"certificate: {result.certificate}")
    print("\nderivation ledger:")
    print(result.ledger.render())

    check = verify_numerically(result, {a: 1.1, r0: 0.7})
    print(f"\nquadrature verification at a=1.1, R0=0.7: scaled error {check.max_error:.2e} (passed={check.passed})")


def honest_verdicts() -> None:
    _banner("2. Honest verdicts: divergence and undecidable parameter relations")
    r0 = positive_symbols("R0")[0]
    slow = hyperbolic_polar_chart(-1)
    field = coexact_field(slow, sympy.exp(-sympy.Rational(1, 5) * slow.coords[0]))
    result = energy_integral(deformation_energy_density(field), slow, ExteriorOfBall(r0))
    print("stream psi = exp(-r/5) on H^2(-1): decay is too slow against the sinh(r) volume growth")
    print(f"  -> {result.certificate}")

    a, b = positive_symbols("a b")
    generic = hyperbolic_polar_chart(-(a**2))
    field = coexact_field(generic, sympy.exp(-b * generic.coords[0]))
    result = energy_integral(deformation_energy_density(field), generic, ExteriorOfBall(r0))
    print("\nstream psi = exp(-b*r) with independent rates a, b: finiteness depends on sign(2b - a)")
    print(f"  -> {result.certificate}")


def integration_by_parts() -> None:
    _banner("3. Integration by parts: <L_Def u, u> = 2|Def u|^2 - div F with the wall flux explicit")
    a, b = positive_symbols("a b")
    chart = hyperbolic_polar_chart(-(a**2))
    field = coexact_field(chart, sympy.exp(-b * chart.coords[0]))
    identity = deformation_energy_identity(field)
    print(f"pointwise residual vanishes: {identity.holds}")
    print(f"boundary flux F = 2 Def(u)^sharp . u: {identity.flux}")
    print(f"flux through the geodesic circle r = c, per unit angle: {identity.radial_boundary_integrand()}")


def weitzenbock_theorems() -> None:
    _banner("4. Chart-level theorems: L_Def = L_Hodge - 2 Ric for a GENERIC stream function")
    a = positive_symbols("a")[0]
    charts = (sphere_chart(1), hyperbolic_polar_chart(-(a**2)), torus_chart(*positive_symbols("Rmaj rmin")))
    for chart in charts:
        q0, q1 = chart.coords
        field = coexact_field(chart, sympy.Function("psi", real=True)(q0, q1))
        verdict = verify_divfree_def_hodge(field)
        print(f"{chart.name}: identity holds for every stream function psi({q0}, {q1}): {verdict}")


def main() -> None:
    exact_exterior_energy()
    honest_verdicts()
    integration_by_parts()
    weitzenbock_theorems()


if __name__ == "__main__":
    main()
