"""Symmetry reduction of chart integrals to one-dimensional radial integrals."""

from __future__ import annotations

from dataclasses import dataclass

import sympy

from riemannian_fluids.symbolic.certificates import DerivationLedger
from riemannian_fluids.symbolic.charts import SymbolicManifold
from riemannian_fluids.symbolic.energy.domains import DomainSpec, radial_interval
from riemannian_fluids.symbolic.simplify import expression_size, simp


class ReductionError(ValueError):
    """The integrand cannot be reduced on this chart."""


@dataclass(frozen=True)
class RadialIntegral:
    integrand: sympy.Expr
    variable: sympy.Symbol
    interval: tuple[sympy.Expr, sympy.Expr]


def reduce_to_radial(
    chart: SymbolicManifold,
    density: sympy.Expr,
    domain: DomainSpec,
    ledger: DerivationLedger | None = None,
) -> tuple[RadialIntegral, DerivationLedger]:
    """Reduce ``integral density dV`` over a radial domain to a single radial integral.

    The volume element is attached from the chart's declared density.  An
    integrand independent of the angular coordinate contributes its exact
    angular measure; otherwise the angular integral is evaluated symbolically
    and a failure there is an explicit error, never a silent approximation.
    """

    if chart.dimension != 2:
        raise ReductionError("radial reduction currently supports two-dimensional charts")
    ledger = ledger or DerivationLedger()
    radial, angular = chart.coords
    full = density * chart.volume_density
    before = expression_size(full)
    full = simp(full)
    ledger = ledger.record("volume-element", f"attached dV = {chart.volume_density} d{radial} d{angular}", before, expression_size(full))

    angular_lower, angular_upper = chart.bounds[1]
    if angular_lower is None or angular_upper is None:
        raise ReductionError(f"{chart.name}: angular coordinate {angular} must have finite bounds")

    if not full.has(angular):
        measure = simp(angular_upper - angular_lower)
        reduced = measure * full
        ledger = ledger.record("symmetry", f"integrand is {angular}-independent; angular measure {measure}", expression_size(full), expression_size(reduced))
    else:
        reduced = sympy.integrate(full, (angular, angular_lower, angular_upper))
        if reduced.has(sympy.Integral):
            raise ReductionError(f"{chart.name}: angular integral over {angular} did not evaluate")
        reduced = simp(reduced)
        description = f"integrated over {angular} in ({angular_lower}, {angular_upper})"
        ledger = ledger.record("angular-integral", description, expression_size(full), expression_size(reduced))

    return RadialIntegral(reduced, radial, radial_interval(chart, domain)), ledger
