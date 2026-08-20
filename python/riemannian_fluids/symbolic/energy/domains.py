"""Radially described integration domains on a chart whose first coordinate is radial."""

from __future__ import annotations

from dataclasses import dataclass

import sympy

from riemannian_fluids.symbolic.charts import SymbolicManifold


class DomainError(ValueError):
    """The domain is incompatible with the chart's radial bounds."""


@dataclass(frozen=True)
class FullManifold:
    def describe(self) -> str:
        return "the full chart"


@dataclass(frozen=True)
class GeodesicBall:
    radius: sympy.Expr

    def describe(self) -> str:
        return f"the geodesic ball of radius {self.radius}"


@dataclass(frozen=True)
class ExteriorOfBall:
    radius: sympy.Expr

    def describe(self) -> str:
        return f"the exterior of the geodesic ball of radius {self.radius}"


@dataclass(frozen=True)
class RadialAnnulus:
    inner: sympy.Expr
    outer: sympy.Expr

    def describe(self) -> str:
        return f"the radial annulus ({self.inner}, {self.outer})"


type DomainSpec = FullManifold | GeodesicBall | ExteriorOfBall | RadialAnnulus


def radial_interval(chart: SymbolicManifold, domain: DomainSpec) -> tuple[sympy.Expr, sympy.Expr]:
    """Return the radial integration interval for the chart's first coordinate."""

    lower, upper = chart.bounds[0]
    chart_lower = sympy.Integer(0) if lower is None else lower
    chart_upper = sympy.oo if upper is None else upper
    match domain:
        case FullManifold():
            return (chart_lower, chart_upper)
        case GeodesicBall(radius=radius):
            return (chart_lower, sympy.sympify(radius))
        case ExteriorOfBall(radius=radius):
            if chart_upper != sympy.oo:
                raise DomainError(f"{chart.name}: exterior domains require an unbounded radial coordinate")
            return (sympy.sympify(radius), sympy.oo)
        case RadialAnnulus(inner=inner, outer=outer):
            return (sympy.sympify(inner), sympy.sympify(outer))
    raise DomainError(f"unsupported domain {domain!r}")
