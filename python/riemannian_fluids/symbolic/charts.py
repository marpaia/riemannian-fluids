"""Symbolic coordinate charts mirroring ``geometry/space_forms.py``.

Every chart factory declares its symbolic parameters with positivity
assumptions and supplies the oriented volume density explicitly, so downstream
integrands never contain ``Abs`` or unresolved square-root branches.  The
declared density is validated against ``det g`` at construction.
"""

from __future__ import annotations

from dataclasses import dataclass, field

import sympy

from riemannian_fluids.symbolic.simplify import is_zero

type Bound = sympy.Expr | None
type SampleWindow = tuple[tuple[float, float], ...]


class ChartConstructionError(ValueError):
    """The chart data are inconsistent or under-specified."""


@dataclass(frozen=True)
class SymbolicManifold:
    """A coordinate patch with an explicit positive-definite symbolic metric."""

    name: str
    coords: tuple[sympy.Symbol, ...]
    metric: sympy.ImmutableMatrix
    volume_density: sympy.Expr
    bounds: tuple[tuple[Bound, Bound], ...]
    sample_window: SampleWindow
    params: tuple[sympy.Symbol, ...] = ()
    notes: tuple[str, ...] = field(default=())

    def __post_init__(self) -> None:
        n = len(self.coords)
        if self.metric.shape != (n, n):
            raise ChartConstructionError(f"{self.name}: metric shape {self.metric.shape} does not match {n} coordinates")
        if len(self.bounds) != n or len(self.sample_window) != n:
            raise ChartConstructionError(f"{self.name}: bounds and sample window must cover all {n} coordinates")
        free = self.metric.free_symbols | self.volume_density.free_symbols
        undeclared = free - set(self.coords) - set(self.params)
        if undeclared:
            raise ChartConstructionError(f"{self.name}: undeclared symbols {sorted(undeclared, key=str)}; declare them as chart params")
        for symbol in self.params:
            if not symbol.is_positive:
                raise ChartConstructionError(f"{self.name}: parameter {symbol} must be declared positive for branch-safe simplification")
        if is_zero(self.metric.det() - self.volume_density**2) is False:
            raise ChartConstructionError(f"{self.name}: volume density does not square to det g")

    @property
    def dimension(self) -> int:
        return len(self.coords)

    @property
    def inverse_metric(self) -> sympy.ImmutableMatrix:
        return sympy.ImmutableMatrix(self.metric.inv())


def positive_symbols(names: str) -> tuple[sympy.Symbol, ...]:
    """Declare chart parameters; positivity is required by every chart factory."""

    symbols = sympy.symbols(names, positive=True)
    return symbols if isinstance(symbols, tuple) else (symbols,)


def _as_param(value: sympy.Expr | float) -> tuple[sympy.Expr, tuple[sympy.Symbol, ...]]:
    expr = sympy.sympify(value)
    return expr, tuple(sorted(expr.free_symbols, key=str))


def sphere_chart(radius: sympy.Expr | float = 1) -> SymbolicManifold:
    """Return ``S^2(radius)`` in colatitude/longitude coordinates ``(theta, phi)``."""

    r_expr, params = _as_param(radius)
    theta, phi = sympy.symbols("theta phi", positive=True)
    metric = sympy.ImmutableMatrix([[r_expr**2, 0], [0, r_expr**2 * sympy.sin(theta) ** 2]])
    return SymbolicManifold(
        name=f"S^2({radius})",
        coords=(theta, phi),
        metric=metric,
        volume_density=r_expr**2 * sympy.sin(theta),
        bounds=((sympy.Integer(0), sympy.pi), (sympy.Integer(0), 2 * sympy.pi)),
        sample_window=((0.4, 2.7), (0.1, 6.1)),
        params=params,
        notes=("theta in (0, pi) keeps sin(theta) positive",),
    )


def hyperbolic_polar_chart(curvature: sympy.Expr | float = -1) -> SymbolicManifold:
    """Return ``H^2(curvature)`` in geodesic-polar coordinates ``(r, theta)``."""

    curvature_expr, params = _as_param(curvature)
    if curvature_expr.is_nonnegative:
        raise ChartConstructionError("hyperbolic curvature must be negative")
    scale = sympy.sqrt(-curvature_expr)
    r, theta = sympy.symbols("r theta", positive=True)
    radial = sympy.sinh(scale * r) / scale
    metric = sympy.ImmutableMatrix([[1, 0], [0, radial**2]])
    return SymbolicManifold(
        name=f"H^2_polar({curvature})",
        coords=(r, theta),
        metric=metric,
        volume_density=radial,
        bounds=((sympy.Integer(0), None), (sympy.Integer(0), 2 * sympy.pi)),
        sample_window=((0.3, 2.4), (0.1, 6.1)),
        params=params,
    )


def torus_chart(major_radius: sympy.Expr | float, minor_radius: sympy.Expr | float) -> SymbolicManifold:
    """Return the torus of revolution in poloidal/toroidal coordinates ``(theta, phi)``."""

    major, major_params = _as_param(major_radius)
    minor, minor_params = _as_param(minor_radius)
    theta, phi = sympy.symbols("theta phi", positive=True)
    radial = major + minor * sympy.cos(theta)
    metric = sympy.ImmutableMatrix([[minor**2, 0], [0, radial**2]])
    return SymbolicManifold(
        name=f"T^2({major_radius},{minor_radius})",
        coords=(theta, phi),
        metric=metric,
        volume_density=minor * radial,
        bounds=((sympy.Integer(0), 2 * sympy.pi), (sympy.Integer(0), 2 * sympy.pi)),
        sample_window=((0.1, 6.1), (0.1, 6.1)),
        params=tuple(dict.fromkeys(major_params + minor_params)),
        notes=("positivity of the density requires major_radius > minor_radius",),
    )


def spheroid_chart(equatorial_radius: sympy.Expr | float, polar_radius: sympy.Expr | float) -> SymbolicManifold:
    """Return the spheroid ``(a sin(theta)cos(phi), a sin(theta)sin(phi), c cos(theta))``."""

    a, a_params = _as_param(equatorial_radius)
    c, c_params = _as_param(polar_radius)
    theta, phi = sympy.symbols("theta phi", positive=True)
    meridian = a**2 * sympy.cos(theta) ** 2 + c**2 * sympy.sin(theta) ** 2
    metric = sympy.ImmutableMatrix([[meridian, 0], [0, a**2 * sympy.sin(theta) ** 2]])
    return SymbolicManifold(
        name=f"spheroid({equatorial_radius},{polar_radius})",
        coords=(theta, phi),
        metric=metric,
        volume_density=a * sympy.sin(theta) * sympy.sqrt(meridian),
        bounds=((sympy.Integer(0), sympy.pi), (sympy.Integer(0), 2 * sympy.pi)),
        sample_window=((0.4, 2.7), (0.1, 6.1)),
        params=tuple(dict.fromkeys(a_params + c_params)),
    )
