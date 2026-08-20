"""Structured symbolic fields whose geometric properties hold by construction.

The vector-field hierarchy is closed: every concrete class is registered here,
solvers dispatch on the concrete types, and capability unions express what a
solver accepts, so unsupported usage fails in the type checker and again at
runtime.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar

import sympy

from riemannian_fluids.symbolic.charts import ChartConstructionError, SymbolicManifold
from riemannian_fluids.symbolic.kernel import Components, raise_index


@dataclass(frozen=True)
class SymbolicScalarField:
    manifold: SymbolicManifold
    expr: sympy.Expr

    def __post_init__(self) -> None:
        undeclared = sympy.sympify(self.expr).free_symbols - set(self.manifold.coords) - set(self.manifold.params)
        for symbol in undeclared:
            if not symbol.is_positive:
                raise ChartConstructionError(f"scalar-field symbol {symbol} must be declared positive (use positive_symbols)")


@dataclass(frozen=True)
class SymbolicVectorField:
    """Abstract structured vector field; only registered subclasses may exist."""

    manifold: SymbolicManifold

    _registry: ClassVar[frozenset[str]] = frozenset({"CoexactField", "GradientField", "RotationKillingField"})

    def __init_subclass__(cls) -> None:
        if cls.__name__ not in SymbolicVectorField._registry:
            raise TypeError(f"{cls.__name__} is not a registered structured field; add constructors to fields.py instead of subclassing")

    def components(self) -> Components:
        raise NotImplementedError

    def construction(self) -> str:
        raise NotImplementedError


@dataclass(frozen=True)
class CoexactField(SymbolicVectorField):
    """``u = sharp(*d psi)`` on an oriented two-manifold; divergence-free by construction."""

    stream: SymbolicScalarField

    def __post_init__(self) -> None:
        if self.manifold.dimension != 2:
            raise ChartConstructionError("a scalar stream function represents velocity only in dimension two")

    def components(self) -> Components:
        psi = self.stream.expr
        q0, q1 = self.manifold.coords
        density = self.manifold.volume_density
        return (sympy.diff(psi, q1) / density, -sympy.diff(psi, q0) / density)

    def construction(self) -> str:
        return "u = sharp(*d psi): divergence-free by construction"


@dataclass(frozen=True)
class GradientField(SymbolicVectorField):
    """``u = grad(f)``; curl-free by construction, not divergence-free."""

    potential: SymbolicScalarField

    def components(self) -> Components:
        covector = tuple(sympy.diff(self.potential.expr, coord) for coord in self.manifold.coords)
        return raise_index(self.manifold, covector)

    def construction(self) -> str:
        return "u = grad(f): exact one-form by construction"


@dataclass(frozen=True)
class RotationKillingField(SymbolicVectorField):
    """The coordinate rotation generator of a metric-invariant coordinate."""

    axis: int

    def __post_init__(self) -> None:
        coord = self.manifold.coords[self.axis]
        for i in range(self.manifold.dimension):
            for j in range(self.manifold.dimension):
                if sympy.diff(self.manifold.metric[i, j], coord) != 0:
                    raise ChartConstructionError(f"{self.manifold.name}: metric depends on {coord}; d/d{coord} is not a Killing field")

    def components(self) -> Components:
        return tuple(sympy.Integer(1) if i == self.axis else sympy.Integer(0) for i in range(self.manifold.dimension))

    def construction(self) -> str:
        return f"u = d/d{self.manifold.coords[self.axis]}: Killing by metric invariance, divergence-free by construction"


def coexact_field(manifold: SymbolicManifold, stream: sympy.Expr) -> CoexactField:
    return CoexactField(manifold=manifold, stream=SymbolicScalarField(manifold, sympy.sympify(stream)))


def gradient_field(manifold: SymbolicManifold, potential: sympy.Expr) -> GradientField:
    return GradientField(manifold=manifold, potential=SymbolicScalarField(manifold, sympy.sympify(potential)))


def rotation_killing_field(manifold: SymbolicManifold, axis: int = 1) -> RotationKillingField:
    return RotationKillingField(manifold=manifold, axis=axis)


type SolenoidalField = CoexactField | RotationKillingField
type StructuredField = CoexactField | GradientField | RotationKillingField
