"""Graded truncated series in a small parameter with mechanical order tracking.

An ``EpsSeries`` is exact through ``symbol**order``; the tail is unknown, not
zero.  Arithmetic can only lose order, and reading a coefficient beyond the
tracked order raises, so a silently dropped term is unrepresentable.  A series
with ``order=None`` is an exact polynomial with no unknown tail.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy


class TruncationError(RuntimeError):
    """A coefficient beyond the tracked truncation order was requested."""


def _min_order(first: int | None, second: int | None) -> int | None:
    if first is None:
        return second
    if second is None:
        return first
    return min(first, second)


@dataclass(frozen=True)
class EpsSeries:
    symbol: sympy.Symbol
    coeffs: tuple[sympy.Expr, ...]
    order: int | None

    def __post_init__(self) -> None:
        if self.order is not None and len(self.coeffs) != self.order + 1:
            raise ValueError(f"a series exact through order {self.order} needs {self.order + 1} coefficients, got {len(self.coeffs)}")
        for coefficient in self.coeffs:
            if sympy.sympify(coefficient).has(self.symbol):
                raise ValueError(f"coefficient {coefficient} depends on the series symbol {self.symbol}")

    def coeff(self, k: int) -> sympy.Expr:
        if self.order is not None and k > self.order:
            raise TruncationError(f"coefficient of {self.symbol}**{k} is beyond the tracked order {self.order}")
        return self.coeffs[k] if k < len(self.coeffs) else sympy.Integer(0)

    def truncate(self, order: int) -> EpsSeries:
        if self.order is not None and order > self.order:
            raise TruncationError(f"cannot extend a series exact through order {self.order} to order {order}")
        coeffs = tuple(self.coeff(k) for k in range(order + 1))
        return EpsSeries(self.symbol, coeffs, order)

    def _pair(self, other: EpsSeries) -> None:
        if not isinstance(other, EpsSeries) or other.symbol != self.symbol:
            raise ValueError("series arithmetic requires matching symbols")

    def __add__(self, other: EpsSeries) -> EpsSeries:
        self._pair(other)
        order = _min_order(self.order, other.order)
        length = (order + 1) if order is not None else max(len(self.coeffs), len(other.coeffs))
        coeffs = tuple(self.coeff(k) + other.coeff(k) for k in range(length))
        return EpsSeries(self.symbol, coeffs, order)

    def __mul__(self, other: EpsSeries | sympy.Expr) -> EpsSeries:
        if not isinstance(other, EpsSeries):
            factor = sympy.sympify(other)
            if factor.has(self.symbol):
                raise ValueError("scalar factors must not depend on the series symbol; build an EpsSeries instead")
            return EpsSeries(self.symbol, tuple(factor * c for c in self.coeffs), self.order)
        self._pair(other)
        order = _min_order(self.order, other.order)
        length = (order + 1) if order is not None else len(self.coeffs) + len(other.coeffs) - 1
        coeffs = tuple(
            sum((self.coeff(i) * other.coeff(k - i) for i in range(k + 1)), start=sympy.Integer(0))
            for k in range(length)
        )
        return EpsSeries(self.symbol, coeffs, order)

    __rmul__ = __mul__

    def as_expr(self) -> sympy.Expr:
        return sum((c * self.symbol**k for k, c in enumerate(self.coeffs)), start=sympy.Integer(0))


def series_of(expr: sympy.Expr, symbol: sympy.Symbol, order: int) -> EpsSeries:
    """Expand an expression to a tracked series around ``symbol = 0``."""

    expansion = sympy.series(sympy.sympify(expr), symbol, 0, order + 1).removeO()
    polynomial = sympy.Poly(sympy.expand(expansion), symbol)
    coeffs = tuple(polynomial.coeff_monomial(symbol**k) for k in range(order + 1))
    return EpsSeries(symbol, coeffs, order)


def exact_polynomial(expr: sympy.Expr, symbol: sympy.Symbol) -> EpsSeries:
    """Wrap a polynomial in ``symbol`` as an exact (untail-ed) series."""

    polynomial = sympy.Poly(sympy.expand(sympy.sympify(expr)), symbol)
    coeffs = tuple(polynomial.coeff_monomial(symbol**k) for k in range(polynomial.degree() + 1))
    return EpsSeries(symbol, coeffs, None)
