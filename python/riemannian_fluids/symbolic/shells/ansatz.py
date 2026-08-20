"""Wall-typed shell ansatz fields.

The two-wall relation ``d_sigma U = 2 alpha S(sigma) U`` is imposed at both
walls when the field is constructed, so an ansatz violating its wall law is
unrepresentable.  The constructor verifies that the imposed profile satisfies
the wall law through the tracked epsilon order and raises otherwise.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy

from riemannian_fluids.symbolic.charts import ChartConstructionError
from riemannian_fluids.symbolic.shells.tube import ShellChart


@dataclass(frozen=True)
class RotationalShellField:
    """The degree-one rotational mode ``U = (0, p(sigma), 0)`` with a two-wall profile."""

    chart: ShellChart
    alpha: sympy.Expr
    thickness: sympy.Symbol
    profile: sympy.Expr
    order: int

    def components(self) -> tuple[sympy.Expr, sympy.Expr, sympy.Expr]:
        return (sympy.Integer(0), self.profile, sympy.Integer(0))

    def construction(self) -> str:
        return f"two-wall rotational profile with d_sigma U = 2*{self.alpha}*S(sigma) U at sigma = +-{self.thickness}"


def two_wall_rotational_field(
    chart: ShellChart,
    alpha: sympy.Expr,
    thickness: sympy.Symbol,
    *,
    order: int = 2,
) -> RotationalShellField:
    """Construct the quadratic two-wall rotational profile on a shell chart."""

    sigma = chart.sigma
    eps = thickness
    a1, a2 = sympy.symbols("_a1 _a2")
    ansatz = 1 + a1 * sigma + a2 * sigma**2
    shear = chart.shape_operator[1, 1]
    wall = sympy.diff(ansatz, sigma) - 2 * alpha * shear * ansatz
    solutions = sympy.solve([wall.subs(sigma, eps), wall.subs(sigma, -eps)], [a1, a2], dict=True)
    if not solutions:
        raise ChartConstructionError("the two-wall conditions have no quadratic solution on this chart")
    coefficients = {symbol: sympy.series(value, eps, 0, order + 1).removeO() for symbol, value in solutions[0].items()}
    profile = ansatz.subs(coefficients)

    residual = (sympy.diff(profile, sigma) - 2 * alpha * shear * profile).subs(sigma, eps)
    residual_order = sympy.series(sympy.expand(residual), eps, 0, order).removeO()
    if sympy.expand(residual_order) != 0:
        raise ChartConstructionError(f"two-wall residual {residual_order} does not vanish through order {order - 1}")
    return RotationalShellField(chart=chart, alpha=sympy.sympify(alpha), thickness=eps, profile=profile, order=order)
