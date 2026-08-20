"""Staged, size-guarded simplification for chart-level tensor expressions."""

from __future__ import annotations

import sympy

DEFAULT_OPS_BUDGET = 40_000


class ExpressionSizeError(RuntimeError):
    """The expression exceeded the simplification size budget."""


def expression_size(expr: sympy.Expr) -> int:
    return int(sympy.count_ops(expr))


def simp(expr: sympy.Expr, *, ops_budget: int = DEFAULT_OPS_BUDGET) -> sympy.Expr:
    """Simplify through staged targeted rewrites before any general fallback.

    The stages are ordered from cheap and predictable to expensive: rational
    normalization, trigonometric/hyperbolic contraction, power collection, and
    a bounded general ``simplify`` only when the expression is still small.
    """

    expr = sympy.sympify(expr)
    if expression_size(expr) > ops_budget:
        raise ExpressionSizeError(f"expression has {expression_size(expr)} ops; budget is {ops_budget}")
    expr = sympy.cancel(sympy.expand(expr))
    generic_functions = bool(expr.atoms(sympy.core.function.AppliedUndef))
    if not generic_functions and expr.has(sympy.sin, sympy.cos, sympy.tan, sympy.sinh, sympy.cosh, sympy.tanh, sympy.coth):
        expr = _attempt(sympy.trigsimp, expr)
    expr = _attempt(lambda e: sympy.powsimp(e, force=False), expr)
    if expression_size(expr) <= 400 and not generic_functions:
        expr = _attempt(sympy.simplify, expr)
    return expr


def _attempt(stage, expr: sympy.Expr) -> sympy.Expr:
    """Apply a simplification stage, keeping the input when SymPy cannot handle it."""

    try:
        return stage(expr)
    except (NotImplementedError, RecursionError, ValueError):
        return expr


def exp_normal_zero(expr: sympy.Expr) -> bool:
    """Decide zero by exponential normal form.

    Rewriting trigonometric and hyperbolic factors as exponentials turns the
    expression into a rational function of exponentials (and any derivative
    atoms), where cancellation is exact polynomial arithmetic.  ``True`` is a
    proof; ``False`` only means this normal form did not close.
    """

    try:
        rewritten = sympy.expand(sympy.sympify(expr).rewrite(sympy.exp))
        numerator, _ = sympy.fraction(sympy.together(rewritten))
        return sympy.expand(numerator) == 0
    except (NotImplementedError, RecursionError, ValueError):
        return False


def is_zero(expr: sympy.Expr) -> bool | None:
    """Three-valued zero test: True, False, or None when undecided.

    The exponential normal form and ``simplify`` prove zeros; ``Expr.equals``
    refutes them by exact evaluation at random points, so a ``False`` here is a
    witness-backed refutation.  Refutation by evaluation is skipped when the
    expression contains undefined functions, whose values are not samplable.
    """

    expr = sympy.sympify(expr)
    if exp_normal_zero(expr):
        return True
    candidate = simp(expr)
    if candidate == 0:
        return True
    if candidate.atoms(sympy.core.function.AppliedUndef):
        return None
    verdict = candidate.equals(0)
    if verdict is True:
        return True
    if verdict is False:
        return False
    return None


def simp_matrix(matrix: sympy.Matrix, *, ops_budget: int = DEFAULT_OPS_BUDGET) -> sympy.Matrix:
    return matrix.applyfunc(lambda entry: simp(entry, ops_budget=ops_budget))
