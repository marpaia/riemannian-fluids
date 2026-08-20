"""Thin-shell limits: transverse averaging, effective eigenvalues, and the interpolating family.

The effective eigenvalue of a shell field is the ratio of the transverse
averages of ``<L_Def U, U>`` and ``|U|^2``; its ``eps -> 0`` coefficient is the
surface eigenvalue selected by the wall condition.  The two-dimensional
interpolating family ``L(alpha) = L_Def + 2 alpha Ric + 4 alpha (1-alpha) S^2``
is the operator the limit is compared against.
"""

from __future__ import annotations

import sympy

from riemannian_fluids.symbolic import kernel
from riemannian_fluids.symbolic.charts import SymbolicManifold
from riemannian_fluids.symbolic.series import EpsSeries, series_of
from riemannian_fluids.symbolic.shells.ansatz import RotationalShellField
from riemannian_fluids.symbolic.shells.tube import ShellChart


def transverse_average(
    expr: sympy.Expr,
    chart: ShellChart,
    thickness: sympy.Symbol,
    *,
    order: int,
) -> EpsSeries:
    """Return the per-unit-thickness jacobian-weighted normal average as an eps-series.

    The sigma-Taylor truncation is carried two degrees past the requested
    order, so every reported coefficient is exact.
    """

    sigma = chart.sigma
    depth = order + 2
    integrand = sympy.series(sympy.expand(expr * chart.jacobian), sigma, 0, depth + 1).removeO()
    averaged = sympy.integrate(integrand, (sigma, -thickness, thickness)) / (2 * thickness)
    return series_of(sympy.cancel(sympy.expand(averaged)), thickness, order)


def pairing_eigenvalue(field: RotationalShellField, *, order: int = 1) -> EpsSeries:
    """Return the eps-expansion of ``avg<L_Def U, U> / avg|U|^2`` for a shell field."""

    chart = field.chart
    components = field.components()
    shell = chart.shell
    laplacian = kernel.deformation_laplacian(shell, components)
    lowered = kernel.lower_index(shell, components)
    pairing = sympy.expand(sum(laplacian[i] * lowered[i] for i in range(3)))
    squared = sympy.expand(sum(lowered[i] * components[i] for i in range(3)))

    sigma = chart.sigma
    eps = field.thickness
    depth = order + 3
    numerator = sympy.integrate(sympy.series(sympy.expand(pairing * chart.jacobian), sigma, 0, depth).removeO(), (sigma, -eps, eps))
    denominator = sympy.integrate(sympy.series(sympy.expand(squared * chart.jacobian), sigma, 0, depth).removeO(), (sigma, -eps, eps))
    ratio = sympy.cancel(numerator / denominator)
    return series_of(ratio, eps, order)


def interpolating_operator(
    surface: SymbolicManifold,
    vector: kernel.Components,
    alpha: sympy.Expr,
    shape: sympy.ImmutableMatrix,
) -> kernel.Components:
    """Apply ``L(alpha) = L_Def + 2 alpha Ric + 4 alpha (1-alpha) S^2`` on a surface chart."""

    deformation = kernel.deformation_laplacian(surface, vector)
    ricci = kernel.ricci_action(surface, vector)
    squared_shape = shape * shape
    shape_action = tuple(sum(squared_shape[i, j] * vector[j] for j in range(surface.dimension)) for i in range(surface.dimension))
    return tuple(
        sympy.simplify(deformation[i] + 2 * alpha * ricci[i] + 4 * alpha * (1 - alpha) * shape_action[i])
        for i in range(surface.dimension)
    )


def rotational_mode_eigenvalue(surface: SymbolicManifold, alpha: sympy.Expr, shape: sympy.ImmutableMatrix) -> sympy.Expr:
    """Return the ``L(alpha)`` eigenvalue of the rotational Killing mode ``d/dphi``."""

    mode = (sympy.Integer(0), sympy.Integer(1))
    image = interpolating_operator(surface, mode, alpha, shape)
    if sympy.simplify(image[0]) != 0:
        raise ValueError("the rotational mode is not an eigenvector of L(alpha) on this chart")
    return sympy.simplify(image[1])
