"""Tube (Fermi) charts around embedded surfaces.

A ``ShellChart`` couples a two-dimensional surface chart with its
three-dimensional normal shell: the shell metric, the sigma-dependent shape
operator of the level surfaces, and the exact tube Jacobian relative to the
surface measure.  In codimension one the Jacobian is the terminating
polynomial ``det(I - sigma S)``; nothing here is truncated.

Sign convention: the shape operator matches the numeric backend
(``geometry.shape_operator``), for which the unit sphere with outward normal
has ``S = -I`` and ``det(I - sigma S) = (1 + sigma)**2``.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy

from riemannian_fluids.symbolic.charts import ChartConstructionError, SymbolicManifold, sphere_chart
from riemannian_fluids.symbolic.simplify import is_zero


@dataclass(frozen=True)
class ShellChart:
    surface: SymbolicManifold
    shell: SymbolicManifold
    sigma: sympy.Symbol
    shape_operator: sympy.ImmutableMatrix
    jacobian: sympy.Expr

    def __post_init__(self) -> None:
        if self.shell.dimension != 3 or self.surface.dimension != 2:
            raise ChartConstructionError("shell charts pair a 2D surface with a 3D tube")
        if self.shell.coords[2] != self.sigma:
            raise ChartConstructionError("the third shell coordinate must be the normal coordinate sigma")
        if is_zero(self.jacobian * self.surface.volume_density - self.shell.volume_density) is False:
            raise ChartConstructionError(f"{self.shell.name}: tube jacobian is inconsistent with the shell volume density")


def sphere_shell_chart(radius: sympy.Expr | float = 1) -> ShellChart:
    """Return the normal shell of ``S^2(radius)`` with outward normal coordinate sigma."""

    surface = sphere_chart(radius)
    r_expr = sympy.sympify(radius)
    theta, phi = surface.coords
    sigma = sympy.Symbol("sigma", real=True)
    scale = r_expr + sigma
    shell = SymbolicManifold(
        name=f"shell(S^2({radius}))",
        coords=(theta, phi, sigma),
        metric=sympy.ImmutableMatrix(
            [
                [scale**2, 0, 0],
                [0, scale**2 * sympy.sin(theta) ** 2, 0],
                [0, 0, 1],
            ]
        ),
        volume_density=scale**2 * sympy.sin(theta),
        bounds=(surface.bounds[0], surface.bounds[1], (None, None)),
        sample_window=(*surface.sample_window, (-0.2, 0.2)),
        params=surface.params,
        notes=("sigma is the signed distance along the outward normal",),
    )
    shape = sympy.ImmutableMatrix([[-1 / scale, 0], [0, -1 / scale]])
    jacobian = (scale / r_expr) ** 2
    return ShellChart(surface=surface, shell=shell, sigma=sigma, shape_operator=shape, jacobian=jacobian)
