"""Integration-by-parts and curvature identities with explicit boundary bookkeeping.

The central identity is the divergence form of the deformation energy,

    <L_Def u, u> = 2 |Def u|^2 - div F,      F^i = 2 Def^i_j u^j,

whose flux ``F`` carries every boundary term of the weak formulation.  The
Weitzenboeck comparison ``L_Def = L_Hodge - 2 Ric`` for divergence-free fields
is verified pointwise on a chart for a generic stream function, which makes
the check a chart-level theorem rather than an example.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy

from riemannian_fluids.symbolic import kernel
from riemannian_fluids.symbolic.charts import SymbolicManifold
from riemannian_fluids.symbolic.fields import SolenoidalField, StructuredField
from riemannian_fluids.symbolic.simplify import is_zero, simp


def deformation_flux(manifold: SymbolicManifold, vector: kernel.Components) -> kernel.Components:
    """Return ``F^i = 2 Def^i_j u^j``, the boundary flux of the deformation energy."""

    tensor = kernel.deformation_tensor(manifold, vector)
    inverse = manifold.inverse_metric
    lowered = kernel.lower_index(manifold, vector)
    n = manifold.dimension
    flux = []
    for i in range(n):
        total = sympy.Integer(0)
        for k in range(n):
            for j in range(n):
                for m in range(n):
                    total += 2 * inverse[i, k] * tensor[k, j] * inverse[j, m] * lowered[m]
        flux.append(simp(total))
    return tuple(flux)


@dataclass(frozen=True)
class DeformationEnergyIdentity:
    """``<L_Def u, u> = 2|Def u|^2 - div F`` on a chart, with the flux exposed."""

    manifold: SymbolicManifold
    pairing: sympy.Expr
    energy_density: sympy.Expr
    flux: kernel.Components
    residual: sympy.Expr

    @property
    def holds(self) -> bool | None:
        return is_zero(self.residual)

    def radial_boundary_integrand(self) -> sympy.Expr:
        """Return the flux through a ``{q0 = c}`` level set per unit angular coordinate.

        The outward unit normal of a sublevel set is ``d/dq0 / sqrt(g00)`` and the
        induced measure is ``volume_density / sqrt(g00) dq1``, so the boundary
        integrand is ``<F, nu> dS = (F-flat)_0 * volume_density / g00 dq1``.
        """

        g = self.manifold.metric
        lowered_flux_0 = sum(g[0, j] * self.flux[j] for j in range(self.manifold.dimension))
        return simp(lowered_flux_0 / sympy.sqrt(g[0, 0]) * self.manifold.volume_density / sympy.sqrt(g[0, 0]))


def deformation_energy_identity(field: StructuredField) -> DeformationEnergyIdentity:
    manifold = field.manifold
    components = field.components()
    tensor = kernel.deformation_tensor(manifold, components)
    energy_density = simp(2 * kernel.covariant_tensor_squared_norm(manifold, tensor))
    laplacian = kernel.deformation_laplacian(manifold, components)
    lowered = kernel.lower_index(manifold, components)
    pairing = simp(sum(laplacian[i] * lowered[i] for i in range(manifold.dimension)))
    flux = deformation_flux(manifold, components)
    residual = simp(pairing - energy_density + kernel.divergence(manifold, flux))
    return DeformationEnergyIdentity(manifold, pairing, energy_density, flux, residual)


def weitzenbock_residual(manifold: SymbolicManifold, vector: kernel.Components) -> kernel.Components:
    """Return the components of ``L_Def u - L_Hodge u + 2 Ric u``.

    The result vanishes identically for divergence-free fields.
    """

    deformation = kernel.deformation_laplacian(manifold, vector)
    hodge = kernel.hodge_laplacian(manifold, vector)
    ricci = kernel.ricci_action(manifold, vector)
    return tuple(simp(deformation[i] - hodge[i] + 2 * ricci[i]) for i in range(manifold.dimension))


def verify_divfree_def_hodge(field: SolenoidalField) -> bool:
    """Verify ``L_Def = L_Hodge - 2 Ric`` on the field's chart.

    Applied to a coexact field with a generic stream function this verifies the
    identity for every stream on the chart, not for one example.
    """

    residual = weitzenbock_residual(field.manifold, field.components())
    verdicts = [is_zero(component) for component in residual]
    if all(verdict is True for verdict in verdicts):
        return True
    if any(verdict is False for verdict in verdicts):
        raise AssertionError(f"Weitzenboeck identity refuted on {field.manifold.name}: residual {residual}")
    raise AssertionError(f"Weitzenboeck identity undecided on {field.manifold.name}")
