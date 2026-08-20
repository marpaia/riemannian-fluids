"""Chart-level identity verification: Weitzenboeck comparison and energy integration by parts."""

from __future__ import annotations

import mpmath
import pytest
import sympy

from riemannian_fluids.symbolic import hyperbolic_polar_chart, is_zero, positive_symbols, sphere_chart, spheroid_chart, torus_chart
from riemannian_fluids.symbolic.energy import ExteriorOfBall, deformation_energy_density, energy_integral, verify_numerically
from riemannian_fluids.symbolic.energy.identities import deformation_energy_identity, verify_divfree_def_hodge, weitzenbock_residual
from riemannian_fluids.symbolic.fields import coexact_field


class TestWeitzenbock:
    @pytest.mark.parametrize(
        "chart_factory",
        [
            lambda: sphere_chart(1),
            lambda: hyperbolic_polar_chart(-(positive_symbols("a")[0] ** 2)),
            lambda: torus_chart(*positive_symbols("Rmaj rmin")),
        ],
        ids=["sphere", "hyperbolic-symbolic-curvature", "torus-symbolic-radii"],
    )
    def test_generic_stream_function(self, chart_factory):
        """L_Def = L_Hodge - 2 Ric for every stream function on the chart."""

        chart = chart_factory()
        q0, q1 = chart.coords
        field = coexact_field(chart, sympy.Function("psi", real=True)(q0, q1))
        assert verify_divfree_def_hodge(field) is True

    def test_spheroid_concrete_stream(self):
        chart = spheroid_chart(sympy.Rational(3, 2), 1)
        field = coexact_field(chart, sympy.cos(chart.coords[0]))
        assert verify_divfree_def_hodge(field) is True

    def test_wrong_sign_is_refuted(self):
        """Flipping the Ricci sign must break the identity: the convention mutation guard."""

        chart = sphere_chart(1)
        field = coexact_field(chart, sympy.cos(2 * chart.coords[0]))
        residual = weitzenbock_residual(chart, field.components())
        mutated = tuple(component + 4 * ricci for component, ricci in zip(residual, _ricci_action(chart, field), strict=True))
        assert any(is_zero(component) is False for component in mutated)


def _ricci_action(chart, field):
    from riemannian_fluids.symbolic import kernel

    return kernel.ricci_action(chart, field.components())


class TestDeformationEnergyIdentity:
    def test_sphere_divergence_form(self):
        chart = sphere_chart(1)
        identity = deformation_energy_identity(coexact_field(chart, sympy.cos(2 * chart.coords[0])))
        assert identity.holds is True

    def test_h2_divergence_form(self):
        a, b = positive_symbols("a b")
        chart = hyperbolic_polar_chart(-(a**2))
        identity = deformation_energy_identity(coexact_field(chart, sympy.exp(-b * chart.coords[0])))
        assert identity.holds is True

    def test_h2_boundary_term_closes_the_budget(self):
        """Numerically: integral of <L_Def u, u> over the exterior equals the energy plus the wall flux."""

        a, b, r0 = positive_symbols("a b R0")
        chart = hyperbolic_polar_chart(-(a**2))
        r = chart.coords[0]
        field = coexact_field(chart, sympy.exp(-2 * a * r))
        identity = deformation_energy_identity(field)

        energy = energy_integral(deformation_energy_density(field), chart, ExteriorOfBall(r0))
        params = {a: sympy.Float(1.1), r0: sympy.Float(0.7)}
        assert verify_numerically(energy, params).passed

        pairing_integrand = (identity.pairing * chart.volume_density).subs(params)
        quadrature = mpmath.quad(sympy.lambdify(r, pairing_integrand, modules="mpmath"), [float(params[r0]), mpmath.inf])
        boundary = identity.radial_boundary_integrand().subs(params).subs(r, params[r0])
        expected = float(energy.closed_form.subs(params)) + 2 * mpmath.pi * float(boundary)
        assert abs(2 * mpmath.pi * quadrature - expected) < 1e-8 * (1 + abs(expected))
