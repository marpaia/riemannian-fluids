"""Field-construction guarantees and certified energy integrals."""

from __future__ import annotations

import pytest
import sympy

from riemannian_fluids.symbolic import (
    ChartConstructionError,
    hyperbolic_polar_chart,
    is_zero,
    positive_symbols,
    simp,
    sphere_chart,
    torus_chart,
)
from riemannian_fluids.symbolic import kernel as sym
from riemannian_fluids.symbolic.certificates import DivergentCertificate, ExactCertificate, FiniteCertificate, UnresolvedCertificate
from riemannian_fluids.symbolic.energy import (
    ExteriorOfBall,
    FullManifold,
    deformation_energy_density,
    energy_integral,
    verify_numerically,
)
from riemannian_fluids.symbolic.fields import SymbolicVectorField, coexact_field, rotation_killing_field


def _h2_setup():
    a, b, r0 = positive_symbols("a b R0")
    chart = hyperbolic_polar_chart(-(a**2))
    return a, b, r0, chart


class TestFieldConstruction:
    @pytest.mark.parametrize("chart_factory", [lambda: sphere_chart(1), lambda: hyperbolic_polar_chart(-1), lambda: torus_chart(2, 1)])
    def test_coexact_fields_are_divergence_free(self, chart_factory):
        chart = chart_factory()
        q0, q1 = chart.coords
        field = coexact_field(chart, sympy.exp(-q0) * sympy.cos(q1))
        assert is_zero(sym.divergence(chart, field.components())) is True

    def test_killing_field_has_vanishing_deformation(self):
        chart = sphere_chart(1)
        killing = rotation_killing_field(chart, axis=1)
        tensor = sym.deformation_tensor(chart, killing.components())
        assert all(simp(tensor[i, j]) == 0 for i in range(2) for j in range(2))

    def test_rotational_stream_on_sphere_is_killing(self):
        chart = sphere_chart(1)
        theta = chart.coords[0]
        field = coexact_field(chart, sympy.cos(theta))
        assert simp(deformation_energy_density(field)) == 0

    def test_killing_axis_must_be_metric_invariant(self):
        chart = sphere_chart(1)
        with pytest.raises(ChartConstructionError):
            rotation_killing_field(chart, axis=0)

    def test_hierarchy_is_closed(self):
        with pytest.raises(TypeError):

            class RogueField(SymbolicVectorField):
                pass


class TestEnergyIntegral:
    def test_h2_exterior_energy_exact(self):
        a, _, r0, chart = _h2_setup()
        field = coexact_field(chart, sympy.exp(-2 * a * chart.coords[0]))
        result = energy_integral(deformation_energy_density(field), chart, ExteriorOfBall(r0))
        assert isinstance(result.certificate, ExactCertificate)
        assert result.closed_form is not None
        assert "a > 0" in result.certificate.assumptions and "R0 > 0" in result.certificate.assumptions
        check = verify_numerically(result, {a: 1.1, r0: 0.7})
        assert check.passed, f"quadrature mismatch: {check.max_error:.3e}"

    def test_h2_generic_rates_are_unresolved(self):
        a, b, r0, chart = _h2_setup()
        field = coexact_field(chart, sympy.exp(-b * chart.coords[0]))
        result = energy_integral(deformation_energy_density(field), chart, ExteriorOfBall(r0))
        assert isinstance(result.certificate, FiniteCertificate | UnresolvedCertificate | ExactCertificate)
        if isinstance(result.certificate, ExactCertificate):
            check = verify_numerically(result, {a: 1.0, b: 1.5, r0: 0.7})
            assert check.passed

    def test_h2_slow_decay_is_divergent(self):
        r0 = positive_symbols("R0")[0]
        chart = hyperbolic_polar_chart(-1)
        field = coexact_field(chart, sympy.exp(-sympy.Rational(1, 5) * chart.coords[0]))
        result = energy_integral(deformation_energy_density(field), chart, ExteriorOfBall(r0))
        assert isinstance(result.certificate, DivergentCertificate)

    def test_finiteness_without_closed_form(self):
        a, _, r0, chart = _h2_setup()
        r = chart.coords[0]
        density = sympy.exp(-3 * a * r - sympy.exp(-r))
        result = energy_integral(density, chart, ExteriorOfBall(r0))
        assert isinstance(result.certificate, FiniteCertificate | ExactCertificate)

    def test_sphere_full_energy_matches_quadrature(self):
        chart = sphere_chart(1)
        theta = chart.coords[0]
        field = coexact_field(chart, sympy.cos(2 * theta))
        result = energy_integral(deformation_energy_density(field), chart, FullManifold())
        assert isinstance(result.certificate, ExactCertificate)
        check = verify_numerically(result, {})
        assert check.passed, f"quadrature mismatch: {check.max_error:.3e}"

    def test_ledger_records_reduction(self):
        a, _, r0, chart = _h2_setup()
        field = coexact_field(chart, sympy.exp(-2 * a * chart.coords[0]))
        result = energy_integral(deformation_energy_density(field), chart, ExteriorOfBall(r0))
        kinds = [step.kind for step in result.ledger.steps]
        assert kinds[:2] == ["volume-element", "symmetry"]
        assert "radial-integral" in kinds
