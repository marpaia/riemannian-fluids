"""Cross-backend and golden-identity tests for the symbolic kernel."""

from __future__ import annotations

import jax.numpy as jnp
import pytest
import sympy

from riemannian_fluids.geometry import intrinsic_ricci_tensor, space_forms
from riemannian_fluids.operators import viscosity
from riemannian_fluids.symbolic import (
    ChartConstructionError,
    SymbolicManifold,
    crosscheck_components,
    crosscheck_scalar,
    hyperbolic_polar_chart,
    positive_symbols,
    require_agreement,
    ricci_tensor,
    scalar_curvature,
    simp,
    sphere_chart,
    spheroid_chart,
    torus_chart,
)
from riemannian_fluids.symbolic import kernel as sym
from riemannian_fluids.tensors import calculus


def _chart_cases() -> list[tuple[SymbolicManifold, object, dict]]:
    a = positive_symbols("a")[0]
    return [
        (sphere_chart(1), space_forms.sphere(1.0), {}),
        (hyperbolic_polar_chart(-(a**2)), space_forms.hyperbolic_geodesic_polar(curvature=-1.69), {a: 1.3}),
        (torus_chart(sympy.Rational(9, 5), sympy.Rational(11, 20)), space_forms.torus_of_revolution(1.8, 0.55), {}),
        (spheroid_chart(sympy.Rational(3, 2), 1), space_forms.spheroid(1.5, 1.0), {}),
    ]


def _test_field(chart: SymbolicManifold) -> tuple[tuple[sympy.Expr, ...], object]:
    q0, q1 = chart.coords
    symbolic = (sympy.sin(q0) * sympy.cos(q1), sympy.cos(q0))

    def numeric(q: jnp.ndarray) -> jnp.ndarray:
        return jnp.asarray((jnp.sin(q[0]) * jnp.cos(q[1]), jnp.cos(q[0])))

    return symbolic, numeric


@pytest.mark.parametrize(("chart", "geometry", "params"), _chart_cases(), ids=lambda case: getattr(case, "name", None) or str(case)[:24])
class TestKernelAgainstJax:
    def test_metric(self, chart, geometry, params):
        entries = tuple(chart.metric[i, j] for i in range(2) for j in range(2))
        require_agreement(
            crosscheck_components(chart, entries, lambda q: geometry.metric(q).reshape(-1), params, quantity=f"{chart.name}: metric")
        )

    def test_ricci_tensor(self, chart, geometry, params):
        ricci = ricci_tensor(chart)
        entries = tuple(ricci[i, j] for i in range(2) for j in range(2))
        require_agreement(
            crosscheck_components(
                chart,
                entries,
                lambda q: intrinsic_ricci_tensor(geometry, q).reshape(-1),
                params,
                quantity=f"{chart.name}: Ricci",
                rtol=1e-6,
            )
        )

    def test_divergence(self, chart, geometry, params):
        field, numeric_field = _test_field(chart)
        require_agreement(
            crosscheck_scalar(
                chart,
                sym.divergence(chart, field),
                lambda q: calculus.divergence(geometry, numeric_field, q),
                params,
                quantity=f"{chart.name}: divergence",
            )
        )

    def test_deformation_tensor(self, chart, geometry, params):
        field, numeric_field = _test_field(chart)
        tensor = sym.deformation_tensor(chart, field)
        entries = tuple(tensor[i, j] for i in range(2) for j in range(2))
        require_agreement(
            crosscheck_components(
                chart,
                entries,
                lambda q: calculus.deformation_tensor(geometry, numeric_field, q).reshape(-1),
                params,
                quantity=f"{chart.name}: Def",
            )
        )

    @pytest.mark.parametrize(
        ("symbolic_op", "numeric_op"),
        [
            (sym.rough_laplacian, viscosity.rough_laplacian),
            (sym.deformation_laplacian, viscosity.deformation_laplacian),
            (sym.hodge_laplacian, viscosity.hodge_laplacian),
            (sym.ricci_action, viscosity.ricci_action),
        ],
        ids=["rough", "deformation", "hodge", "ricci-action"],
    )
    def test_viscosity_operators(self, chart, geometry, params, symbolic_op, numeric_op):
        field, numeric_field = _test_field(chart)
        require_agreement(
            crosscheck_components(
                chart,
                symbolic_op(chart, field),
                lambda q: numeric_op(geometry, numeric_field, q),
                params,
                quantity=f"{chart.name}: {symbolic_op.__name__}",
                rtol=1e-6,
                count=4,
            )
        )


class TestGoldenCurvature:
    def test_sphere_scalar_curvature(self):
        radius = positive_symbols("R")[0]
        assert simp(scalar_curvature(sphere_chart(radius)) - 2 / radius**2) == 0

    def test_hyperbolic_scalar_curvature(self):
        a = positive_symbols("a")[0]
        assert simp(scalar_curvature(hyperbolic_polar_chart(-(a**2))) + 2 * a**2) == 0

    def test_torus_gauss_curvature(self):
        major, minor = positive_symbols("Rmaj rmin")
        chart = torus_chart(major, minor)
        theta = chart.coords[0]
        gauss = scalar_curvature(chart) / 2
        expected = sympy.cos(theta) / (minor * (major + minor * sympy.cos(theta)))
        assert simp(gauss - expected) == 0


class TestChartValidation:
    def test_undeclared_symbol_rejected(self):
        stray = sympy.Symbol("b")
        theta, phi = sympy.symbols("theta phi", positive=True)
        with pytest.raises(ChartConstructionError):
            SymbolicManifold(
                name="broken",
                coords=(theta, phi),
                metric=sympy.ImmutableMatrix([[stray, 0], [0, 1]]),
                volume_density=sympy.sqrt(stray),
                bounds=((None, None), (None, None)),
                sample_window=((0.0, 1.0), (0.0, 1.0)),
            )

    def test_wrong_volume_density_rejected(self):
        theta, phi = sympy.symbols("theta phi", positive=True)
        with pytest.raises(ChartConstructionError):
            SymbolicManifold(
                name="broken-density",
                coords=(theta, phi),
                metric=sympy.ImmutableMatrix([[1, 0], [0, 1]]),
                volume_density=sympy.Integer(2),
                bounds=((None, None), (None, None)),
                sample_window=((0.0, 1.0), (0.0, 1.0)),
            )
