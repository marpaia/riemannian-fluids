"""Thin-shell solver tests: series grading, tube geometry, and the wall-selected eigenvalue."""

from __future__ import annotations

import jax.numpy as jnp
import pytest
import sympy

from riemannian_fluids.geometry import space_forms
from riemannian_fluids.geometry.core import metric as numeric_metric
from riemannian_fluids.geometry.core import shape_operator as numeric_shape_operator
from riemannian_fluids.operators.viscosity import interpolating_viscosity
from riemannian_fluids.shells.averaging import tubular_jacobian
from riemannian_fluids.symbolic import crosscheck_components, require_agreement, sphere_chart
from riemannian_fluids.symbolic.series import TruncationError, exact_polynomial, series_of
from riemannian_fluids.symbolic.shells import (
    interpolating_operator,
    pairing_eigenvalue,
    rotational_mode_eigenvalue,
    sphere_shell_chart,
    transverse_average,
    two_wall_rotational_field,
)

EPS = sympy.Symbol("varepsilon", positive=True)
ALPHA = sympy.Symbol("alpha", nonnegative=True)


class TestEpsSeries:
    def test_multiplication_tracks_order(self):
        x = sympy.Symbol("x", positive=True)
        first = series_of(1 / (1 - EPS * x), EPS, 2)
        second = exact_polynomial(1 + EPS, EPS)
        product = first * second
        assert product.order == 2
        assert sympy.expand(product.coeff(2) - (x**2 + x)) == 0

    def test_coefficient_beyond_order_raises(self):
        truncated = series_of(sympy.exp(EPS), EPS, 1)
        with pytest.raises(TruncationError):
            truncated.coeff(2)

    def test_dropped_term_is_unrepresentable(self):
        """The seeded-mutation gate: truncating then reading deeper must raise, never return 0."""

        quadratic = exact_polynomial(1 + EPS + EPS**2, EPS)
        with pytest.raises(TruncationError):
            quadratic.truncate(1).coeff(2)

    def test_exact_polynomials_multiply_exactly(self):
        cubic = exact_polynomial((1 + EPS) ** 3, EPS)
        assert cubic.order is None
        assert cubic.coeff(3) == 1 and cubic.coeff(7) == 0


class TestSphereShellGeometry:
    def test_shell_metric_matches_ambient_pullback(self):
        chart = sphere_shell_chart(1)

        def embedding(q: jnp.ndarray) -> jnp.ndarray:
            theta, phi, sigma = q
            return (1 + sigma) * jnp.asarray((jnp.sin(theta) * jnp.cos(phi), jnp.sin(theta) * jnp.sin(phi), jnp.cos(theta)))

        entries = tuple(chart.shell.metric[i, j] for i in range(3) for j in range(3))
        require_agreement(
            crosscheck_components(chart.shell, entries, lambda q: numeric_metric(embedding, q).reshape(-1), {}, quantity="shell metric vs pullback")
        )

    def test_jacobian_matches_numeric_convention(self):
        chart = sphere_shell_chart(1)
        sphere = space_forms.sphere(1.0)
        q = jnp.asarray((1.1, 0.7))
        shape = numeric_shape_operator(sphere, q)
        for r in (0.05, -0.08, 0.15):
            expected = float(tubular_jacobian(shape, r))
            actual = float(chart.jacobian.subs(chart.sigma, r))
            assert abs(expected - actual) < 1e-6

    def test_transverse_average_of_jacobian_only(self):
        chart = sphere_shell_chart(1)
        averaged = transverse_average(sympy.Integer(1), chart, EPS, order=2)
        assert averaged.coeff(0) == 1
        assert averaged.coeff(1) == 0
        assert sympy.nsimplify(averaged.coeff(2)) == sympy.Rational(1, 3)


class TestWallSelectedEigenvalue:
    def test_two_wall_profile_construction(self):
        chart = sphere_shell_chart(1)
        field = two_wall_rotational_field(chart, ALPHA, EPS)
        assert field.profile.subs(chart.sigma, 0).subs(EPS, 0) == 1

    def test_rotational_eigenvalue_is_six_alpha_minus_four_alpha_squared(self):
        """The WBS26 gate: the thin-shell pairing selects lambda_alpha = 6 alpha - 4 alpha^2."""

        chart = sphere_shell_chart(1)
        field = two_wall_rotational_field(chart, ALPHA, EPS)
        eigenvalue = pairing_eigenvalue(field, order=1)
        limit = sympy.expand(eigenvalue.coeff(0))
        assert sympy.expand(limit - (6 * ALPHA - 4 * ALPHA**2)) == 0

    def test_endpoint_eigenvalues(self):
        chart = sphere_shell_chart(1)
        field = two_wall_rotational_field(chart, ALPHA, EPS)
        limit = pairing_eigenvalue(field, order=1).coeff(0)
        assert limit.subs(ALPHA, 0) == 0
        assert limit.subs(ALPHA, 1) == 2

    def test_interpolating_family_matches_thin_shell_limit(self):
        surface = sphere_chart(1)
        shape = sympy.ImmutableMatrix([[-1, 0], [0, -1]])
        eigenvalue = rotational_mode_eigenvalue(surface, ALPHA, shape)
        assert sympy.expand(eigenvalue - (6 * ALPHA - 4 * ALPHA**2)) == 0

    @pytest.mark.parametrize("alpha", [sympy.Rational(1, 4), sympy.Rational(1, 2), sympy.Rational(3, 4)])
    def test_interpolating_operator_matches_numeric(self, alpha):
        surface = sphere_chart(1)
        theta, phi = surface.coords
        field = (sympy.sin(theta) * sympy.cos(phi), sympy.cos(theta))
        shape = sympy.ImmutableMatrix([[-1, 0], [0, -1]])
        symbolic = interpolating_operator(surface, field, alpha, shape)

        sphere = space_forms.sphere(1.0)

        def numeric_field(q: jnp.ndarray) -> jnp.ndarray:
            return jnp.asarray((jnp.sin(q[0]) * jnp.cos(q[1]), jnp.cos(q[0])))

        require_agreement(
            crosscheck_components(
                surface,
                symbolic,
                lambda q: interpolating_viscosity(sphere, numeric_field, q, float(alpha)),
                {},
                quantity=f"L({alpha}) vs numeric",
                rtol=1e-6,
                count=4,
            )
        )
