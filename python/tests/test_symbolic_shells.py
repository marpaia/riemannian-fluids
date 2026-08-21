"""Thin-shell solver tests: series grading, tube geometry, and the wall-selected eigenvalue."""

from __future__ import annotations

import jax.numpy as jnp
import pytest
import sympy

from riemannian_fluids.geometry import space_forms
from riemannian_fluids.geometry.core import metric as numeric_metric
from riemannian_fluids.geometry.core import shape_operator as numeric_shape_operator
from riemannian_fluids.operators import deformation_dissipation_density
from riemannian_fluids.operators.viscosity import interpolating_viscosity
from riemannian_fluids.shells.averaging import tubular_jacobian
from riemannian_fluids.symbolic import crosscheck_components, crosscheck_scalar, kernel, require_agreement, sphere_chart
from riemannian_fluids.symbolic.series import TruncationError, exact_polynomial, series_of
from riemannian_fluids.symbolic.shells import (
    RecoveryConstructionError,
    RecoveryEndpoint,
    canonical_navier_torus_recovery,
    canonical_torus_smooth_recovery,
    canonical_torus_smooth_recovery_rate,
    canonical_torus_smooth_solenoidal_field,
    interpolating_operator,
    pairing_eigenvalue,
    rotational_mode_eigenvalue,
    sphere_shell_chart,
    torus_shell_chart,
    transverse_average,
    two_wall_rotational_field,
)
from riemannian_fluids.tensors import divergence as numeric_divergence

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


class TestTorusShellGeometry:
    def test_shell_metric_matches_ambient_pullback(self):
        chart = torus_shell_chart(2, 1)

        def embedding(q: jnp.ndarray) -> jnp.ndarray:
            theta, phi, sigma = q
            offset = 1 + sigma
            radial = 2 + offset * jnp.cos(theta)
            return jnp.asarray((radial * jnp.cos(phi), radial * jnp.sin(phi), offset * jnp.sin(theta)))

        entries = tuple(chart.shell.metric[i, j] for i in range(3) for j in range(3))
        require_agreement(
            crosscheck_components(chart.shell, entries, lambda q: numeric_metric(embedding, q).reshape(-1), {}, quantity="torus shell metric vs pullback")
        )


class TestCanonicalNavierRecovery:
    def test_exact_admissibility_and_identification(self):
        certificate = canonical_navier_torus_recovery(EPS)
        assert certificate.surface_divergence == 0
        assert certificate.shell_divergence == 0
        assert certificate.wall_normal_traces == (0, 0)
        assert certificate.wall_stress_residuals == ((0, 0), (0, 0))
        assert certificate.identified_components == certificate.surface_components
        assert certificate.weighted_transverse_average == certificate.surface_components

    def test_exact_mass_and_energy_limits(self):
        certificate = canonical_navier_torus_recovery(EPS)
        assert sympy.simplify(certificate.surface_energy - 25 * sympy.pi**2) == 0
        assert sympy.simplify(
            certificate.normalized_shell_energy
            - sympy.pi**2 * (9 * EPS - 8 * sympy.log(1 - EPS) + 8 * sympy.log(1 + EPS)) / EPS
        ) == 0
        assert sympy.simplify(certificate.energy_error_coefficient - sympy.Rational(16, 3) * sympy.pi**2) == 0
        assert sympy.simplify(certificate.surface_l2_norm_squared - 19 * sympy.pi**2) == 0
        assert sympy.simplify(certificate.normalized_shell_l2_norm_squared - sympy.pi**2 * (19 + 3 * EPS**2)) == 0
        assert sympy.simplify(certificate.norm_error_coefficient - 3 * sympy.pi**2) == 0

    def test_invalid_thickness_assumption_is_rejected(self):
        with pytest.raises(RecoveryConstructionError, match="positive SymPy symbol"):
            canonical_navier_torus_recovery(sympy.Symbol("varepsilon", real=True))

    def test_symbolic_certificate_matches_independent_jax_calculus(self):
        certificate = canonical_navier_torus_recovery(EPS)
        shell = certificate.chart.shell

        def embedding(q: jnp.ndarray) -> jnp.ndarray:
            theta, phi, sigma = q
            offset = 1 + sigma
            radial = 2 + offset * jnp.cos(theta)
            return jnp.asarray((radial * jnp.cos(phi), radial * jnp.sin(phi), offset * jnp.sin(theta)))

        def field(q: jnp.ndarray) -> jnp.ndarray:
            return jnp.asarray((0.0, jnp.sin(q[0]), 0.0), dtype=q.dtype)

        require_agreement(
            crosscheck_scalar(
                shell,
                certificate.shell_divergence,
                lambda q: numeric_divergence(embedding, field, q),
                {},
                quantity="recovery shell divergence",
            )
        )
        require_agreement(
            crosscheck_scalar(
                shell,
                certificate.shell_energy_density,
                lambda q: deformation_dissipation_density(embedding, field, q),
                {},
                quantity="recovery deformation-energy density",
            )
        )


class TestCanonicalSmoothRecovery:
    def test_stream_plus_flux_represents_general_solenoidal_data(self):
        field = canonical_torus_smooth_solenoidal_field()
        theta, phi = field.chart.surface.coords
        rho = field.chart.surface.volume_density
        assert field.divergence == 0
        assert sympy.simplify(
            rho * field.components[0]
            - sympy.diff(field.stream_function, phi)
            - field.meridional_flux
        ) == 0
        assert sympy.simplify(
            rho * field.components[1]
            + sympy.diff(field.stream_function, theta)
            - field.azimuthal_flux
        ) == 0

    @pytest.mark.parametrize("endpoint", list(RecoveryEndpoint))
    def test_arbitrary_field_recovery_is_exactly_admissible(self, endpoint):
        certificate = canonical_torus_smooth_recovery(endpoint, EPS)
        assert certificate.surface_divergence == 0
        assert certificate.shell_divergence == 0
        assert certificate.flux_moment_residuals == (0, 0)
        assert certificate.normal_antiderivative_residual == 0
        assert certificate.upper_wall_flux_identity_residual == 0
        assert certificate.wall_normal_traces == (0, 0)
        assert certificate.wall_law_residuals == ((0, 0), (0, 0))
        assert certificate.transverse_flux_average == certificate.surface_field.components

    @pytest.mark.parametrize("endpoint", list(RecoveryEndpoint))
    def test_universal_strong_and_quadratic_energy_rate(self, endpoint):
        certificate = canonical_torus_smooth_recovery_rate(endpoint, EPS)
        assert all(
            residual == 0
            for component in certificate.exact_component_jet_residuals
            for residual in component
        )
        assert certificate.fast_tensor_zeroth_residuals == (0, 0)
        assert certificate.energy_zeroth_residual == 0
        assert certificate.energy_first_average == 0
        assert certificate.strong_difference_zeroth == 0
        assert certificate.strong_difference_first == 0
        assert not certificate.shell_energy_second.has(EPS)
        assert not certificate.strong_difference_second.has(EPS)

    @pytest.mark.parametrize("endpoint", list(RecoveryEndpoint))
    def test_coordinate_wall_relation_matches_native_tensor_trace(self, endpoint):
        prototype = canonical_torus_smooth_solenoidal_field()
        theta, phi = prototype.chart.surface.coords
        field = canonical_torus_smooth_solenoidal_field(
            sympy.sin(theta) * sympy.cos(phi),
            meridional_flux=sympy.Rational(1, 3),
            azimuthal_flux=sympy.Rational(-2, 5),
        )
        certificate = canonical_torus_smooth_recovery(
            endpoint,
            EPS,
            surface_field=field,
        )
        sigma = certificate.chart.sigma
        if endpoint is RecoveryEndpoint.NAVIER:
            tensor = kernel.deformation_tensor(
                certificate.chart.shell,
                certificate.shell_components,
            )
            residuals = (
                tensor[0, 2],
                tensor[1, 2],
            )
        else:
            tensor = kernel.exterior_derivative_one_form(
                certificate.chart.shell,
                certificate.shell_components,
            )
            residuals = (
                tensor[2, 0],
                tensor[2, 1],
            )
        for wall in (-EPS, EPS):
            assert all(sympy.cancel(value.subs(sigma, wall)) == 0 for value in residuals)

    def test_invalid_endpoint_is_rejected(self):
        with pytest.raises(RecoveryConstructionError, match="endpoint must be one of"):
            canonical_torus_smooth_recovery("intermediate", EPS)


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
