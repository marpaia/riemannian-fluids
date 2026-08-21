"""Exact thin-shell recovery certificates on the canonical torus.

The arbitrary-field construction uses the global stream-plus-flux
representation of smooth solenoidal fields on a coordinate torus.  At either
WBS26 endpoint it builds a tangential two-wall profile whose transverse flux
is normalized exactly, then obtains the normal component from one weighted
antiderivative.  The result is exactly solenoidal, has zero normal trace at
both walls, and satisfies the endpoint wall relation.  A universal symbolic
Taylor certificate proves strong recovery and the absence of constant or
linear energy defects, hence the smooth-core ``O(varepsilon**2)`` rate.

The original closed-form Navier mode remains below as a compact regression
fixture with fully integrated mass and energy.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

import sympy

from riemannian_fluids.symbolic import kernel
from riemannian_fluids.symbolic.shells.tube import ShellChart, torus_shell_chart
from riemannian_fluids.symbolic.simplify import is_zero, simp

type SurfaceComponents = tuple[sympy.Expr, sympy.Expr]
type ShellComponents = tuple[sympy.Expr, sympy.Expr, sympy.Expr]
type WallResiduals = tuple[SurfaceComponents, SurfaceComponents]


class RecoveryConstructionError(ValueError):
    """A proposed recovery family failed an exact admissibility or limit gate."""


def _require_zero(expr: sympy.Expr, label: str) -> None:
    if is_zero(expr) is not True:
        raise RecoveryConstructionError(f"{label} was not proved zero: {expr}")


def _require_equal(actual: sympy.Expr, expected: sympy.Expr, label: str) -> None:
    _require_zero(actual - expected, label)


class RecoveryEndpoint(StrEnum):
    """The two rigorous WBS26 endpoint wall laws."""

    NAVIER = "navier"
    HODGE = "hodge"

    @property
    def alpha(self) -> int:
        return 0 if self is RecoveryEndpoint.NAVIER else 1


def _coerce_endpoint(endpoint: RecoveryEndpoint | str) -> RecoveryEndpoint:
    try:
        return endpoint if isinstance(endpoint, RecoveryEndpoint) else RecoveryEndpoint(endpoint)
    except ValueError as error:
        choices = ", ".join(value.value for value in RecoveryEndpoint)
        raise RecoveryConstructionError(f"endpoint must be one of: {choices}") from error


@dataclass(frozen=True)
class CanonicalTorusSolenoidalField:
    """A global smooth solenoidal field in stream-plus-flux coordinates.

    For the canonical metric ``dtheta**2 + (2 + cos(theta))**2 dphi**2``, every
    smooth periodic solenoidal field has

    ``rho v^theta = d_phi psi + a`` and
    ``rho v^phi = -d_theta psi + b``

    for a smooth periodic stream function and two constant fluxes.  The two
    constants retain the harmonic/cohomological modes, so this is not merely
    the coexact subfamily.
    """

    chart: ShellChart
    stream_function: sympy.Expr
    meridional_flux: sympy.Expr
    azimuthal_flux: sympy.Expr
    components: SurfaceComponents
    density_fluxes: SurfaceComponents
    divergence: sympy.Expr
    assumptions: tuple[str, ...]

    def __post_init__(self) -> None:
        _require_zero(self.divergence, "surface divergence")


def canonical_torus_smooth_solenoidal_field(
    stream_function: sympy.Expr | None = None,
    *,
    meridional_flux: sympy.Expr | None = None,
    azimuthal_flux: sympy.Expr | None = None,
) -> CanonicalTorusSolenoidalField:
    """Construct the general smooth solenoidal field on the canonical torus.

    ``stream_function`` is understood to be smooth and ``2*pi``-periodic in
    both chart variables.  The two flux arguments must be coordinate
    constants; when omitted, symbolic real constants are created.
    """

    chart = torus_shell_chart(2, 1)
    theta, phi = chart.surface.coords
    psi = stream_function
    if psi is None:
        psi = sympy.Function("psi")(theta, phi)
    psi = sympy.sympify(psi)
    flux_theta = sympy.sympify(
        meridional_flux
        if meridional_flux is not None
        else sympy.Symbol("meridional_flux", real=True)
    )
    flux_phi = sympy.sympify(
        azimuthal_flux
        if azimuthal_flux is not None
        else sympy.Symbol("azimuthal_flux", real=True)
    )
    for coordinate in (theta, phi):
        _require_zero(sympy.diff(flux_theta, coordinate), "meridional flux derivative")
        _require_zero(sympy.diff(flux_phi, coordinate), "azimuthal flux derivative")

    rho = chart.surface.volume_density
    density_fluxes: SurfaceComponents = (
        sympy.diff(psi, phi) + flux_theta,
        -sympy.diff(psi, theta) + flux_phi,
    )
    components: SurfaceComponents = tuple(simp(value / rho) for value in density_fluxes)  # type: ignore[assignment]
    divergence = kernel.divergence(chart.surface, components)
    return CanonicalTorusSolenoidalField(
        chart=chart,
        stream_function=psi,
        meridional_flux=flux_theta,
        azimuthal_flux=flux_phi,
        components=components,
        density_fluxes=density_fluxes,
        divergence=divergence,
        assumptions=(
            "the stream function is smooth and 2 pi-periodic in theta and phi",
            "the meridional and azimuthal fluxes are real constants",
        ),
    )


def _polynomial_antiderivative_from_lower(
    expression: sympy.Expr,
    variable: sympy.Symbol,
    lower: sympy.Expr,
) -> sympy.Expr:
    """Integrate a polynomial without invoking SymPy's general Risch path."""

    polynomial = sympy.Poly(sympy.cancel(expression), variable)
    return sum(
        (
            coefficient
            * (variable ** (degree[0] + 1) - lower ** (degree[0] + 1))
            / (degree[0] + 1)
        )
        for degree, coefficient in polynomial.terms()
    )


@dataclass(frozen=True)
class TorusEndpointRecoveryCertificate:
    """Exact arbitrary-smooth-field recovery at one wall-law endpoint."""

    endpoint: RecoveryEndpoint
    alpha: int
    chart: ShellChart
    thickness: sympy.Symbol
    surface_field: CanonicalTorusSolenoidalField
    principal_curvatures: SurfaceComponents
    tangential_profiles: SurfaceComponents
    transverse_moments: SurfaceComponents
    transverse_amplitudes: SurfaceComponents
    shell_components: ShellComponents
    surface_divergence: sympy.Expr
    flux_moment_residuals: SurfaceComponents
    normal_antiderivative_residual: sympy.Expr
    upper_wall_flux_identity_residual: sympy.Expr
    shell_divergence: sympy.Expr
    wall_normal_traces: tuple[sympy.Expr, sympy.Expr]
    wall_law_residuals: WallResiduals
    transverse_flux_average: SurfaceComponents
    assumptions: tuple[str, ...]
    source_locator: str
    scope: str

    def __post_init__(self) -> None:
        if self.alpha != self.endpoint.alpha:
            raise RecoveryConstructionError("endpoint and alpha disagree")
        _require_zero(self.surface_divergence, "surface divergence")
        for component, residual in enumerate(self.flux_moment_residuals):
            _require_zero(residual, f"transverse flux moment {component}")
        _require_zero(self.normal_antiderivative_residual, "normal antiderivative identity")
        _require_zero(self.upper_wall_flux_identity_residual, "upper-wall flux identity")
        _require_zero(self.shell_divergence, "shell divergence")
        for wall, trace in zip(("inner", "outer"), self.wall_normal_traces, strict=True):
            _require_zero(trace, f"{wall} normal trace")
        for wall, residual in zip(("inner", "outer"), self.wall_law_residuals, strict=True):
            for component, value in enumerate(residual):
                _require_zero(value, f"{wall} endpoint wall residual component {component}")
        for component, (actual, expected) in enumerate(
            zip(self.transverse_flux_average, self.surface_field.components, strict=True)
        ):
            _require_equal(actual, expected, f"transverse flux average component {component}")


def canonical_torus_smooth_recovery(
    endpoint: RecoveryEndpoint | str,
    thickness: sympy.Symbol | None = None,
    *,
    surface_field: CanonicalTorusSolenoidalField | None = None,
) -> TorusEndpointRecoveryCertificate:
    """Construct an exact shell recovery for every smooth solenoidal torus field.

    The shell occupies ``-varepsilon < sigma < varepsilon``.  The tangential
    profile is the unique epsilon-dependent quadratic profile that satisfies
    ``partial_sigma U^i = 2 alpha S^i_i(sigma) U^i`` at both walls and has the
    WBS26 Taylor coefficients.  Its amplitude is normalized so that

    ``(2 varepsilon)^-1 integral J U^i dsigma = v^i``.

    The weighted antiderivative defining the normal component then has zero
    value at both walls and cancels the shell divergence exactly.  For Navier
    and Hodge this coordinate wall relation is respectively the stress-free
    and vorticity-free relation once the zero normal trace is used.
    """

    selected = _coerce_endpoint(endpoint)
    epsilon = thickness or sympy.Symbol("varepsilon", positive=True)
    if not isinstance(epsilon, sympy.Symbol) or epsilon.is_positive is not True:
        raise RecoveryConstructionError("thickness must be a positive SymPy symbol")
    field = surface_field or canonical_torus_smooth_solenoidal_field()
    chart = field.chart
    if chart != torus_shell_chart(2, 1):
        raise RecoveryConstructionError("the first arbitrary recovery theorem is scoped to the canonical torus")
    if any(component.has(epsilon, chart.sigma) for component in field.components):
        raise RecoveryConstructionError("the surface field must be independent of shell thickness and normal position")

    alpha = selected.alpha
    theta, phi = chart.surface.coords
    sigma = chart.sigma
    rho = chart.surface.volume_density
    principal_curvatures: SurfaceComponents = tuple(
        simp(chart.shape_operator[index, index].subs(sigma, 0)) for index in range(2)
    )  # type: ignore[assignment]
    denominators = tuple(
        1 - (1 + alpha) * (1 + 2 * alpha) * curvature**2 * epsilon**2
        for curvature in principal_curvatures
    )
    linear_coefficients = tuple(
        simp(2 * alpha * curvature / denominators[index])
        for index, curvature in enumerate(principal_curvatures)
    )
    quadratic_coefficients = tuple(
        simp(alpha * (1 + 2 * alpha) * curvature**2 / denominators[index])
        for index, curvature in enumerate(principal_curvatures)
    )
    profiles: SurfaceComponents = tuple(
        1 + linear_coefficients[index] * sigma + quadratic_coefficients[index] * sigma**2
        for index in range(2)
    )  # type: ignore[assignment]
    moments: SurfaceComponents = tuple(
        simp(sympy.integrate(chart.jacobian * profile, (sigma, -epsilon, epsilon)))
        for profile in profiles
    )  # type: ignore[assignment]
    amplitudes: SurfaceComponents = tuple(simp(2 * epsilon / moment) for moment in moments)  # type: ignore[assignment]
    tangential: SurfaceComponents = tuple(
        simp(profiles[index] * amplitudes[index] * field.components[index])
        for index in range(2)
    )  # type: ignore[assignment]

    flux_factors = tuple(
        simp(chart.shell.volume_density * profiles[index] * amplitudes[index] / rho)
        for index in range(2)
    )
    flux_divergence = (
        sympy.diff(flux_factors[0] * field.density_fluxes[0], theta)
        + sympy.diff(flux_factors[1] * field.density_fluxes[1], phi)
    )
    normal_numerator = _polynomial_antiderivative_from_lower(
        flux_divergence,
        sigma,
        -epsilon,
    )
    normal_component = -normal_numerator / chart.shell.volume_density
    shell_components: ShellComponents = (*tangential, normal_component)

    surface_divergence = field.divergence
    flux_moment_residuals: SurfaceComponents = tuple(
        simp(moment * amplitudes[index] - 2 * epsilon)
        for index, moment in enumerate(moments)
    )  # type: ignore[assignment]
    antiderivative_residual = sympy.cancel(
        sympy.diff(normal_numerator, sigma) - flux_divergence
    )
    upper_identity_residual = sympy.cancel(
        normal_numerator.subs(sigma, epsilon)
        - 2 * epsilon * rho * surface_divergence
    )
    shell_divergence = sympy.cancel(
        (flux_divergence - sympy.diff(normal_numerator, sigma))
        / chart.shell.volume_density
    )
    lower_numerator = sympy.cancel(normal_numerator.subs(sigma, -epsilon))
    upper_numerator = sympy.cancel(normal_numerator.subs(sigma, epsilon))
    wall_normal_traces = (
        sympy.cancel(-lower_numerator / chart.shell.volume_density.subs(sigma, -epsilon)),
        sympy.cancel(-upper_numerator / chart.shell.volume_density.subs(sigma, epsilon)),
    )
    wall_law_residuals: WallResiduals = tuple(
        tuple(
            simp(
                (
                    sympy.diff(tangential[index], sigma)
                    - 2 * alpha * chart.shape_operator[index, index] * tangential[index]
                ).subs(sigma, wall)
            )
            for index in range(2)
        )
        for wall in (-epsilon, epsilon)
    )  # type: ignore[assignment]
    transverse_flux_average: SurfaceComponents = tuple(
        simp(moment * amplitudes[index] * field.components[index] / (2 * epsilon))
        for index, moment in enumerate(moments)
    )  # type: ignore[assignment]

    return TorusEndpointRecoveryCertificate(
        endpoint=selected,
        alpha=alpha,
        chart=chart,
        thickness=epsilon,
        surface_field=field,
        principal_curvatures=principal_curvatures,
        tangential_profiles=profiles,
        transverse_moments=moments,
        transverse_amplitudes=amplitudes,
        shell_components=shell_components,
        surface_divergence=surface_divergence,
        flux_moment_residuals=flux_moment_residuals,
        normal_antiderivative_residual=antiderivative_residual,
        upper_wall_flux_identity_residual=upper_identity_residual,
        shell_divergence=shell_divergence,
        wall_normal_traces=wall_normal_traces,
        wall_law_residuals=wall_law_residuals,
        transverse_flux_average=transverse_flux_average,
        assumptions=(
            *field.assumptions,
            "the shell half-thickness satisfies 0 < varepsilon < 1/4",
            "bulk mass and energy use the normalization 1/(2 varepsilon)",
        ),
        source_locator=(
            "arXiv:2605.20589v3, Theorem 4.5 (M2), Proposition 3.2, "
            "Section 3.4, and Appendix A.4"
        ),
        scope=(
            "every smooth solenoidal field on the canonical torus at the Navier or Hodge "
            "endpoint; smooth-core M2 recovery, not M1 or form-domain density"
        ),
    )


@dataclass(frozen=True)
class TorusRecoveryRateCertificate:
    """Universal second-order Taylor certificate for smooth recovery."""

    endpoint: RecoveryEndpoint
    alpha: int
    chart: ShellChart
    thickness: sympy.Symbol
    rescaled_normal_coordinate: sympy.Symbol
    surface_field: CanonicalTorusSolenoidalField
    exact_recovery: TorusEndpointRecoveryCertificate
    second_order_shell_components: ShellComponents
    exact_component_jet_residuals: tuple[
        tuple[sympy.Expr, sympy.Expr, sympy.Expr],
        tuple[sympy.Expr, sympy.Expr, sympy.Expr],
        tuple[sympy.Expr, sympy.Expr, sympy.Expr],
    ]
    fast_tensor_zeroth_residuals: SurfaceComponents
    surface_energy_integrand: sympy.Expr
    shell_energy_zeroth: sympy.Expr
    shell_energy_first: sympy.Expr
    shell_energy_second: sympy.Expr
    energy_zeroth_residual: sympy.Expr
    energy_first_average: sympy.Expr
    strong_difference_zeroth: sympy.Expr
    strong_difference_first: sympy.Expr
    strong_difference_second: sympy.Expr
    jet_atoms: tuple[sympy.Expr, ...]
    jet_symbols: tuple[sympy.Symbol, ...]
    assumptions: tuple[str, ...]
    source_locator: str
    scope: str

    def __post_init__(self) -> None:
        if self.alpha != self.endpoint.alpha:
            raise RecoveryConstructionError("endpoint and alpha disagree")
        _require_zero(self.energy_zeroth_residual, "zeroth-order energy residual")
        _require_zero(self.energy_first_average, "averaged first-order energy residual")
        _require_zero(self.strong_difference_zeroth, "zeroth-order strong-recovery residual")
        _require_zero(self.strong_difference_first, "first-order strong-recovery residual")
        for component, residuals in enumerate(self.exact_component_jet_residuals):
            for order, residual in enumerate(residuals):
                _require_zero(
                    residual,
                    f"exact recovery component {component} Taylor residual at order {order}",
                )
        for component, residual in enumerate(self.fast_tensor_zeroth_residuals):
            _require_zero(residual, f"leading fast-tensor residual component {component}")
        for label, expression in (
            ("quadratic energy coefficient", self.shell_energy_second),
            ("quadratic strong-recovery coefficient", self.strong_difference_second),
        ):
            if expression.has(self.thickness, sympy.oo, -sympy.oo, sympy.zoo, sympy.nan):
                raise RecoveryConstructionError(f"{label} is not a finite thickness-independent jet")


def _jet_substitution(expressions: tuple[sympy.Expr, ...]) -> tuple[
    tuple[sympy.Expr, ...],
    tuple[sympy.Symbol, ...],
    tuple[sympy.Expr, ...],
]:
    atoms = tuple(
        sorted(
            set().union(
                *(expression.atoms(sympy.Derivative) for expression in expressions),
                *(expression.atoms(sympy.core.function.AppliedUndef) for expression in expressions),
            ),
            key=str,
        )
    )
    symbols = sympy.symbols(f"recovery_jet0:{len(atoms)}", real=True)
    mapping = dict(zip(atoms, symbols, strict=True))
    return tuple(expression.xreplace(mapping) for expression in expressions), symbols, atoms


def _coefficient_at_zero(expression: sympy.Expr, symbol: sympy.Symbol, order: int) -> sympy.Expr:
    return sympy.diff(expression, symbol, order).subs(symbol, 0) / sympy.factorial(order)


def canonical_torus_smooth_recovery_rate(
    endpoint: RecoveryEndpoint | str,
    thickness: sympy.Symbol | None = None,
    *,
    surface_field: CanonicalTorusSolenoidalField | None = None,
) -> TorusRecoveryRateCertificate:
    """Certify strong convergence and the smooth-core quadratic energy rate.

    The expressions are the universal two-jet of the exact recovery returned
    by :func:`canonical_torus_smooth_recovery`; equality of all three component
    jets is part of the certificate.  The normal-tangential block of the
    endpoint energy tensor also vanishes at leading order.  Consequently the
    one normal derivative lost when replacing ``sigma`` by ``varepsilon*z``
    cannot change the energy through quadratic order.  Undefined
    stream-function derivatives are replaced injectively by independent jet
    symbols before differentiating in thickness; this avoids asking SymPy to
    order multivariate derivative objects while preserving the polynomial
    identity.
    """

    selected = _coerce_endpoint(endpoint)
    epsilon = thickness or sympy.Symbol("varepsilon", positive=True)
    if not isinstance(epsilon, sympy.Symbol) or epsilon.is_positive is not True:
        raise RecoveryConstructionError("thickness must be a positive SymPy symbol")
    field = surface_field or canonical_torus_smooth_solenoidal_field()
    chart = field.chart
    if chart != torus_shell_chart(2, 1):
        raise RecoveryConstructionError("the first arbitrary recovery theorem is scoped to the canonical torus")

    alpha = selected.alpha
    theta, phi = chart.surface.coords
    sigma = chart.sigma
    z = sympy.Symbol("z", real=True)
    rho = chart.surface.volume_density
    curvatures: SurfaceComponents = tuple(
        simp(chart.shape_operator[index, index].subs(sigma, 0)) for index in range(2)
    )  # type: ignore[assignment]
    trace = sum(curvatures)
    gaussian = curvatures[0] * curvatures[1]
    moment_second = tuple(
        gaussian
        + alpha * (1 + 2 * alpha) * curvature**2
        - 2 * alpha * curvature * trace
        for curvature in curvatures
    )
    moment_average = tuple(value / 3 for value in moment_second)
    tangential: SurfaceComponents = tuple(
        field.components[index]
        * (
            1
            + 2 * alpha * curvatures[index] * sigma
            + alpha * (1 + 2 * alpha) * curvatures[index] ** 2 * sigma**2
            - epsilon**2 * moment_average[index]
        )
        for index in range(2)
    )  # type: ignore[assignment]
    first_flux_coefficients = tuple(2 * alpha * curvature - trace for curvature in curvatures)
    leading_divergence_defect = sympy.cancel(
        (
            sympy.diff(rho * first_flux_coefficients[0] * field.components[0], theta)
            + sympy.diff(rho * first_flux_coefficients[1] * field.components[1], phi)
        )
        / rho
    )
    normal = (epsilon**2 - sigma**2) * leading_divergence_defect / 2
    shell_components: ShellComponents = (*tangential, normal)

    if selected is RecoveryEndpoint.NAVIER:
        shell_tensor = kernel.deformation_tensor(chart.shell, shell_components)
        surface_tensor = kernel.deformation_tensor(chart.surface, field.components)
        fast_tensor = (shell_tensor[0, 2], shell_tensor[1, 2])
        shell_density = 2 * kernel.covariant_tensor_squared_norm(chart.shell, shell_tensor)
        surface_density = 2 * kernel.covariant_tensor_squared_norm(chart.surface, surface_tensor)
    else:
        shell_tensor = kernel.exterior_derivative_one_form(chart.shell, shell_components)
        surface_tensor = kernel.exterior_derivative_one_form(chart.surface, field.components)
        fast_tensor = (shell_tensor[2, 0], shell_tensor[2, 1])
        shell_density = kernel.covariant_tensor_squared_norm(chart.shell, shell_tensor) / 2
        surface_density = kernel.covariant_tensor_squared_norm(chart.surface, surface_tensor) / 2

    shell_energy = (shell_density * chart.shell.volume_density).subs(sigma, epsilon * z)
    surface_energy = surface_density * chart.surface.volume_density
    exact = canonical_torus_smooth_recovery(
        selected,
        epsilon,
        surface_field=field,
    )
    exact_rescaled = tuple(
        component.subs(sigma, epsilon * z) for component in exact.shell_components
    )
    approximate_rescaled = tuple(
        component.subs(sigma, epsilon * z) for component in shell_components
    )
    difference = (
        tangential[0] - field.components[0],
        tangential[1] - field.components[1],
        normal,
    )
    strong_difference = (
        kernel.vector_squared_norm(chart.shell, difference) * chart.shell.volume_density
    ).subs(sigma, epsilon * z)
    substituted, jet_symbols, jet_atoms = _jet_substitution(
        (
            *exact_rescaled,
            *approximate_rescaled,
            shell_energy,
            surface_energy,
            strong_difference,
            *(component.subs(sigma, epsilon * z) for component in fast_tensor),
        )
    )
    exact_rescaled = substituted[:3]
    approximate_rescaled = substituted[3:6]
    shell_energy, surface_energy, strong_difference = substituted[6:9]
    fast_tensor = substituted[9:]

    component_jet_residuals = tuple(
        tuple(
            simp(_coefficient_at_zero(actual - approximate, epsilon, order))
            for order in range(3)
        )
        for actual, approximate in zip(
            exact_rescaled,
            approximate_rescaled,
            strict=True,
        )
    )

    shell_zeroth = _coefficient_at_zero(shell_energy, epsilon, 0)
    shell_first = _coefficient_at_zero(shell_energy, epsilon, 1)
    shell_second = _coefficient_at_zero(shell_energy, epsilon, 2)
    difference_zeroth = _coefficient_at_zero(strong_difference, epsilon, 0)
    difference_first = _coefficient_at_zero(strong_difference, epsilon, 1)
    difference_second = _coefficient_at_zero(strong_difference, epsilon, 2)
    energy_zeroth_residual = simp(shell_zeroth - surface_energy)
    energy_first_average = simp(sympy.integrate(shell_first, (z, -1, 1)) / 2)
    fast_tensor_zeroth = tuple(
        simp(_coefficient_at_zero(component, epsilon, 0)) for component in fast_tensor
    )

    return TorusRecoveryRateCertificate(
        endpoint=selected,
        alpha=alpha,
        chart=chart,
        thickness=epsilon,
        rescaled_normal_coordinate=z,
        surface_field=field,
        exact_recovery=exact,
        second_order_shell_components=shell_components,
        exact_component_jet_residuals=component_jet_residuals,
        fast_tensor_zeroth_residuals=fast_tensor_zeroth,
        surface_energy_integrand=surface_energy,
        shell_energy_zeroth=shell_zeroth,
        shell_energy_first=shell_first,
        shell_energy_second=shell_second,
        energy_zeroth_residual=energy_zeroth_residual,
        energy_first_average=energy_first_average,
        strong_difference_zeroth=simp(difference_zeroth),
        strong_difference_first=simp(difference_first),
        strong_difference_second=difference_second,
        jet_atoms=jet_atoms,
        jet_symbols=jet_symbols,
        assumptions=(
            *field.assumptions,
            "the shell half-thickness satisfies 0 < varepsilon < 1/4",
            "the exact rational recovery is expanded at varepsilon = 0 with sigma = varepsilon z",
            "the smooth field has bounded derivatives through order three on the compact torus",
        ),
        source_locator=(
            "arXiv:2605.20589v3, Theorem 4.5 (M2), Section 3.4, "
            "and Appendix A.4 energy expansion"
        ),
        scope=(
            "universal smooth-core strong recovery and O(varepsilon^2) energy rate on the "
            "canonical torus for both endpoint forms"
        ),
    )


@dataclass(frozen=True)
class NavierTorusRecoveryCertificate:
    """A checked Navier recovery family for one nonconstant torus mode.

    Thickness is the *half-thickness*: the shell occupies
    ``-varepsilon < sigma < varepsilon`` and bulk integrals are normalized by
    ``1 / (2 varepsilon)``.
    """

    chart: ShellChart
    thickness: sympy.Symbol
    surface_components: SurfaceComponents
    shell_components: ShellComponents
    surface_divergence: sympy.Expr
    shell_divergence: sympy.Expr
    wall_normal_traces: tuple[sympy.Expr, sympy.Expr]
    wall_stress_residuals: WallResiduals
    identified_components: SurfaceComponents
    weighted_transverse_average: SurfaceComponents
    surface_energy_density: sympy.Expr
    shell_energy_density: sympy.Expr
    surface_energy: sympy.Expr
    normalized_shell_energy: sympy.Expr
    energy_limit: sympy.Expr
    energy_error_coefficient: sympy.Expr
    surface_l2_norm_squared: sympy.Expr
    normalized_shell_l2_norm_squared: sympy.Expr
    norm_limit: sympy.Expr
    norm_error_coefficient: sympy.Expr
    assumptions: tuple[str, ...]
    source_locator: str
    scope: str

    def __post_init__(self) -> None:
        _require_zero(self.surface_divergence, "surface divergence")
        _require_zero(self.shell_divergence, "shell divergence")
        for wall, trace in zip(("inner", "outer"), self.wall_normal_traces, strict=True):
            _require_zero(trace, f"{wall} normal trace")
        for wall, residual in zip(("inner", "outer"), self.wall_stress_residuals, strict=True):
            for component, value in enumerate(residual):
                _require_zero(value, f"{wall} stress-free residual component {component}")
        for component, (actual, expected) in enumerate(zip(self.identified_components, self.surface_components, strict=True)):
            _require_equal(actual, expected, f"identified tangential component {component}")
        for component, (actual, expected) in enumerate(zip(self.weighted_transverse_average, self.surface_components, strict=True)):
            _require_equal(actual, expected, f"weighted transverse average component {component}")
        _require_equal(self.energy_limit, self.surface_energy, "deformation-energy limit")
        _require_equal(self.norm_limit, self.surface_l2_norm_squared, "normalized L2 limit")
        if self.energy_error_coefficient.has(sympy.oo, -sympy.oo, sympy.zoo, sympy.nan):
            raise RecoveryConstructionError("the quadratic energy-error coefficient is not finite")
        if self.norm_error_coefficient.has(sympy.oo, -sympy.oo, sympy.zoo, sympy.nan):
            raise RecoveryConstructionError("the quadratic norm-error coefficient is not finite")
        if is_zero(self.surface_energy) is not False:
            raise RecoveryConstructionError("the selected surface mode must have nonzero deformation energy")

    @property
    def energy_defect(self) -> sympy.Expr:
        return simp(self.normalized_shell_energy - self.surface_energy)

    @property
    def norm_defect(self) -> sympy.Expr:
        return simp(self.normalized_shell_l2_norm_squared - self.surface_l2_norm_squared)


def canonical_navier_torus_recovery(thickness: sympy.Symbol | None = None) -> NavierTorusRecoveryCertificate:
    """Construct the exact recovery ``U_eps = sin(theta) partial_phi``.

    The surface is the torus of revolution with major radius 2 and minor
    radius 1.  For ``0 < varepsilon < 1`` the same coordinate field throughout
    the normal shell is smooth, exactly solenoidal, impermeable, and
    stress-free.  Its normal corrector vanishes for this azimuthal mode.

    This is a single smooth recovery family, not a proof for arbitrary data and
    not a proof of Mosco convergence.
    """

    epsilon = thickness or sympy.Symbol("varepsilon", positive=True)
    if not isinstance(epsilon, sympy.Symbol) or epsilon.is_positive is not True:
        raise RecoveryConstructionError("thickness must be a positive SymPy symbol")

    chart = torus_shell_chart(2, 1)
    theta, phi = chart.surface.coords
    sigma = chart.sigma
    surface_components: SurfaceComponents = (sympy.Integer(0), sympy.sin(theta))
    shell_components: ShellComponents = (*surface_components, sympy.Integer(0))

    surface_divergence = kernel.divergence(chart.surface, surface_components)
    shell_divergence = kernel.divergence(chart.shell, shell_components)
    shell_deformation = kernel.deformation_tensor(chart.shell, shell_components)
    wall_normal_traces = tuple(shell_components[2].subs(sigma, wall) for wall in (-epsilon, epsilon))
    wall_stress_residuals: WallResiduals = tuple(
        tuple(simp(shell_deformation[index, 2].subs(sigma, wall)) for index in range(2)) for wall in (-epsilon, epsilon)
    )  # type: ignore[assignment]

    identified_components: SurfaceComponents = tuple(component.subs(sigma, 0) for component in shell_components[:2])  # type: ignore[assignment]
    transverse_weight = chart.jacobian
    transverse_mass = sympy.integrate(transverse_weight, (sigma, -epsilon, epsilon))
    weighted_transverse_average: SurfaceComponents = tuple(
        simp(sympy.integrate(component * transverse_weight, (sigma, -epsilon, epsilon)) / transverse_mass)
        for component in shell_components[:2]
    )  # type: ignore[assignment]

    surface_deformation = kernel.deformation_tensor(chart.surface, surface_components)
    surface_energy_density = simp(2 * kernel.covariant_tensor_squared_norm(chart.surface, surface_deformation))
    shell_energy_density = simp(2 * kernel.covariant_tensor_squared_norm(chart.shell, shell_deformation))

    surface_energy = simp(
        sympy.integrate(
            surface_energy_density * chart.surface.volume_density,
            (theta, 0, 2 * sympy.pi),
            (phi, 0, 2 * sympy.pi),
        )
    )
    normalized_shell_energy = simp(
        sympy.integrate(
            shell_energy_density * chart.shell.volume_density,
            (theta, 0, 2 * sympy.pi),
            (phi, 0, 2 * sympy.pi),
            (sigma, -epsilon, epsilon),
        )
        / (2 * epsilon)
    )
    energy_limit = sympy.limit(normalized_shell_energy, epsilon, 0, dir="+")
    energy_error_coefficient = simp(sympy.limit((normalized_shell_energy - surface_energy) / epsilon**2, epsilon, 0, dir="+"))

    surface_l2_norm_squared = simp(
        sympy.integrate(
            kernel.vector_squared_norm(chart.surface, surface_components) * chart.surface.volume_density,
            (theta, 0, 2 * sympy.pi),
            (phi, 0, 2 * sympy.pi),
        )
    )
    normalized_shell_l2_norm_squared = simp(
        sympy.integrate(
            kernel.vector_squared_norm(chart.shell, shell_components) * chart.shell.volume_density,
            (theta, 0, 2 * sympy.pi),
            (phi, 0, 2 * sympy.pi),
            (sigma, -epsilon, epsilon),
        )
        / (2 * epsilon)
    )
    norm_limit = sympy.limit(normalized_shell_l2_norm_squared, epsilon, 0, dir="+")
    norm_error_coefficient = simp(
        sympy.limit((normalized_shell_l2_norm_squared - surface_l2_norm_squared) / epsilon**2, epsilon, 0, dir="+")
    )

    return NavierTorusRecoveryCertificate(
        chart=chart,
        thickness=epsilon,
        surface_components=surface_components,
        shell_components=shell_components,
        surface_divergence=surface_divergence,
        shell_divergence=shell_divergence,
        wall_normal_traces=wall_normal_traces,
        wall_stress_residuals=wall_stress_residuals,
        identified_components=identified_components,
        weighted_transverse_average=weighted_transverse_average,
        surface_energy_density=surface_energy_density,
        shell_energy_density=shell_energy_density,
        surface_energy=surface_energy,
        normalized_shell_energy=normalized_shell_energy,
        energy_limit=energy_limit,
        energy_error_coefficient=energy_error_coefficient,
        surface_l2_norm_squared=surface_l2_norm_squared,
        normalized_shell_l2_norm_squared=normalized_shell_l2_norm_squared,
        norm_limit=norm_limit,
        norm_error_coefficient=norm_error_coefficient,
        assumptions=(
            "the shell half-thickness satisfies 0 < varepsilon < 1",
            "the torus has major radius 2 and minor radius 1",
            "bulk mass and energy use the normalization 1/(2 varepsilon)",
        ),
        source_locator="arXiv:2605.20589v3, Theorem 4.5 (M2) and Appendix A.4, restricted to alpha=0 and one azimuthal mode",
        scope="one exact smooth Navier recovery family; no arbitrary-data, density, liminf, or Mosco theorem",
    )
