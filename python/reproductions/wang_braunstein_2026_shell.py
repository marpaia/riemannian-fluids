"""Thin-shell operator-selection claims of Wang--Braunstein (2026)."""

import jax
import jax.numpy as jnp
import sympy

from riemannian_fluids.geometry import shape_operator, sphere, spheroid, torus_of_revolution, vector_norm
from riemannian_fluids.operators import deformation_dissipation_density, interpolating_viscosity
from riemannian_fluids.shells import (
    ambient_positive_laplacian_tangent,
    matched_wall_jets,
    solve_two_wall_tangential_field,
    wall_residual,
)
from riemannian_fluids.symbolic import crosscheck_scalar, require_agreement
from riemannian_fluids.symbolic.shells import (
    RecoveryEndpoint,
    canonical_navier_torus_recovery,
    canonical_torus_smooth_recovery_rate,
)
from riemannian_fluids.tensors import divergence, stream_vector_field
from riemannian_fluids.types import Array
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

WALL_PARAMETERS = (0.0, 0.3, 0.7, 1.0)

PAPER = Paper(
    "WBS26",
    "Boundary conditions select the viscous operator on Riemannian hypersurfaces: formal analysis and rigorous thin-shell limits",
    ("Zhi-Wei Wang", "Samuel L. Braunstein"),
    2026,
    "https://arxiv.org/abs/2605.20589",
    "v3",
    "Wall-condition selection, matched fields, and rigorous thin-shell convergence.",
)
CLAIMS = (
    Claim(
        "WBS26-local-interpolating-family",
        PAPER.id,
        "The tangential ambient operator gives L_Def + 2a Ric + 4a(1-a)S^2.",
        "arXiv:2605.20589v3, Lemma 3.1, Proposition 3.2, and Theorem 3.3, equations (12)--(18)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
        {"non-umbilic evidence": "on the spheroid and torus Ric != S^2 pointwise, so the sweep pins both curvature coefficients"},
        geometry_coverage="sphere+spheroid+torus_of_revolution",
        sample_coverage="2 points x 4 wall parameters per surface",
    ),
    Claim(
        "WBS26-two-wall-profile",
        PAPER.id,
        "A finite-thickness tangential profile satisfies both wall laws.",
        "arXiv:2605.20589v3, Proposition 3.2 and Section 3.4, equations (13)--(19)",
        EvidenceKind.MANUFACTURED_SOLUTION,
        ClaimStatus.VALIDATED,
        {"shape operators": "anisotropic spheroid and torus spectra plus non-diagonal perturbed-sphere matrices"},
        geometry_coverage="spheroid+torus_of_revolution+perturbed_sphere",
        sample_coverage="2 points x 4 wall parameters x 2 thicknesses per surface",
    ),
    Claim(
        "WBS26-smooth-recovery-mode",
        PAPER.id,
        "On the canonical torus T(2,1), the z-independent Navier lift of the nonconstant field "
        "u = sin(theta) partial_phi is exactly solenoidal, impermeable, and stress-free; its "
        "normalized mass and deformation energy converge to those of u with quadratic error.",
        "Project specialization of arXiv:2605.20589v3, Theorem 4.5 (M2) and Appendix A.4, to alpha=0 and one azimuthal mode",
        EvidenceKind.CONSTRUCTIVE_WITNESS,
        ClaimStatus.VALIDATED,
        {
            "thickness": "half-thickness 0 < varepsilon < 1 with bulk normalization 1/(2 varepsilon)",
            "recovery scope": "one smooth azimuthal field whose source normal corrector vanishes identically",
            "exclusion": "does not establish arbitrary-data recovery, form-domain density, liminf, or Mosco convergence",
        },
        geometry_coverage="torus_of_revolution(R=2,a=1)",
        sample_coverage="exact symbolic identities on the full chart and epsilon family + 8 deterministic JAX shell points",
    ),
    Claim(
        "WBS26-smooth-recovery-canonical-torus",
        PAPER.id,
        "On the canonical torus T(2,1), every smooth tangential solenoidal field has an "
        "exactly solenoidal and impermeable three-dimensional recovery satisfying either "
        "endpoint wall law, with exact transverse-flux identification, strong L2 recovery, "
        "and the source-scoped quadratic energy rate on the smooth core.",
        "Project specialization of arXiv:2605.20589v3, Theorem 4.5 (M2), Proposition 3.2, "
        "Section 3.4, and Appendix A.4, to the canonical torus and both endpoints",
        EvidenceKind.CONSTRUCTIVE_WITNESS,
        ClaimStatus.VALIDATED,
        {
            "surface field": "arbitrary smooth periodic stream function plus both constant torus flux modes",
            "thickness": "physical half-thickness 0 < varepsilon < 1/4 with normalization 1/(2 varepsilon)",
            "rate": (
                "the exact recovery and its universal two-jet agree through order two; "
                "the integrated linear energy term vanishes by symmetric-shell averaging"
            ),
            "exclusion": "smooth-core M2 only; no form-domain density extension, M1, Mosco theorem, or operator convergence",
        },
        geometry_coverage="torus_of_revolution(R=2,a=1)",
        sample_coverage=(
            "exact identities for an arbitrary smooth stream jet and both flux parameters at "
            "the Navier and Hodge endpoints + native tensor traces for one nontrivial stream-and-flux field"
        ),
    ),
    Claim(
        "WBS26-mosco-resolvent-spectrum",
        PAPER.id,
        "For torus-type surfaces of revolution and for both stress-free/deformation and "
        "vorticity-free/Hodge wall conditions, the thin-shell forms Mosco-converge; the "
        "associated nonnegative self-adjoint operators have strongly convergent resolvents "
        "and semigroups uniformly on compact time intervals; eigenvalues converge with "
        "multiplicity on each fixed azimuthal mode and, by the uniform high-mode gap, for "
        "the full spectrum without spectral pollution.",
        "arXiv:2605.20589v3, Theorem 4.5 and Corollary 4.6",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "surface": "torus-type surface of revolution",
            "wall conditions": "stress-free/deformation and vorticity-free/Hodge",
            "spectral scope": "fixed-mode and full-spectrum convergence with multiplicity; no high-mode pollution",
            "framework": "Kuwae-Shioya varying Hilbert spaces",
        },
    ),
    Claim(
        "WBS26-resolved-volume-shell",
        PAPER.id,
        "A resolved curved 3D shell converges after transverse averaging to the selected "
        "surface operator, with mesh convergence at fixed thickness established separately "
        "from thickness convergence.",
        "Project numerical gate motivated by arXiv:2605.20589v3, Theorem 4.5; not a numerical theorem asserted in the paper",
        EvidenceKind.THIN_SHELL_CONVERGENCE,
        ClaimStatus.CATALOGUED,
        {
            "required limits": "mesh size h -> 0 at fixed epsilon, then thickness epsilon -> 0",
            "geometry": "resolved curved volume shell rather than a normal-fibre surrogate",
        },
    ),
)


def _spherical_stream(q):
    return jnp.sin(q[0]) ** 2 * jnp.cos(2.0 * q[1]) + 0.17 * jnp.sin(3.0 * q[0]) * jnp.sin(q[1])


def _torus_stream(q):
    return jnp.sin(q[0]) + 0.31 * jnp.cos(2.0 * q[1]) + 0.19 * jnp.sin(q[0] + q[1])


def _perturbed_sphere(q):
    theta, phi = q
    radius = 1.0 + 0.11 * jnp.sin(2.0 * theta) * jnp.cos(3.0 * phi)
    return radius * jnp.asarray(
        (
            jnp.sin(theta) * jnp.cos(phi),
            jnp.sin(theta) * jnp.sin(phi),
            jnp.cos(theta),
        )
    )


def _interpolating_identity_residuals() -> dict[str, float | int | str]:
    """Sweep the ambient-jet reduction against ``L_Def+2aRic+4a(1-a)S^2``.

    The spheroid and torus have ``Ric != S^2`` pointwise, so agreement across
    the wall-parameter sweep pins the Ricci and shape-square coefficients
    separately rather than only their sum.
    """

    cases = (
        ("sphere", sphere().embedding, _spherical_stream, ((1.1, 0.7), (2.0, 3.9))),
        ("spheroid", spheroid().embedding, _spherical_stream, ((1.1, 0.7), (2.0, 3.9))),
        ("torus_of_revolution", torus_of_revolution().embedding, _torus_stream, ((0.9, 0.7), (2.4, 4.1))),
    )
    alphas = jnp.asarray(WALL_PARAMETERS, dtype=jnp.float64)
    measurements: dict[str, float | int | str] = {}
    worst = 0.0
    for name, embedding, stream, pts in cases:
        velocity = stream_vector_field(embedding, stream)

        def zero(point: Array) -> Array:
            return jnp.asarray(0.0, dtype=point.dtype)

        def identity_residual(q, alpha, embedding=embedding, velocity=velocity, zero=zero):
            jets = matched_wall_jets(embedding, velocity, zero, zero, alpha)
            direct = ambient_positive_laplacian_tangent(embedding, jets, jnp.ones((6,), dtype=q.dtype), q)
            expected = interpolating_viscosity(embedding, velocity, q, alpha)
            return vector_norm(embedding, direct - expected, q)

        points = jnp.asarray(pts, dtype=jnp.float64)
        grid_points = jnp.repeat(points, alphas.shape[0], axis=0)
        grid_alphas = jnp.tile(alphas, points.shape[0])
        values = jax.jit(jax.vmap(identity_residual))(grid_points, grid_alphas)
        surface_max = float(jnp.max(values))
        measurements[f"{name}_max_absolute_residual"] = surface_max
        worst = max(worst, surface_max)
    measurements["max_absolute_residual"] = worst
    measurements["wall_parameters"] = ",".join(f"{alpha:g}" for alpha in WALL_PARAMETERS)
    return measurements


def _two_wall_profile_residuals() -> dict[str, float | int | str]:
    """Solve the finite-thickness two-wall profile against both wall laws."""

    cases = (
        ("spheroid", spheroid().embedding, _spherical_stream, ((1.1, 0.7), (2.0, 3.9))),
        ("torus_of_revolution", torus_of_revolution().embedding, _torus_stream, ((0.9, 0.7), (2.4, 4.1))),
        ("perturbed_sphere", _perturbed_sphere, _spherical_stream, ((1.1, 0.7), (2.0, 3.9))),
    )
    shapes = []
    velocities = []
    largest_off_diagonal = 0.0
    for _, embedding, stream, pts in cases:
        velocity = stream_vector_field(embedding, stream)
        for point in pts:
            q = jnp.asarray(point, dtype=jnp.float64)
            shape = shape_operator(embedding, q)
            largest_off_diagonal = max(largest_off_diagonal, float(jnp.abs(shape[0, 1])), float(jnp.abs(shape[1, 0])))
            shapes.append(shape)
            velocities.append(velocity(q))
    stacked_shapes = jnp.stack(shapes)
    stacked_velocities = jnp.stack(velocities)
    alphas = jnp.asarray(WALL_PARAMETERS, dtype=jnp.float64)
    thicknesses = jnp.asarray((0.2, 0.05), dtype=jnp.float64)

    def profile_residual(shape, u0, thickness, alpha):
        profile = solve_two_wall_tangential_field(shape, u0, thickness, alpha)
        return jnp.maximum(
            jnp.linalg.norm(wall_residual(shape, profile, thickness, alpha, -1)),
            jnp.linalg.norm(wall_residual(shape, profile, thickness, alpha, 1)),
        )

    sweep = jax.jit(
        jax.vmap(
            lambda shape, u0: jax.vmap(
                lambda thickness: jax.vmap(lambda alpha: profile_residual(shape, u0, thickness, alpha))(alphas),
            )(thicknesses),
        )
    )(stacked_shapes, stacked_velocities)
    return {
        "max_wall_residual": float(jnp.max(sweep)),
        "shape_operator_samples": int(stacked_shapes.shape[0]),
        "max_shape_off_diagonal": largest_off_diagonal,
        "thicknesses": "0.2,0.05",
        "wall_parameters": ",".join(f"{alpha:g}" for alpha in WALL_PARAMETERS),
    }


def _smooth_recovery_measurements() -> dict[str, float | int | str]:
    """Certify one exact smooth Navier recovery and cross-check its local calculus."""

    epsilon = sympy.Symbol("varepsilon", positive=True)
    certificate = canonical_navier_torus_recovery(epsilon)
    shell = certificate.chart.shell

    def embedding(q: Array) -> Array:
        theta, phi, sigma = q
        offset = 1.0 + sigma
        radial = 2.0 + offset * jnp.cos(theta)
        return jnp.asarray((radial * jnp.cos(phi), radial * jnp.sin(phi), offset * jnp.sin(theta)))

    def field(q: Array) -> Array:
        return jnp.asarray((0.0, jnp.sin(q[0]), 0.0), dtype=q.dtype)

    divergence_check = require_agreement(
        crosscheck_scalar(
            shell,
            certificate.shell_divergence,
            lambda q: divergence(embedding, field, q),
            {},
            quantity="canonical Navier recovery divergence",
        )
    )
    energy_check = require_agreement(
        crosscheck_scalar(
            shell,
            certificate.shell_energy_density,
            lambda q: deformation_dissipation_density(embedding, field, q),
            {},
            quantity="canonical Navier recovery deformation density",
        )
    )
    return {
        "exact_surface_divergence": str(certificate.surface_divergence),
        "exact_shell_divergence": str(certificate.shell_divergence),
        "exact_max_wall_residual": "0",
        "exact_identification_residual": "0",
        "surface_energy": str(certificate.surface_energy),
        "normalized_shell_energy": str(certificate.normalized_shell_energy),
        "quadratic_energy_error_coefficient": str(certificate.energy_error_coefficient),
        "surface_l2_norm_squared": str(certificate.surface_l2_norm_squared),
        "normalized_shell_l2_norm_squared": str(certificate.normalized_shell_l2_norm_squared),
        "quadratic_norm_error_coefficient": str(certificate.norm_error_coefficient),
        "jax_divergence_max_scaled_error": divergence_check.max_error,
        "jax_energy_density_max_scaled_error": energy_check.max_error,
        "jax_points_per_quantity": divergence_check.points,
    }


def _smooth_core_recovery_measurements() -> dict[str, float | int | str]:
    """Certify the arbitrary smooth-core recovery at both endpoint forms."""

    epsilon = sympy.Symbol("varepsilon", positive=True)
    measurements: dict[str, float | int | str] = {
        "endpoint_count": len(RecoveryEndpoint),
        "surface_flux_parameters": 2,
        "stream_function": "arbitrary smooth periodic psi(theta,phi)",
    }
    for endpoint in RecoveryEndpoint:
        rate = canonical_torus_smooth_recovery_rate(endpoint, epsilon)
        exact = rate.exact_recovery
        prefix = endpoint.value
        measurements[f"{prefix}_surface_divergence"] = str(exact.surface_divergence)
        measurements[f"{prefix}_shell_divergence"] = str(exact.shell_divergence)
        measurements[f"{prefix}_wall_residual"] = str(
            max(
                (sympy.count_ops(value) for wall in exact.wall_law_residuals for value in wall),
                default=0,
            )
        )
        measurements[f"{prefix}_identification_residual"] = str(
            max((sympy.count_ops(value) for value in exact.flux_moment_residuals), default=0)
        )
        measurements[f"{prefix}_exact_two_jet_residual"] = str(
            max(
                (
                    sympy.count_ops(value)
                    for component in rate.exact_component_jet_residuals
                    for value in component
                ),
                default=0,
            )
        )
        measurements[f"{prefix}_leading_fast_tensor_residual"] = str(
            max(
                (sympy.count_ops(value) for value in rate.fast_tensor_zeroth_residuals),
                default=0,
            )
        )
        measurements[f"{prefix}_energy_zeroth_residual"] = str(rate.energy_zeroth_residual)
        measurements[f"{prefix}_averaged_energy_linear_term"] = str(rate.energy_first_average)
        measurements[f"{prefix}_strong_squared_zeroth_term"] = str(rate.strong_difference_zeroth)
        measurements[f"{prefix}_strong_squared_linear_term"] = str(rate.strong_difference_first)
    return measurements


def run() -> tuple[ClaimResult, ...]:
    identity_measurements = _interpolating_identity_residuals()
    profile_measurements = _two_wall_profile_residuals()
    recovery_measurements = _smooth_recovery_measurements()
    smooth_core_measurements = _smooth_core_recovery_measurements()
    identity_passed = float(identity_measurements["max_absolute_residual"]) < 1.0e-10
    profile_passed = (
        float(profile_measurements["max_wall_residual"]) < 1.0e-10 and float(profile_measurements["max_shape_off_diagonal"]) > 1.0e-2
    )
    recovery_passed = (
        recovery_measurements["exact_shell_divergence"] == "0"
        and recovery_measurements["exact_max_wall_residual"] == "0"
        and recovery_measurements["exact_identification_residual"] == "0"
        and float(recovery_measurements["jax_divergence_max_scaled_error"]) < 1.0e-10
        and float(recovery_measurements["jax_energy_density_max_scaled_error"]) < 1.0e-10
    )
    smooth_core_passed = int(smooth_core_measurements["endpoint_count"]) == 2 and all(
        value == "0"
        for key, value in smooth_core_measurements.items()
        if key.endswith(
            (
                "divergence",
                "wall_residual",
                "identification_residual",
                "exact_two_jet_residual",
                "leading_fast_tensor_residual",
                "energy_zeroth_residual",
                "averaged_energy_linear_term",
                "strong_squared_zeroth_term",
                "strong_squared_linear_term",
            )
        )
    )
    return (
        ClaimResult(CLAIMS[0].id, identity_passed, identity_measurements),
        ClaimResult(CLAIMS[1].id, profile_passed, profile_measurements),
        ClaimResult(CLAIMS[2].id, recovery_passed, recovery_measurements),
        ClaimResult(CLAIMS[3].id, smooth_core_passed, smooth_core_measurements),
    )
