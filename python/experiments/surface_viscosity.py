"""Validate surface-viscosity identities and the 2025/2026 paper formulas."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence

import jax
import jax.numpy as jnp

from experiments.surfaces import SurfaceCase, sample_points, surface_cases
from riemannian_fluids.geometry import (
    covariant_tensor_norm,
    extrinsic_gaussian_curvature,
    intrinsic_gaussian_curvature,
    mean_curvature,
    metric,
    vector_norm,
    vector_squared_norm,
)
from riemannian_fluids.operators import (
    deformation_laplacian,
    hodge_laplacian,
    interpolating_viscosity,
    ricci_action,
    rough_laplacian,
)
from riemannian_fluids.shells import (
    AmbientJets,
    ambient_positive_laplacian_tangent,
    ambient_restriction_formula,
    matched_wall_jets,
)
from riemannian_fluids.tensors import (
    deformation_tensor,
    divergence,
    gradient,
    lie_bracket,
    lie_derivative_metric,
    raised_lie_derivative_one_form,
    stream_vector_field,
)
from riemannian_fluids.types import Array, Embedding, ScalarField, VectorField

SOURCE_2025 = "arXiv:2511.10579v1, equations (1.5)-(1.8)"
SOURCE_2026 = "arXiv:2605.20589v3, equations (12)-(17)"


def relative_vector_residual(
    embedding: Embedding,
    left: Array,
    right: Array,
    q: Array,
) -> Array:
    numerator = vector_norm(embedding, left - right, q)
    denominator = jnp.maximum(
        jnp.maximum(vector_norm(embedding, left, q), vector_norm(embedding, right, q)),
        1.0e-12,
    )
    return numerator / denominator


def ellipsoid_scaling_generator(embedding: Embedding) -> VectorField:
    """Return ``A=-1/4 grad(log K)`` for the cited spheroid."""

    def generator(q: Array) -> Array:
        return -0.25 * gradient(
            embedding,
            lambda point: jnp.log(intrinsic_gaussian_curvature(embedding, point)),
            q,
        )

    return generator


def ellipsoid_2025_candidates(
    embedding: Embedding,
    field: VectorField,
    q: Array,
) -> tuple[Array, Array, Array, Array]:
    generator = ellipsoid_scaling_generator(embedding)
    deformation = deformation_laplacian(embedding, field, q)
    hodge = hodge_laplacian(embedding, field, q)
    bracket = lie_bracket(generator, field, q)
    one_form_lie = raised_lie_derivative_one_form(embedding, generator, field, q)
    generator_value = generator(q)
    component = (field(q) @ metric(embedding, q) @ generator_value) * generator_value
    return (
        deformation + bracket + 2.0 * component,
        hodge + one_form_lie,
        deformation + bracket,
        hodge + one_form_lie - 2.0 * component,
    )


def diagnostic_ambient_jets(field: VectorField) -> AmbientJets:
    def first_tangent(q: Array) -> Array:
        first, second = q
        return jnp.asarray((0.23 * jnp.sin(first + 0.7 * second), -0.19 * jnp.cos(1.3 * first - second)))

    def second_tangent(q: Array) -> Array:
        first, second = q
        return jnp.asarray((-0.17 * jnp.cos(0.8 * first + second), 0.13 * jnp.sin(first - 1.1 * second)))

    def normal_value(q: Array) -> Array:
        first, second = q
        return 0.11 * jnp.sin(1.2 * first) * jnp.cos(0.9 * second)

    def normal_first(q: Array) -> Array:
        first, second = q
        return -0.07 * jnp.cos(first + second)

    def normal_second(q: Array) -> Array:
        first, second = q
        return 0.05 * jnp.sin(0.6 * first - 1.4 * second)

    return AmbientJets(field, first_tangent, second_tangent, normal_value, normal_first, normal_second)


def normal_derivative_diagnostics() -> tuple[ScalarField, ScalarField]:
    def normal_first(q: Array) -> Array:
        first, second = q
        return 0.09 * jnp.sin(first + 0.4 * second)

    def normal_second(q: Array) -> Array:
        first, second = q
        return -0.06 * jnp.cos(0.7 * first - second)

    return normal_first, normal_second


def ambient_point_diagnostics(case: SurfaceCase, q: Array, partial_alpha: float) -> Array:
    embedding = case.embedding
    field = stream_vector_field(embedding, case.stream_function)
    manufactured = diagnostic_ambient_jets(field)
    zero_weights = jnp.zeros((6,), dtype=q.dtype)
    direct_contributions = jax.jacfwd(lambda switches: ambient_positive_laplacian_tangent(embedding, manufactured, switches, q))(zero_weights)
    direct_unrestricted = jnp.sum(direct_contributions, axis=1)
    predicted_unrestricted = ambient_restriction_formula(embedding, manufactured, q)
    unrestricted_residual = relative_vector_residual(embedding, direct_unrestricted, predicted_unrestricted, q)

    normal_first, normal_second = normal_derivative_diagnostics()
    boundary_residuals = []
    for alpha in (0.0, partial_alpha, 1.0):
        profile = matched_wall_jets(embedding, field, normal_first, normal_second, alpha)
        direct = ambient_positive_laplacian_tangent(embedding, profile, jnp.ones((6,), dtype=q.dtype), q)
        expected = interpolating_viscosity(embedding, field, q, alpha)
        boundary_residuals.append(relative_vector_residual(embedding, direct, expected, q))

    navier_direct = ambient_positive_laplacian_tangent(
        embedding,
        matched_wall_jets(embedding, field, normal_first, normal_second, 0.0),
        jnp.ones((6,), dtype=q.dtype),
        q,
    )
    hodge_direct = ambient_positive_laplacian_tangent(
        embedding,
        matched_wall_jets(embedding, field, normal_first, normal_second, 1.0),
        jnp.ones((6,), dtype=q.dtype),
        q,
    )
    endpoint_navier = relative_vector_residual(embedding, navier_direct, deformation_laplacian(embedding, field, q), q)
    endpoint_hodge = relative_vector_residual(embedding, hodge_direct, hodge_laplacian(embedding, field, q), q)
    contribution_norms = [vector_norm(embedding, direct_contributions[:, index], q) for index in range(6)]
    return jnp.asarray(
        (
            unrestricted_residual,
            *boundary_residuals,
            endpoint_navier,
            endpoint_hodge,
            *contribution_norms,
        )
    )


def paper_2025_point_comparison(case: SurfaceCase, q: Array) -> Array:
    embedding = case.embedding
    field = stream_vector_field(embedding, case.stream_function)
    candidates = ellipsoid_2025_candidates(embedding, field, q)
    baselines = (
        deformation_laplacian(embedding, field, q),
        hodge_laplacian(embedding, field, q),
    ) * 2
    comparisons = []
    for baseline, candidate in zip(baselines, candidates, strict=True):
        comparisons.append(
            jnp.asarray(
                (
                    vector_squared_norm(embedding, baseline - candidate, q),
                    vector_squared_norm(embedding, baseline, q),
                    vector_squared_norm(embedding, candidate, q),
                )
            )
        )
    return jnp.stack(comparisons)


def point_residuals(case: SurfaceCase, q: Array) -> Array:
    embedding = case.embedding
    field = stream_vector_field(embedding, case.stream_function)
    rough = rough_laplacian(embedding, field, q)
    hodge = hodge_laplacian(embedding, field, q)
    deformation = deformation_laplacian(embedding, field, q)
    ricci = ricci_action(embedding, field, q)
    grad_divergence = gradient(embedding, lambda point: divergence(embedding, field, point), q)
    return jnp.asarray(
        (
            jnp.abs(divergence(embedding, field, q)),
            covariant_tensor_norm(
                embedding,
                lie_derivative_metric(embedding, field, q) - 2.0 * deformation_tensor(embedding, field, q),
                q,
            ),
            jnp.abs(intrinsic_gaussian_curvature(embedding, q) - extrinsic_gaussian_curvature(embedding, q)),
            relative_vector_residual(embedding, hodge, rough + ricci, q),
            relative_vector_residual(embedding, deformation, rough - ricci - grad_divergence, q),
            relative_vector_residual(embedding, deformation, hodge - 2.0 * ricci, q),
            jnp.abs(mean_curvature(embedding, q)),
            jnp.abs(intrinsic_gaussian_curvature(embedding, q)),
        )
    )


def run_case(case: SurfaceCase, count: int, partial_alpha: float) -> dict[str, object]:
    points = sample_points(case, count)
    maxima = jnp.max(jax.jit(jax.vmap(lambda q: point_residuals(case, q)))(points), axis=0)
    ambient_maxima = jnp.max(
        jax.jit(jax.vmap(lambda q: ambient_point_diagnostics(case, q, partial_alpha)))(points),
        axis=0,
    )
    result: dict[str, object] = {
        "surface": case.name,
        "sample_count": int(points.shape[0]),
        "max_abs_divergence": float(maxima[0]),
        "max_abs_lie_def_residual": float(maxima[1]),
        "max_abs_gauss_residual": float(maxima[2]),
        "max_rel_weizenbock_residual": float(maxima[3]),
        "max_rel_deformation_residual": float(maxima[4]),
        "max_rel_div_free_candidate_residual": float(maxima[5]),
        "ambient_restriction": {
            "max_rel_unrestricted_formula_residual": float(ambient_maxima[0]),
            "direct_contribution_max_norms": {
                name: float(ambient_maxima[index]) for name, index in zip(("u0", "u1", "u2", "w0", "w1", "w2"), range(6, 12), strict=True)
            },
        },
        "boundary_reductions_2026": {
            "source": SOURCE_2026,
            "navier": {
                "alpha": 0.0,
                "max_rel_ambient_vs_2026": float(ambient_maxima[1]),
                "max_rel_ambient_vs_deformation": float(ambient_maxima[4]),
            },
            "partial_slip": {
                "alpha": partial_alpha,
                "max_rel_ambient_vs_2026": float(ambient_maxima[2]),
            },
            "hodge": {
                "alpha": 1.0,
                "max_rel_ambient_vs_2026": float(ambient_maxima[3]),
                "max_rel_ambient_vs_hodge": float(ambient_maxima[5]),
            },
            "positive_formula": "L_Def+2*alpha*Ric+4*alpha*(1-alpha)*S^2",
        },
    }
    if case.name in {"sphere", "ellipsoid"}:
        comparison = jax.jit(jax.vmap(lambda q: paper_2025_point_comparison(case, q)))(points)
        sums = jnp.sum(comparison, axis=0)
        relative = jnp.sqrt(sums[:, 0]) / jnp.maximum(jnp.maximum(jnp.sqrt(sums[:, 1]), jnp.sqrt(sums[:, 2])), 1.0e-12)
        result["scaling_candidates_2025"] = {
            "status": "evaluated",
            "source": SOURCE_2025,
            "values": [float(value) for value in relative],
        }
    else:
        result["scaling_candidates_2025"] = {
            "status": "not_applicable",
            "source": SOURCE_2025,
            "reason": "published formulas are specific to the axisymmetric ellipsoid",
        }
    return result


def validate_results(results: Sequence[dict[str, object]], tolerance: float) -> None:
    failures = []
    intrinsic_names = (
        "max_abs_divergence",
        "max_abs_lie_def_residual",
        "max_abs_gauss_residual",
        "max_rel_weizenbock_residual",
        "max_rel_deformation_residual",
        "max_rel_div_free_candidate_residual",
    )
    for result in results:
        for name in intrinsic_names:
            if float(result[name]) > tolerance:
                failures.append(f"{result['surface']}:{name}={float(result[name]):.3e}")
        ambient = result["ambient_restriction"]
        boundary = result["boundary_reductions_2026"]
        assert isinstance(ambient, dict) and isinstance(boundary, dict)
        checks = [ambient["max_rel_unrestricted_formula_residual"]]
        for name in ("navier", "partial_slip", "hodge"):
            value = boundary[name]
            assert isinstance(value, dict)
            checks.append(value["max_rel_ambient_vs_2026"])
        if any(float(value) > tolerance for value in checks):
            failures.append(f"{result['surface']}:ambient boundary identity")
    if failures:
        raise AssertionError("Surface-viscosity validation failed:\n  " + "\n  ".join(failures))


def print_table(results: Sequence[dict[str, object]], partial_alpha: float) -> None:
    print("surface                 div          Lie=2Def     Gauss        Weitzenbock  Def identity candidate")
    for result in results:
        print(
            f"{result['surface']!s:23s} "
            f"{float(result['max_abs_divergence']):.3e}  "
            f"{float(result['max_abs_lie_def_residual']):.3e}  "
            f"{float(result['max_abs_gauss_residual']):.3e}  "
            f"{float(result['max_rel_weizenbock_residual']):.3e}  "
            f"{float(result['max_rel_deformation_residual']):.3e}  "
            f"{float(result['max_rel_div_free_candidate_residual']):.3e}"
        )
    print(f"\n2026 two-wall reductions; partial-slip alpha={partial_alpha:g}")
    print("surface                 unrestricted  Navier       partial      Hodge")
    for result in results:
        ambient = result["ambient_restriction"]
        boundary = result["boundary_reductions_2026"]
        assert isinstance(ambient, dict) and isinstance(boundary, dict)
        values = []
        for name in ("navier", "partial_slip", "hodge"):
            value = boundary[name]
            assert isinstance(value, dict)
            values.append(float(value["max_rel_ambient_vs_2026"]))
        print(f"{result['surface']!s:23s} {float(ambient['max_rel_unrestricted_formula_residual']):.3e}  {values[0]:.3e}  {values[1]:.3e}  {values[2]:.3e}")
    print("\n2025 ellipsoid candidates versus normal-direction endpoints")
    for result in results:
        comparison = result["scaling_candidates_2025"]
        assert isinstance(comparison, dict)
        if comparison["status"] == "evaluated":
            values = comparison["values"]
            assert isinstance(values, list)
            formatted = "  ".join(f"{float(value):.3e}" for value in values)
            print(f"{result['surface']!s:23s} {formatted}")
        else:
            print(f"{result['surface']!s:23s} not applicable")


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--tolerance", type=float, default=2.0e-8)
    parser.add_argument("--partial-slip-alpha", type=float, default=0.5)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    if args.samples < 2:
        parser.error("--samples must be at least 2")
    if args.tolerance <= 0.0:
        parser.error("--tolerance must be positive")
    if not 0.0 < args.partial_slip_alpha < 1.0:
        parser.error("--partial-slip-alpha must lie strictly between zero and one")
    results = [run_case(case, args.samples, args.partial_slip_alpha) for case in surface_cases()]
    validate_results(results, args.tolerance)
    if args.as_json:
        print(json.dumps(results, indent=2, sort_keys=True))
    else:
        print_table(results, args.partial_slip_alpha)


if __name__ == "__main__":
    main()
