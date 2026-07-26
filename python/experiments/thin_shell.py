"""Finite-thickness study of two-wall fields and the solenoidal corrector."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence

import jax
import jax.numpy as jnp

from experiments.surfaces import SurfaceCase, sample_points, surface_cases
from riemannian_fluids.geometry import shape_operator, vector_norm
from riemannian_fluids.shells import (
    asymptotic_wall_jets,
    fermi_divergence,
    finite_thickness_jets,
    solve_two_wall_tangential_field,
    wall_residual,
)
from riemannian_fluids.tensors import stream_vector_field
from riemannian_fluids.types import Array, Embedding

SOURCE_2026 = "arXiv:2605.20589v3, equations (13)-(20)"


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


def point_metrics(case: SurfaceCase, q: Array, thickness: float, alpha: float) -> Array:
    embedding = case.embedding
    field = stream_vector_field(embedding, case.stream_function)
    shape = shape_operator(embedding, q)
    wall_field = solve_two_wall_tangential_field(shape, field(q), thickness, alpha)
    expected_u1, expected_u2 = asymptotic_wall_jets(shape, field(q), alpha)

    wall_error = jnp.maximum(
        vector_norm(embedding, wall_residual(shape, wall_field, thickness, alpha, -1), q),
        vector_norm(embedding, wall_residual(shape, wall_field, thickness, alpha, 1), q),
    )
    u1_error = relative_vector_residual(embedding, wall_field.u1, expected_u1, q)
    u2_error = relative_vector_residual(embedding, wall_field.u2, expected_u2, q)

    uncorrected = finite_thickness_jets(embedding, field, thickness, alpha, corrected=False)
    corrected = finite_thickness_jets(embedding, field, thickness, alpha, corrected=True)
    normal_samples = jnp.linspace(-0.5 * thickness, 0.5 * thickness, 5)
    divergence_uncorrected = jax.vmap(lambda r: fermi_divergence(embedding, uncorrected, q, r))(
        normal_samples
    )
    divergence_corrected = jax.vmap(lambda r: fermi_divergence(embedding, corrected, q, r))(
        normal_samples
    )
    half_width = 0.5 * thickness
    lower_normal = corrected.w0(q) - half_width * corrected.w1(q) + half_width**2 * corrected.w2(q)
    upper_normal = corrected.w0(q) + half_width * corrected.w1(q) + half_width**2 * corrected.w2(q)
    return jnp.asarray(
        (
            wall_error,
            u1_error,
            u2_error,
            jnp.sqrt(jnp.mean(divergence_uncorrected**2)),
            jnp.sqrt(jnp.mean(divergence_corrected**2)),
            jnp.maximum(jnp.abs(lower_normal), jnp.abs(upper_normal)),
        )
    )


def run_case(
    case: SurfaceCase,
    count: int,
    thicknesses: Sequence[float],
    alphas: Sequence[float],
) -> list[dict[str, object]]:
    points = sample_points(case, count)
    evaluate = jax.jit(
        jax.vmap(
            lambda q, width, slip: point_metrics(case, q, width, slip),
            in_axes=(0, None, None),
        )
    )
    results = []
    for alpha in alphas:
        profiles = []
        for thickness in thicknesses:
            maxima = jnp.max(evaluate(points, thickness, alpha), axis=0)
            profiles.append(
                {
                    "thickness": thickness,
                    "max_abs_two_wall_residual": float(maxima[0]),
                    "max_rel_u1_vs_asymptotic": float(maxima[1]),
                    "max_rel_u2_vs_asymptotic": float(maxima[2]),
                    "max_rms_divergence_uncorrected": float(maxima[3]),
                    "max_rms_divergence_corrected": float(maxima[4]),
                    "max_abs_normal_wall_trace": float(maxima[5]),
                }
            )
        results.append(
            {
                "surface": case.name,
                "alpha": alpha,
                "sample_count": int(points.shape[0]),
                "source": SOURCE_2026,
                "profiles": profiles,
            }
        )
    return results


def validate_results(results: Sequence[dict[str, object]], tolerance: float) -> None:
    failures = []
    for result in results:
        profiles = result["profiles"]
        assert isinstance(profiles, list)
        for profile in profiles:
            assert isinstance(profile, dict)
            for name in ("max_abs_two_wall_residual", "max_abs_normal_wall_trace"):
                value = float(profile[name])
                if not jnp.isfinite(value) or value > tolerance:
                    failures.append(
                        f"{result['surface']}:alpha={result['alpha']}:"
                        f"epsilon={profile['thickness']}:{name}={value:.3e}"
                    )
            if float(profile["max_rms_divergence_corrected"]) > (
                float(profile["max_rms_divergence_uncorrected"]) + tolerance
            ):
                failures.append(
                    f"{result['surface']}:alpha={result['alpha']}:corrector increased divergence"
                )
        if len(profiles) > 1:
            first, last = profiles[0], profiles[-1]
            for name in ("max_rel_u1_vs_asymptotic", "max_rel_u2_vs_asymptotic"):
                if float(last[name]) > float(first[name]) + tolerance:
                    failures.append(f"{result['surface']}:{name} did not decrease")
    if failures:
        raise AssertionError("Thin-shell validation failed:\n  " + "\n  ".join(failures))


def print_table(results: Sequence[dict[str, object]]) -> None:
    print("finite-thickness two-wall shell fields (positive convention)")
    print(
        "surface                 alpha eps       wall         u1 asym      u2 asym      "
        "div raw      div corrected"
    )
    for result in results:
        profiles = result["profiles"]
        assert isinstance(profiles, list)
        for profile in profiles:
            assert isinstance(profile, dict)
            print(
                f"{result['surface']!s:23s} {float(result['alpha']):.2f}  "
                f"{float(profile['thickness']):.4f}  "
                f"{float(profile['max_abs_two_wall_residual']):.3e}  "
                f"{float(profile['max_rel_u1_vs_asymptotic']):.3e}  "
                f"{float(profile['max_rel_u2_vs_asymptotic']):.3e}  "
                f"{float(profile['max_rms_divergence_uncorrected']):.3e}  "
                f"{float(profile['max_rms_divergence_corrected']):.3e}"
            )


def parse_thicknesses(raw: str) -> tuple[float, ...]:
    values = tuple(float(item) for item in raw.split(","))
    if not values or any(value <= 0.0 for value in values):
        raise argparse.ArgumentTypeError("thicknesses must be positive")
    if any(right >= left for left, right in zip(values, values[1:], strict=False)):
        raise argparse.ArgumentTypeError("thicknesses must be strictly decreasing")
    return values


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--surface", choices=("all", *(case.name for case in surface_cases())), default="all"
    )
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument(
        "--thicknesses",
        type=parse_thicknesses,
        default=parse_thicknesses("0.1,0.05,0.025,0.0125"),
    )
    parser.add_argument("--partial-slip-alpha", type=float, default=0.5)
    parser.add_argument("--tolerance", type=float, default=2.0e-9)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    if args.samples < 2:
        parser.error("--samples must be at least 2")
    if not 0.0 < args.partial_slip_alpha < 1.0:
        parser.error("--partial-slip-alpha must lie strictly between zero and one")
    cases = surface_cases()
    if args.surface != "all":
        cases = tuple(case for case in cases if case.name == args.surface)
    alphas = (0.0, args.partial_slip_alpha, 1.0)
    results = [
        result
        for case in cases
        for result in run_case(case, args.samples, args.thicknesses, alphas)
    ]
    validate_results(results, args.tolerance)
    if args.as_json:
        print(json.dumps(results, indent=2, sort_keys=True))
    else:
        print_table(results)


if __name__ == "__main__":
    main()
