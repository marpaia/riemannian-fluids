"""Resolve Navier, Hodge, and intermediate wall-selected spherical modes."""

from __future__ import annotations

import argparse
import json
import math
from collections.abc import Sequence

from mpi4py import MPI

from riemannian_fluids.discretization.fenicsx_shell import (
    solve_wall_selected_spherical_shell,
    wall_selection_diagnostics_dict,
)
from riemannian_fluids.shells import WallLaw
from riemannian_fluids.validation.refinement import fitted_order, monotone_refinement, observed_orders

Configuration = tuple[float, int, int, WallLaw, float]


def _solve(configuration: Configuration) -> dict[str, float | int | str]:
    thickness, refinement, normal_layers, wall_law, alpha = configuration
    return wall_selection_diagnostics_dict(
        solve_wall_selected_spherical_shell(
            refinement=refinement,
            normal_layers=normal_layers,
            thickness=thickness,
            wall_law=wall_law,
            alpha=alpha,
        )
    )


def run_study() -> dict[str, object]:
    cache: dict[Configuration, dict[str, float | int | str]] = {}

    def solve(configuration: Configuration) -> dict[str, float | int | str]:
        if configuration not in cache:
            cache[configuration] = _solve(configuration)
        return cache[configuration]

    family_configurations = (
        (0.2, 2, 8, WallLaw.NAVIER, 0.0),
        (0.2, 2, 8, WallLaw.PARTIAL_SLIP, 0.25),
        (0.2, 2, 8, WallLaw.PARTIAL_SLIP, 0.5),
        (0.2, 2, 8, WallLaw.PARTIAL_SLIP, 0.75),
        (0.2, 2, 8, WallLaw.HODGE, 1.0),
    )
    mesh_profiles = {}
    coupled_profiles = {}
    coupled_orders = {}
    for wall_law, alpha in ((WallLaw.PARTIAL_SLIP, 0.5), (WallLaw.HODGE, 1.0)):
        key = wall_law.value
        mesh_configurations = tuple((0.2, refinement, 8, wall_law, alpha) for refinement in (0, 1, 2, 3))
        mesh_profiles[key] = [solve(configuration) for configuration in mesh_configurations]
        coupled_configurations = (
            (0.2, 2, 8, wall_law, alpha),
            (0.1, 3, 8, wall_law, alpha),
            (0.05, 4, 8, wall_law, alpha),
        )
        coupled_profiles[key] = [solve(configuration) for configuration in coupled_configurations]
        thicknesses = tuple(configuration[0] for configuration in coupled_configurations)
        errors = tuple(float(profile["relative_surface_coefficient_error"]) for profile in coupled_profiles[key])
        coupled_orders[key] = {
            "pairwise": observed_orders(thicknesses, errors),
            "fitted": fitted_order(thicknesses, errors),
        }
    return {
        "evidence_class": "separated resolved-shell discretization and coupled thin-limit study",
        "scope": "one reaction-shifted degree-one rotational resolvent on concentric spherical shells",
        "non_claim": "this is not a Mosco, strong-resolvent, semigroup, or full-spectrum proof",
        "wall_family": [solve(configuration) for configuration in family_configurations],
        "fixed_thickness_mesh_limits": mesh_profiles,
        "coupled_h_over_epsilon_limits": coupled_profiles,
        "coupled_observed_orders": coupled_orders,
    }


def validate_results(result: dict[str, object]) -> None:
    family = result["wall_family"]
    mesh_limits = result["fixed_thickness_mesh_limits"]
    coupled_limits = result["coupled_h_over_epsilon_limits"]
    coupled_orders = result["coupled_observed_orders"]
    assert isinstance(family, list)
    assert isinstance(mesh_limits, dict)
    assert isinstance(coupled_limits, dict)
    assert isinstance(coupled_orders, dict)
    failures = []
    for profile in family:
        for name in (
            "averaged_shell_coefficient",
            "relative_surface_coefficient_error",
            "divergence_l2",
            "normal_wall_trace_l2",
            "wall_law_residual_l2",
            "pressure_mean",
        ):
            if not math.isfinite(float(profile[name])):
                failures.append(f"nonfinite {name} for alpha={profile['alpha']}")
        if float(profile["relative_surface_coefficient_error"]) >= 0.07:
            failures.append(f"surface coefficient error exceeded 7% for alpha={profile['alpha']}")
    navier = family[0]
    if abs(float(navier["averaged_shell_coefficient"]) - 1.0) >= 1.0e-9:
        failures.append("the Navier rotational Killing response was not one")
    for key in (WallLaw.PARTIAL_SLIP.value, WallLaw.HODGE.value):
        mesh_profiles = mesh_limits[key]
        thin_profiles = coupled_limits[key]
        errors = tuple(float(profile["relative_surface_coefficient_error"]) for profile in mesh_profiles)
        if not monotone_refinement(errors):
            failures.append(f"{key} coefficient error did not decrease at fixed thickness")
        if errors[-1] >= 0.035:
            failures.append(f"{key} fine-mesh coefficient error exceeded 3.5%")
        fine = mesh_profiles[-1]
        if float(fine["divergence_l2"]) >= 5.0e-3:
            failures.append(f"{key} fine-mesh divergence exceeded 5e-3")
        if float(fine["normal_wall_trace_l2"]) >= 1.0e-3:
            failures.append(f"{key} fine-mesh normal trace exceeded 1e-3")
        if float(fine["wall_law_residual_l2"]) >= 0.06:
            failures.append(f"{key} fine-mesh wall residual exceeded 0.06")
        ratios = tuple(float(profile["h_over_thickness"]) for profile in thin_profiles)
        if any(abs(ratio / ratios[0] - 1.0) >= 0.02 for ratio in ratios[1:]):
            failures.append(f"{key} coupled sequence did not hold h/epsilon fixed")
        thin_errors = tuple(float(profile["relative_surface_coefficient_error"]) for profile in thin_profiles)
        if any(right >= 0.3 * left for left, right in zip(thin_errors, thin_errors[1:], strict=False)):
            failures.append(f"{key} coupled error did not decrease by the expected factor")
        orders = coupled_orders[key]
        assert isinstance(orders, dict)
        if float(orders["fitted"]) <= 1.7:
            failures.append(f"{key} coupled fitted order was not near quadratic")
    if failures:
        raise AssertionError("Wall-selection validation failed:\n  " + "\n  ".join(failures))


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    result = run_study()
    validate_results(result)
    if MPI.COMM_WORLD.rank != 0:
        return
    if args.as_json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return
    print("resolved Navier--Hodge wall selection on spherical shells")
    print("law/alpha        eigenvalue expected    shell       relative error")
    family = result["wall_family"]
    assert isinstance(family, list)
    for profile in family:
        label = f"{profile['wall_law']}:{float(profile['alpha']):.2f}"
        print(
            f"{label:16s} {float(profile['surface_eigenvalue']):.3f}      "
            f"{float(profile['expected_surface_coefficient']):.6f}  "
            f"{float(profile['averaged_shell_coefficient']):.6f}  "
            f"{float(profile['relative_surface_coefficient_error']):.3e}"
        )
    orders = result["coupled_observed_orders"]
    assert isinstance(orders, dict)
    for key, value in orders.items():
        assert isinstance(value, dict)
        pairwise = ", ".join(f"{float(order):.2f}" for order in value["pairwise"])
        print(f"{key} coupled orders over thickness 0.2/0.1/0.05: pairwise [{pairwise}] fitted {float(value['fitted']):.2f}")


if __name__ == "__main__":
    main()
