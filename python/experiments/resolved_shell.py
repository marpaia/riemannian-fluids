"""Run a resolved three-dimensional spherical-shell refinement study."""

from __future__ import annotations

import argparse
import json
import math
from collections.abc import Sequence

from mpi4py import MPI

from riemannian_fluids.discretization.fenicsx_shell import (
    diagnostics_dict,
    solve_resolved_spherical_shell,
)
from riemannian_fluids.validation.refinement import monotone_refinement

ShellConfiguration = tuple[float, int, int]


def parse_refinements(raw: str) -> tuple[int, ...]:
    values = tuple(int(item) for item in raw.split(","))
    if len(values) < 2 or any(value < 0 for value in values):
        raise argparse.ArgumentTypeError("provide at least two nonnegative refinement levels")
    if any(right <= left for left, right in zip(values, values[1:], strict=False)):
        raise argparse.ArgumentTypeError("refinements must be strictly increasing")
    return values


def parse_thickness_configurations(raw: str) -> tuple[ShellConfiguration, ...]:
    try:
        configurations = tuple(
            (float(width), int(refinement), int(layers))
            for item in raw.split(",")
            for width, refinement, layers in (item.split(":"),)
        )
    except ValueError as error:
        raise argparse.ArgumentTypeError("use thickness:refinement:normal-layers entries") from error
    if len(configurations) < 2:
        raise argparse.ArgumentTypeError("provide at least two thickness configurations")
    if any(width <= 0.0 or refinement < 0 or layers < 2 for width, refinement, layers in configurations):
        raise argparse.ArgumentTypeError("widths must be positive, refinements nonnegative, and layers at least two")
    if any(right[0] >= left[0] for left, right in zip(configurations, configurations[1:], strict=False)):
        raise argparse.ArgumentTypeError("thicknesses must be strictly decreasing")
    return configurations


def _solve(configuration: ShellConfiguration) -> dict[str, float | int | str]:
    thickness, refinement, normal_layers = configuration
    return diagnostics_dict(
        solve_resolved_spherical_shell(
            refinement=refinement,
            normal_layers=normal_layers,
            thickness=thickness,
        )
    )


def run_study(
    refinements: Sequence[int],
    thickness_configurations: Sequence[ShellConfiguration],
    *,
    mesh_thickness: float = 0.4,
) -> dict[str, object]:
    cache: dict[ShellConfiguration, dict[str, float | int | str]] = {}

    def solve(configuration: ShellConfiguration) -> dict[str, float | int | str]:
        if configuration not in cache:
            cache[configuration] = _solve(configuration)
        return cache[configuration]

    mesh_configurations = tuple((mesh_thickness, refinement, 2 ** (refinement + 1)) for refinement in refinements)
    mesh_profiles = [solve(configuration) for configuration in mesh_configurations]
    thickness_profiles = [solve(configuration) for configuration in thickness_configurations]
    resolution_warnings = []
    for coarse, thin in zip(thickness_profiles, thickness_profiles[1:], strict=False):
        ratio_growth = float(thin["h_over_thickness"]) / float(coarse["h_over_thickness"])
        error_growth = float(thin["relative_velocity_l2_error"]) / float(coarse["relative_velocity_l2_error"])
        if ratio_growth > 1.5 and error_growth > 1.0:
            resolution_warnings.append(
                {
                    "thickness": thin["thickness"],
                    "h_over_thickness": thin["h_over_thickness"],
                    "velocity_error_growth": error_growth,
                    "meaning": "the thinner shell is not tangentially resolved at comparable h/epsilon",
                }
            )
    return {
        "evidence_class": "resolved three-dimensional volume-shell finite-element study",
        "geometry": "tetrahedral spherical shell with tagged inner and outer no-slip walls",
        "manufactured_field": "divergence-free radially modulated rotational field",
        "mesh_profiles": mesh_profiles,
        "thickness_profiles": thickness_profiles,
        "resolution_warnings": resolution_warnings,
    }


def validate_results(result: dict[str, object]) -> None:
    mesh_profiles = result["mesh_profiles"]
    thickness_profiles = result["thickness_profiles"]
    assert isinstance(mesh_profiles, list)
    assert isinstance(thickness_profiles, list)
    failures = []
    for profile in (*mesh_profiles, *thickness_profiles):
        for name in (
            "divergence_l2",
            "wall_residual_l2",
            "pressure_mean",
            "averaged_surface_error_l2",
            "relative_velocity_l2_error",
            "relative_pressure_l2_error",
        ):
            if not math.isfinite(float(profile[name])):
                failures.append(f"nonfinite {name} for epsilon={profile['thickness']}")
        if abs(float(profile["pressure_mean"])) >= 1.0e-2:
            failures.append(f"pressure gauge diagnostic exceeded 1e-2 for epsilon={profile['thickness']}")
        if float(profile["relative_pressure_l2_error"]) >= 5.0e-2:
            failures.append(f"relative pressure error exceeded 0.05 for epsilon={profile['thickness']}")
    velocity_errors = tuple(float(profile["relative_velocity_l2_error"]) for profile in mesh_profiles)
    wall_residuals = tuple(float(profile["wall_residual_l2"]) for profile in mesh_profiles)
    average_errors = tuple(float(profile["averaged_surface_error_l2"]) for profile in mesh_profiles)
    if not monotone_refinement(velocity_errors):
        failures.append("resolved-shell velocity error did not decrease under mesh refinement")
    if not monotone_refinement(wall_residuals):
        failures.append("curved-wall trace mismatch did not decrease under mesh refinement")
    if not monotone_refinement(average_errors):
        failures.append("transverse-average error did not decrease under mesh refinement")
    if velocity_errors[-1] >= 0.5 * velocity_errors[0]:
        failures.append("resolved-shell velocity error did not decrease by a factor of two")
    if failures:
        raise AssertionError("Resolved-shell validation failed:\n  " + "\n  ".join(failures))


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refinements", type=parse_refinements, default=parse_refinements("0,1,2"))
    parser.add_argument("--mesh-thickness", type=float, default=0.4)
    parser.add_argument(
        "--thickness-configurations",
        type=parse_thickness_configurations,
        default=parse_thickness_configurations("0.4:1:4,0.2:2:8,0.1:2:12"),
    )
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    if args.mesh_thickness <= 0.0:
        parser.error("mesh thickness must be positive")
    result = run_study(
        args.refinements,
        args.thickness_configurations,
        mesh_thickness=args.mesh_thickness,
    )
    validate_results(result)
    if MPI.COMM_WORLD.rank != 0:
        return
    if args.as_json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return
    print("resolved three-dimensional spherical-shell Stokes")
    print("mesh refinement: level cells    h/epsilon velocity error wall trace    average error")
    mesh_profiles = result["mesh_profiles"]
    assert isinstance(mesh_profiles, list)
    for profile in mesh_profiles:
        print(
            f"{int(profile['refinement']):<16d} {int(profile['cells']):<8d} "
            f"{float(profile['h_over_thickness']):.3f}     "
            f"{float(profile['relative_velocity_l2_error']):.3e}      "
            f"{float(profile['wall_residual_l2']):.3e}    "
            f"{float(profile['averaged_surface_error_l2']):.3e}"
        )
    warnings = result["resolution_warnings"]
    assert isinstance(warnings, list)
    for warning in warnings:
        print(
            f"resolution warning: epsilon={float(warning['thickness']):.3f}, "
            f"h/epsilon={float(warning['h_over_thickness']):.3f}: {warning['meaning']}"
        )


if __name__ == "__main__":
    main()
