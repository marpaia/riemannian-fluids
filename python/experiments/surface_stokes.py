"""Compare native surface finite elements with a spherical Killing mode."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence

import jax.numpy as jnp
from mpi4py import MPI

from riemannian_fluids.discretization import SphereStokesBasis
from riemannian_fluids.discretization.fenicsx_surface import solve_sphere_surface_stokes
from riemannian_fluids.operators import ViscosityModel
from riemannian_fluids.solvers import solve_mixed_stokes
from riemannian_fluids.validation.refinement import monotone_refinement, observed_orders


def parse_refinements(raw: str) -> tuple[int, ...]:
    values = tuple(int(item) for item in raw.split(","))
    if len(values) < 2 or any(value < 0 for value in values):
        raise argparse.ArgumentTypeError("provide at least two nonnegative refinement levels")
    if any(right <= left for left, right in zip(values, values[1:], strict=False)):
        raise argparse.ArgumentTypeError("refinements must be strictly increasing")
    return values


def run_study(refinements: Sequence[int]) -> dict[str, object]:
    basis = SphereStokesBasis(1)
    killing_indices = basis.killing_mode_indices()
    killing_eigenvalues = tuple(float(basis.viscosity_eigenvalues(ViscosityModel.DEFORMATION)[index]) for index in killing_indices)
    reference_force = jnp.zeros((len(basis.velocity_modes),), dtype=jnp.float64).at[killing_indices[0]].set(1.0)
    spectral_solution = solve_mixed_stokes(
        basis.stokes_system(
            reference_force,
            model=ViscosityModel.DEFORMATION,
            reaction=1.0,
        )
    )
    profiles = [solve_sphere_surface_stokes(refinement=refinement).as_dict() for refinement in refinements]
    errors = tuple(float(profile["spectral_reference_error"]) for profile in profiles)
    scales = tuple(2.0 ** (-refinement) for refinement in refinements)
    return {
        "evidence_class": "native mixed surface finite-element refinement and spectral comparison",
        "geometry": "unit sphere approximated by normalized octahedral refinements",
        "spectral_mode": "degree-one coexact rotational Killing field",
        "spectral_deformation_eigenvalues": killing_eigenvalues,
        "spectral_resolvent_coefficient": float(spectral_solution.velocity[killing_indices[0]]),
        "spectral_resolvent_residual": spectral_solution.residual_norm,
        "profiles": profiles,
        "observed_orders": observed_orders(scales, errors),
    }


def validate_results(result: dict[str, object]) -> None:
    profiles = result["profiles"]
    eigenvalues = result["spectral_deformation_eigenvalues"]
    assert isinstance(profiles, list)
    errors = tuple(float(profile["spectral_reference_error"]) for profile in profiles)
    failures = []
    if any(abs(float(value)) > 1.0e-12 for value in eigenvalues):
        failures.append("spherical reference did not identify the deformation Killing kernel")
    if abs(float(result["spectral_resolvent_coefficient"]) - 1.0) > 1.0e-12:
        failures.append("reaction-shifted spherical resolvent did not preserve the Killing coefficient")
    if float(result["spectral_resolvent_residual"]) > 1.0e-12:
        failures.append("reaction-shifted spherical resolvent residual exceeded tolerance")
    if not monotone_refinement(errors):
        failures.append("surface velocity error did not decrease monotonically")
    if errors[-1] >= 0.25 * errors[0]:
        failures.append("surface velocity error did not decrease by a factor of four")
    if float(profiles[-1]["divergence_l2"]) >= 0.04:
        failures.append("fine-mesh divergence exceeded 0.04")
    if float(profiles[-1]["tangency_l2"]) >= 0.13:
        failures.append("fine-mesh normal leakage exceeded 0.13")
    if any(abs(float(profile["pressure_mean"])) >= 1.0e-10 for profile in profiles):
        failures.append("pressure gauge residual exceeded tolerance")
    if failures:
        raise AssertionError("Surface Stokes validation failed:\n  " + "\n  ".join(failures))


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refinements", type=parse_refinements, default=parse_refinements("0,1,2,3"))
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    result = run_study(args.refinements)
    validate_results(result)
    if MPI.COMM_WORLD.rank != 0:
        return
    if args.as_json:
        print(json.dumps(result, indent=2, sort_keys=True))
        return
    print("native mixed surface Stokes on the unit sphere")
    print("level cells    velocity error divergence    normal leakage")
    profiles = result["profiles"]
    assert isinstance(profiles, list)
    for profile in profiles:
        print(
            f"{int(profile['refinement']):<5d} {int(profile['cells']):<8d} "
            f"{float(profile['relative_velocity_l2_error']):.3e}      "
            f"{float(profile['divergence_l2']):.3e}      "
            f"{float(profile['tangency_l2']):.3e}"
        )


if __name__ == "__main__":
    main()
