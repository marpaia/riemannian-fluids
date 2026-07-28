from __future__ import annotations

from experiments.surface_stokes import run_study, validate_results


def test_surface_stokes_converges_to_spherical_killing_mode() -> None:
    result = run_study((0, 1, 2, 3))
    validate_results(result)
