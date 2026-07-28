from __future__ import annotations

from riemannian_fluids.discretization import (
    FENICSX_CAPABILITIES,
    JAX_CAPABILITIES,
    SPHERE_SPECTRAL_CAPABILITIES,
)


def test_backend_capabilities_match_implemented_boundaries() -> None:
    assert JAX_CAPABILITIES.local_autodiff
    assert JAX_CAPABILITIES.stationary_navier_stokes
    assert JAX_CAPABILITIES.transient_navier_stokes
    assert not JAX_CAPABILITIES.mixed_surface_stokes

    assert FENICSX_CAPABILITIES.mixed_surface_stokes
    assert FENICSX_CAPABILITIES.resolved_volume_shell
    assert FENICSX_CAPABILITIES.wall_selected_volume_shell
    assert not FENICSX_CAPABILITIES.stationary_navier_stokes

    assert SPHERE_SPECTRAL_CAPABILITIES.mixed_surface_stokes
    assert SPHERE_SPECTRAL_CAPABILITIES.generalized_spectra
    assert not SPHERE_SPECTRAL_CAPABILITIES.resolved_volume_shell
