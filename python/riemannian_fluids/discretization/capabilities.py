"""Explicit numerical-backend capabilities."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class BackendCapabilities:
    local_autodiff: bool = False
    mixed_surface_stokes: bool = False
    stationary_navier_stokes: bool = False
    transient_navier_stokes: bool = False
    normal_fibre_pde: bool = False
    resolved_volume_shell: bool = False
    wall_selected_volume_shell: bool = False
    feec: bool = False
    generalized_spectra: bool = False


JAX_CAPABILITIES = BackendCapabilities(
    local_autodiff=True,
    stationary_navier_stokes=True,
    transient_navier_stokes=True,
)
FENICSX_CAPABILITIES = BackendCapabilities(
    mixed_surface_stokes=True,
    normal_fibre_pde=True,
    resolved_volume_shell=True,
    wall_selected_volume_shell=True,
)
SPHERE_SPECTRAL_CAPABILITIES = BackendCapabilities(
    mixed_surface_stokes=True,
    generalized_spectra=True,
)
