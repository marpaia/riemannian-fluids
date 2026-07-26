"""Explicit numerical-backend capabilities."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class BackendCapabilities:
    local_autodiff: bool = False
    mixed_surface_stokes: bool = False
    normal_fibre_pde: bool = False
    resolved_volume_shell: bool = False
    feec: bool = False
    generalized_spectra: bool = False


JAX_CAPABILITIES = BackendCapabilities(local_autodiff=True)
FENICSX_CAPABILITIES = BackendCapabilities(normal_fibre_pde=True)
SPHERE_SPECTRAL_CAPABILITIES = BackendCapabilities(
    mixed_surface_stokes=True,
    generalized_spectra=True,
)
