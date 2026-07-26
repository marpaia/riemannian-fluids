from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.discretization import OneFormFamily, SphereStokesBasis
from riemannian_fluids.operators import ViscosityModel
from riemannian_fluids.solvers import solve_mixed_stokes


def _mode_index(basis: SphereStokesBasis, degree: int, order: int, family: OneFormFamily) -> int:
    return basis.velocity_modes.index(type(basis.velocity_modes[0])(degree, order, family))


def test_global_sphere_stokes_solves_divergence_free_mode() -> None:
    basis = SphereStokesBasis(2)
    index = _mode_index(basis, 2, 0, OneFormFamily.COEXACT)
    force = jnp.zeros((len(basis.velocity_modes),)).at[index].set(1.0)
    solution = solve_mixed_stokes(basis.stokes_system(force, model=ViscosityModel.DEFORMATION))
    assert solution.residual_norm < 1.0e-10
    assert jnp.isclose(solution.velocity[index], 0.25)
    assert jnp.linalg.norm(basis.divergence_matrix() @ solution.velocity) < 1.0e-12


def test_global_sphere_stokes_recovers_pressure_and_killing_modes() -> None:
    basis = SphereStokesBasis(2)
    exact_index = _mode_index(basis, 2, 1, OneFormFamily.EXACT)
    scalar_index = basis.scalar_modes.index((2, 1))
    force = jnp.zeros((len(basis.velocity_modes),)).at[exact_index].set(1.0)
    solution = solve_mixed_stokes(basis.stokes_system(force, model=ViscosityModel.DEFORMATION))
    assert solution.residual_norm < 1.0e-10
    assert jnp.linalg.norm(solution.velocity) < 1.0e-10
    assert jnp.isclose(solution.pressure[1 + scalar_index], -1.0 / jnp.sqrt(6.0))
    assert len(basis.killing_mode_indices()) == 3
