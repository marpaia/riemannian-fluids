from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.operators import MixedStokesSystem
from riemannian_fluids.solvers import (
    discrete_energy,
    generalized_eigenpairs,
    implicit_euler_step,
    newton_solve,
    solve_mixed_stokes,
)


def test_mixed_stokes_enforces_constraint_and_pressure_gauge() -> None:
    system = MixedStokesSystem(
        jnp.eye(2),
        jnp.asarray(((1.0, 1.0),)),
        jnp.asarray((1.0, -1.0)),
        jnp.zeros((1,)),
    )
    solution = solve_mixed_stokes(system)
    assert solution.residual_norm < 1.0e-12
    assert abs(solution.pressure_mean) < 1.0e-12
    assert jnp.allclose(solution.velocity, jnp.asarray((1.0, -1.0)))


def test_newton_and_implicit_euler_reference_solvers() -> None:
    result = newton_solve(lambda x: x**2 - 2.0, jnp.asarray((1.0,)))
    assert result.converged
    assert jnp.allclose(result.value, jnp.sqrt(2.0), atol=1.0e-10)

    previous = jnp.asarray((1.0,))
    step = implicit_euler_step(jnp.eye(1), lambda x: x, previous, 0.1)
    assert step.nonlinear_result.converged
    assert jnp.allclose(step.current, jnp.asarray((1.0 / 1.1,)))
    assert discrete_energy(jnp.eye(1), step.current) < discrete_energy(jnp.eye(1), previous)


def test_generalized_eigenproblem_uses_mass_matrix() -> None:
    stiffness = jnp.diag(jnp.asarray((2.0, 12.0, 0.0)))
    mass = jnp.diag(jnp.asarray((1.0, 3.0, 2.0)))
    spectrum = generalized_eigenpairs(
        stiffness,
        mass,
        count=2,
        nullspace_tolerance=1.0e-12,
    )
    assert jnp.allclose(spectrum.eigenvalues, jnp.asarray((2.0, 4.0)))
    assert jnp.all(spectrum.residual_norms < 1.0e-12)
