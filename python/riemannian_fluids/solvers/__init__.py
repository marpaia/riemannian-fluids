"""Reference stationary, nonlinear, and transient solvers."""

from riemannian_fluids.solvers.mixed import MixedSolution, solve_mixed_stokes
from riemannian_fluids.solvers.nonlinear import NewtonResult, newton_solve
from riemannian_fluids.solvers.spectral import GeneralizedEigenpairs, generalized_eigenpairs
from riemannian_fluids.solvers.transient import (
    ImplicitEulerStep,
    discrete_energy,
    implicit_euler_step,
)

__all__ = (
    "ImplicitEulerStep",
    "GeneralizedEigenpairs",
    "MixedSolution",
    "NewtonResult",
    "discrete_energy",
    "implicit_euler_step",
    "generalized_eigenpairs",
    "newton_solve",
    "solve_mixed_stokes",
)
