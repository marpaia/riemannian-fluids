"""Reference stationary, nonlinear, and transient solvers."""

from riemannian_fluids.solvers.mixed import MixedSolution, solve_mixed_stokes
from riemannian_fluids.solvers.nonlinear import (
    NewtonResult,
    newton_solve,
    solve_semidiscrete_flow,
    solve_stationary_flow,
)
from riemannian_fluids.solvers.spectral import GeneralizedEigenpairs, generalized_eigenpairs
from riemannian_fluids.solvers.transient import (
    FlowTrajectory,
    ImplicitEulerStep,
    discrete_energy,
    implicit_euler_step,
    integrate_incompressible_flow,
)

__all__ = (
    "ImplicitEulerStep",
    "GeneralizedEigenpairs",
    "FlowTrajectory",
    "MixedSolution",
    "NewtonResult",
    "discrete_energy",
    "implicit_euler_step",
    "integrate_incompressible_flow",
    "generalized_eigenpairs",
    "newton_solve",
    "solve_mixed_stokes",
    "solve_semidiscrete_flow",
    "solve_stationary_flow",
)
