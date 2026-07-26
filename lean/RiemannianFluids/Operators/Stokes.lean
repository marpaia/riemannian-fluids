import RiemannianFluids.FunctionSpaces.Constraints
import RiemannianFluids.Operators.Viscosity

/-!
# Stationary Riemannian Stokes equations

This module corresponds to `riemannian_fluids/operators/stokes.py`.  The
stationary linear problem remains separate from Navier--Stokes.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- Strong stationary Stokes balance plus incompressibility. -/
def IsStationaryStokesState
    (calculus : ScalarVectorCalculus V Q)
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    (u : V) (p : Q) (forcing : V) : Prop :=
  IsIncompressible V Q calculus u ∧
    ν • viscosity u + calculus.gradient p = forcing

end RiemannianFluids

