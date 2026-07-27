import RiemannianFluids.FunctionSpaces.Constraints
import RiemannianFluids.Operators.Viscosity

/-!
# Stationary Riemannian Stokes equations

Remove time dependence and nonlinear transport from Navier--Stokes. The stationary Stokes problem asks for a velocity `u` and pressure `p` satisfying

    div u = 0,
    ν L u + grad p = f.

The first line is a constraint; the second is a linear momentum balance. The definition below mirrors that conjunction exactly and deliberately
accepts the viscosity operator `L` as an argument. On a curved manifold the choice between rough, Hodge, and deformation viscosity must have been made
or proved irrelevant on the intended class before one can speak of *the* Stokes operator.

This is a project-level strong-form interface, corresponding to `riemannian_fluids/operators/stokes.py`. It is not yet a reproduction of the
exterior-domain theorem registered from Chan--Czubak (2021): there is no domain geometry, boundary trace, weak velocity space, pressure quotient,
inf-sup condition, or existence and uniqueness proof. Keeping this file small makes that boundary unmistakable. It records the equation a future
analytic layer must interpret rather than pretending the interpretation is already present.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/--
Strong stationary Stokes balance plus incompressibility:

`div u = 0`, `ν L u + grad p = f`.

The conjunction mirrors the mathematical definition directly. No proof is attached because this declaration is a predicate describing a candidate
state.
-/
def IsStationaryStokesState
    (calculus : ScalarVectorCalculus V Q)
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    (u : V) (p : Q) (forcing : V) : Prop :=
  IsIncompressible V Q calculus u ∧
    ν • viscosity u + calculus.gradient p = forcing

end RiemannianFluids
