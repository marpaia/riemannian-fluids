import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Abstract energy interfaces

These structures isolate algebraic consequences of integration by parts,
incompressibility, and advection cancellation.  They are useful downstream,
but they do not construct Riemannian differential operators or function
spaces.  The geometric development must eventually instantiate them.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/--
An abstract divergence/gradient pair with the duality required by the energy
method.  The identity includes all domain and boundary hypotheses.
-/
structure ScalarVectorCalculus where
  divergence : V →ₗ[ℝ] Q
  gradient : Q →ₗ[ℝ] V
  gradient_divergence_duality : ∀ p u,
    inner ℝ (gradient p) u = -inner ℝ p (divergence u)

/-- Abstract advection equipped with its incompressible energy cancellation. -/
structure EnergyConservingAdvection (incompressible : V → Prop) where
  advect : V → V → V
  energy_cancel : ∀ u, incompressible u → inner ℝ (advect u u) u = 0

end RiemannianFluids
