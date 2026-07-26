import RiemannianFluids.Tensors.Calculus

/-!
# Incompressibility and pressure constraints

This is the theorem-level counterpart of
`riemannian_fluids/function_spaces/constraints.py`.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- A velocity is incompressible when its divergence vanishes. -/
def IsIncompressible (calculus : ScalarVectorCalculus V Q) (u : V) : Prop :=
  calculus.divergence u = 0

/-- Scalar gradients perform no work on incompressible velocities. -/
theorem pressure_work_eq_zero (calculus : ScalarVectorCalculus V Q)
    {u : V} (hu : IsIncompressible V Q calculus u) (p : Q) :
    inner ℝ (calculus.gradient p) u = 0 := by
  rw [calculus.gradient_divergence_duality]
  change calculus.divergence u = 0 at hu
  simp [hu]

end RiemannianFluids

