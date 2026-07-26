import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sign and positivity conventions

The project uses the analysis-positive convention for every operator called a
Laplacian: its quadratic form is nonnegative on the fields where the operator
is intended to act.  This module deliberately records positivity relative to
an admissibility predicate, since differential operators are generally
unbounded and have a nontrivial domain.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A linear operator is nonnegative on the fields selected by `Admissible`. -/
def IsNonnegativeOn (A : V →ₗ[ℝ] V) (Admissible : V → Prop) : Prop :=
  ∀ u, Admissible u → 0 ≤ inner ℝ (A u) u

/-- A proof-carrying analysis-positive operator on a specified admissible space. -/
structure PositiveOperatorOn (Admissible : V → Prop) where
  operator : V →ₗ[ℝ] V
  nonnegative : IsNonnegativeOn V operator Admissible

end RiemannianFluids
