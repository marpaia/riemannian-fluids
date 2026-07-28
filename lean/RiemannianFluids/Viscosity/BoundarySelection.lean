import RiemannianFluids.Geometry.Submanifolds
import RiemannianFluids.Operators.Restriction
import RiemannianFluids.Operators.SubmanifoldConstraints

/-!
# Ambient restriction and boundary-selected surface viscosity

Embedding a manifold in an ambient space does not by itself determine an intrinsic fluid
operator.  One must choose an extension off the surface, apply an ambient operator, project
back to the tangent bundle, and prove that the answer is independent of the extension on the
admissible class.  `Operators.Restriction` exposes those obligations instead of hiding them in
notation.

A second idea from the thin-domain literature is more physical: different wall laws can
select different endpoints of a family of effective surface operators.  Abstracting away the
derivation, the local family has a deformation term, a Ricci correction linear in the wall
parameter, and an extrinsic shape-square correction that vanishes at both endpoints.

The elementary endpoint theorems below are intentionally modest.  They check the algebra and
the coefficients.  They are not a thin-shell convergence theorem, and they do not identify
the signs here with a different convention without an explicit comparison hypothesis.
-/

namespace RiemannianFluids

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The algebraic family produced by a boundary-selection calculation. -/
noncomputable def boundarySelectedOperator
    (deformation ricci shapeSquare : V →ₗ[ℝ] V) (a : ℝ) : V →ₗ[ℝ] V :=
  deformation - (2 * a) • ricci - (4 * a * (1 - a)) • shapeSquare

/-- The zero endpoint is the deformation operator. -/
@[simp]
theorem boundarySelectedOperator_zero
    (deformation ricci shapeSquare : V →ₗ[ℝ] V) :
    boundarySelectedOperator deformation ricci shapeSquare 0 = deformation := by
  ext field
  simp [boundarySelectedOperator]

/-- At the unit endpoint only the Ricci correction remains. -/
@[simp]
theorem boundarySelectedOperator_one
    (deformation ricci shapeSquare : V →ₗ[ℝ] V) :
    boundarySelectedOperator deformation ricci shapeSquare 1 =
      deformation - (2 : ℝ) • ricci := by
  ext field
  simp [boundarySelectedOperator]

/-- The extrinsic shape-square coefficient vanishes at either wall-law endpoint. -/
theorem shapeSquareCoefficient_eq_zero_at_endpoint
    {a : ℝ} (ha : a = 0 ∨ a = 1) : 4 * a * (1 - a) = 0 := by
  rcases ha with rfl | rfl <;> ring

end RiemannianFluids
