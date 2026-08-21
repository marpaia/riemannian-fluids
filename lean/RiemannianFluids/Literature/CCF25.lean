import RiemannianFluids.Operators.Viscosity

/-!
# CCF25: sphere specialization of the four ellipsoid candidates

The thin-shell derivations in CCF25 are explicitly heuristic.  The source-proof node retained by
the corpus is only Remark 1.5's algebraic specialization: constant Gaussian curvature makes the
scaling generator `-1/4 grad(log K)` vanish, and formulas (1.4)--(1.7) reduce to their two named
endpoints.
-/

namespace RiemannianFluids.Literature.CCF25

/-- Observable curvature, scaling generator, four candidate operators, and two endpoints. -/
structure SphereCandidateData (Point Field : Type*) [AddCommGroup Field] [Module ℝ Field] where
  gaussianCurvature : Point → ℝ
  scalingGenerator : Field
  scalingNavierCandidate : Field →ₗ[ℝ] Field
  scalingHodgeCandidate : Field →ₗ[ℝ] Field
  divergenceFreeNavierCandidate : Field →ₗ[ℝ] Field
  divergenceFreeHodgeCandidate : Field →ₗ[ℝ] Field
  deformationEndpoint : Field →ₗ[ℝ] Field
  hodgeEndpoint : Field →ₗ[ℝ] Field

/-- Source signature for CCF25 Remark 1.5.  The constant unit curvature equation exposes the
paper's `a = 1` sphere specialization; all four operator equalities and the vanishing generator
are conclusions. -/
def four_candidates_sphere_statement
    {Point Field : Type*} [AddCommGroup Field] [Module ℝ Field]
    (data : SphereCandidateData Point Field) : Prop :=
  (∀ point, data.gaussianCurvature point = 1) →
    data.scalingGenerator = 0 ∧
      data.scalingNavierCandidate = data.deformationEndpoint ∧
      data.divergenceFreeNavierCandidate = data.deformationEndpoint ∧
      data.scalingHodgeCandidate = data.hodgeEndpoint ∧
      data.divergenceFreeHodgeCandidate = data.hodgeEndpoint

end RiemannianFluids.Literature.CCF25
