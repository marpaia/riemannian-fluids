import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

/-! ## Construction of the four candidates -/

/-- The reusable operations from which formulas (1.4)--(1.7) are built.  `gradient` constructs
the scaling generator `-1/4 grad(log K)`; the two curried linear maps model the Lie bracket and
the raised Lie derivative of a one-form. -/
structure EllipsoidCandidateConstruction
    (Point Field : Type*) [NormedAddCommGroup Field] [InnerProductSpace ℝ Field] where
  gaussianCurvature : Point → ℝ
  gradient : (Point → ℝ) →ₗ[ℝ] Field
  lieBracket : Field →ₗ[ℝ] Field →ₗ[ℝ] Field
  oneFormLieDerivative : Field →ₗ[ℝ] Field →ₗ[ℝ] Field
  deformationEndpoint : Field →ₗ[ℝ] Field
  hodgeEndpoint : Field →ₗ[ℝ] Field

namespace EllipsoidCandidateConstruction

variable {Point Field : Type*} [NormedAddCommGroup Field] [InnerProductSpace ℝ Field]

/-- The vector field `c^3_13 E_1 = -1/4 grad(log K_E)` in Theorems 1.1 and 1.3. -/
noncomputable def scalingGenerator
    (construction : EllipsoidCandidateConstruction Point Field) : Field :=
  (-1 / 4 : ℝ) • construction.gradient (fun point => Real.log (construction.gaussianCurvature point))

/-- The rank-one map `U ↦ inner(U,A) A` occurring in (1.4) and (1.7). -/
noncomputable def generatorComponentMap (generator : Field) : Field →ₗ[ℝ] Field where
  toFun field := inner ℝ field generator • generator
  map_add' first second := by
    rw [inner_add_left, add_smul]
  map_smul' scalar field := by
    simp [inner_smul_left, mul_smul]

/-- Formula (1.4): scaling-direction Navier candidate without the two divergence constraints. -/
noncomputable def scalingNavierCandidate
    (construction : EllipsoidCandidateConstruction Point Field) : Field →ₗ[ℝ] Field :=
  construction.deformationEndpoint +
    construction.lieBracket construction.scalingGenerator +
    (2 : ℝ) • generatorComponentMap construction.scalingGenerator

/-- Formula (1.5): scaling-direction Hodge candidate without the two divergence constraints. -/
noncomputable def scalingHodgeCandidate
    (construction : EllipsoidCandidateConstruction Point Field) : Field →ₗ[ℝ] Field :=
  construction.hodgeEndpoint +
    construction.oneFormLieDerivative construction.scalingGenerator

/-- Formula (1.6): the simultaneously divergence-free Navier candidate. -/
noncomputable def divergenceFreeNavierCandidate
    (construction : EllipsoidCandidateConstruction Point Field) : Field →ₗ[ℝ] Field :=
  construction.deformationEndpoint +
    construction.lieBracket construction.scalingGenerator

/-- Formula (1.7): the simultaneously divergence-free Hodge candidate. -/
noncomputable def divergenceFreeHodgeCandidate
    (construction : EllipsoidCandidateConstruction Point Field) : Field →ₗ[ℝ] Field :=
  construction.hodgeEndpoint +
    construction.oneFormLieDerivative construction.scalingGenerator -
    (2 : ℝ) • generatorComponentMap construction.scalingGenerator

/-- Package the constructed formulas into the stable CCF25 source signature. -/
noncomputable def sphereCandidateData
    (construction : EllipsoidCandidateConstruction Point Field) :
    SphereCandidateData Point Field where
  gaussianCurvature := construction.gaussianCurvature
  scalingGenerator := construction.scalingGenerator
  scalingNavierCandidate := construction.scalingNavierCandidate
  scalingHodgeCandidate := construction.scalingHodgeCandidate
  divergenceFreeNavierCandidate := construction.divergenceFreeNavierCandidate
  divergenceFreeHodgeCandidate := construction.divergenceFreeHodgeCandidate
  deformationEndpoint := construction.deformationEndpoint
  hodgeEndpoint := construction.hodgeEndpoint

theorem scalingGenerator_eq_zero_of_unit_curvature
    (construction : EllipsoidCandidateConstruction Point Field)
    (unitCurvature : ∀ point, construction.gaussianCurvature point = 1) :
    construction.scalingGenerator = 0 := by
  have hlog : (fun point => Real.log (construction.gaussianCurvature point)) = 0 := by
    funext point
    rw [unitCurvature point, Real.log_one]
    rfl
  rw [scalingGenerator, hlog, map_zero, smul_zero]

theorem generatorComponentMap_zero : generatorComponentMap (0 : Field) = 0 := by
  ext field
  simp [generatorComponentMap]

/-- CCF25 Remark 1.5: after setting `a = 1`, constant unit curvature kills the common scaling
generator and all four constructed candidates reduce to their two named endpoints. -/
theorem four_candidates_sphere
    (construction : EllipsoidCandidateConstruction Point Field) :
    four_candidates_sphere_statement construction.sphereCandidateData := by
  intro unitCurvature
  have hgenerator := construction.scalingGenerator_eq_zero_of_unit_curvature unitCurvature
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hgenerator
  all_goals
    simp [sphereCandidateData, scalingNavierCandidate, scalingHodgeCandidate,
      divergenceFreeNavierCandidate, divergenceFreeHodgeCandidate, hgenerator,
      generatorComponentMap_zero]

end EllipsoidCandidateConstruction

end RiemannianFluids.Literature.CCF25
