import RiemannianFluids.PDE.LerayHopf
import RiemannianFluids.ProofStatus

/-!
# CC13 hyperbolic nonuniqueness proof graph

This module follows Chan--Czubak, arXiv:1006.2819v1, Sections 3--6.  It retains the
constant-curvature route to Theorem 1.2: boundary-at-infinity harmonic extension,
Proposition 3.1 and Corollary 3.3, the covering and integrability estimates of Section 4,
the deformation-energy identities of Section 5, and equations (6.5)--(6.6).
-/

namespace RiemannianFluids

/-- Geometry, harmonic seed, estimates, and parametrized solution observables used by CC13. -/
structure CC13Data (Initial Solution Potential : Type*) where
  isHyperbolicPlane : ℝ → Prop
  scalarCurvature : ℝ → ℝ
  lerayHopf : ℝ → LerayHopfFramework Initial Solution
  seedPotential : ℝ → Potential
  hasDeformationDefinition2_1 : Prop
  hasDistanceFunctionIdentities : ℝ → Prop
  hasHyperbolicTriangleComparison : ℝ → Prop
  hasCaccioppoliEstimate : ℝ → Prop
  hasChengYauGradientEstimate : ℝ → Prop
  hasBochnerFormula2_20 : ℝ → Prop
  hasJacobiFieldComparison : ℝ → Prop
  isBoundedNonconstantHarmonic : ℝ → Potential → Prop
  hasExponentialGradientDecay : ℝ → Potential → Prop
  harmonicGradientHasFiniteEnergy : ℝ → Potential → Prop
  hessianHasFiniteEnergy : ℝ → Potential → Prop
  admitsUniformGeodesicCover : ℝ → Prop
  gradientEnergyDerivativeIsL1 : ℝ → Potential → Prop
  deformationControlledByCovariantDerivative : ℝ → Potential → Prop
  hasBochnerDissipationIdentity : ℝ → Potential → Prop
  hasExactHyperbolicDissipationIdentity : ℝ → Potential → Prop
  hasConvectiveGradientIdentity : ℝ → Potential → Prop
  amplitudeSolvesEquation6_6 : ℝ → ℝ → Prop
  initialFromPotential : ℝ → Potential → Initial
  solutionFromPotential : ℝ → Potential → ℝ → Solution

/-! ## Section 2 preliminaries used by the proof -/

/-- CC13 Definition 2.1: the symmetric covariant derivative defining `Def`. -/
def cc13Definition2_1Deformation
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential) : Prop :=
  data.hasDeformationDefinition2_1

/-- CC13 Lemma 2.2: distance-function smoothness, unit gradient, and Laplacian comparison. -/
@[proof_obligation]
theorem cc13_lemma_2_2_distance_function
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.hasDistanceFunctionIdentities a := by
  sorry

/-- CC13 Lemma 2.3: comparison of distant points on a common geodesic sphere. -/
@[proof_obligation]
theorem cc13_lemma_2_3_triangle_comparison
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.hasHyperbolicTriangleComparison a := by
  sorry

/-- CC13 Lemma 2.4: the local Caccioppoli estimate for nonnegative subharmonic functions. -/
@[proof_obligation]
theorem cc13_lemma_2_4_caccioppoli
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.hasCaccioppoliEstimate a := by
  sorry

/-- CC13 Theorem 2.5: the Cheng--Yau gradient estimate. -/
@[proof_obligation]
theorem cc13_theorem_2_5_gradient_estimate
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.hasChengYauGradientEstimate a := by
  sorry

/-- CC13 Lemma 2.6, equation (2.20): the Bochner formula for `Delta |grad F|²`. -/
@[proof_obligation]
theorem cc13_lemma_2_6_bochner_formula
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.hasBochnerFormula2_20 a := by
  sorry

/-- CC13 Theorem 2.7: Jacobi-field comparison and exponential volume growth. -/
@[proof_obligation]
theorem cc13_theorem_2_7_jacobi_comparison
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.hasJacobiFieldComparison a := by
  sorry


end RiemannianFluids
