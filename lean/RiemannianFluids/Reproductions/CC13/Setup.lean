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


end RiemannianFluids
