import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import RiemannianFluids.ProofStatus

/-!
# CCF25 statement contracts

Source: Chan--Czubak--Fuster Aguilera, *Thin shell limit and the derivation of the
viscosity operator on the ellipsoid*, arXiv:2511.10579v1, Theorems 1.1, 1.3, 1.6,
and Remark 1.5.  The paper explicitly describes its convergence argument as heuristic;
these declarations therefore specify symbolic contracts and do not claim an analytic limit.
-/

namespace RiemannianFluids

/-- The four scaling-direction candidates, numbered as equations (1.4)--(1.7). -/
structure CCF25CandidateData (Field : Type*) where
  candidate : Fin 4 → Field → Field
  deformationEndpoint : Field → Field
  hodgeEndpoint : Field → Field
  isRoundSphere : Prop
  scalingCoefficientVanishes : Prop

/-- On a round sphere, the two Navier candidates reduce to deformation and the two Hodge candidates reduce to Hodge. -/
def ccf25FourCandidatesSphereStatement
    {Field : Type*} (data : CCF25CandidateData Field) : Prop :=
  data.isRoundSphere →
    (∀ field, data.candidate 0 field = data.deformationEndpoint field) ∧
    (∀ field, data.candidate 1 field = data.hodgeEndpoint field) ∧
    (∀ field, data.candidate 2 field = data.deformationEndpoint field) ∧
    (∀ field, data.candidate 3 field = data.hodgeEndpoint field)

/-- The five operator terms appearing in formulas (1.4)--(1.7). -/
structure CCF25ScalingFormulaData (Field : Type*) where
  axisScale : ℝ
  thickness : ℝ
  deformationLaplacian : Field → Field
  hodgeLaplacian : Field → Field
  bracketCorrection : Field → Field
  squareCorrection : Field → Field
  lieDerivativeCorrection : Field → Field
  navierAlwaysTangentialCandidate : Field → Field
  hodgeAlwaysTangentialCandidate : Field → Field
  navierDoubleDivergenceFreeCandidate : Field → Field
  hodgeDoubleDivergenceFreeCandidate : Field → Field
  hasEllipsoidFrameIdentities : Prop
  hasScalingAsymptoticExpansion : Prop
  hasGaussLaplacianFormula : Prop
  hasCoefficientIdentityLemma4_2 : Prop

/-- CCF25 Theorems 1.1 and 1.3: the four scaling-direction candidates with every correction exposed. -/
def ccf25ScalingFormulaStatement
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) : Prop :=
  0 < data.axisScale → 0 < data.thickness →
  (∀ field,
    data.navierAlwaysTangentialCandidate field =
      data.deformationLaplacian field + data.bracketCorrection field +
        (2 : ℤ) • data.squareCorrection field) ∧
  (∀ field,
    data.hodgeAlwaysTangentialCandidate field =
      data.hodgeLaplacian field + data.lieDerivativeCorrection field) ∧
  (∀ field,
    data.navierDoubleDivergenceFreeCandidate field =
      data.deformationLaplacian field + data.bracketCorrection field) ∧
  ∀ field,
    data.hodgeDoubleDivergenceFreeCandidate field =
      data.hodgeLaplacian field + data.lieDerivativeCorrection field -
        (2 : ℤ) • data.squareCorrection field

/-- Exact two-formula conclusion of CCF25 Theorem 1.1. -/
def ccf25Theorem1_1Statement
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) : Prop :=
  0 < data.axisScale → 0 < data.thickness →
    (∀ field,
      data.navierAlwaysTangentialCandidate field =
        data.deformationLaplacian field + data.bracketCorrection field +
          (2 : ℤ) • data.squareCorrection field) ∧
    ∀ field,
      data.hodgeAlwaysTangentialCandidate field =
        data.hodgeLaplacian field + data.lieDerivativeCorrection field

/-- Exact two-formula conclusion of CCF25 Theorem 1.3. -/
def ccf25Theorem1_3Statement
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) : Prop :=
  0 < data.axisScale → 0 < data.thickness →
    (∀ field,
      data.navierDoubleDivergenceFreeCandidate field =
        data.deformationLaplacian field + data.bracketCorrection field) ∧
    ∀ field,
      data.hodgeDoubleDivergenceFreeCandidate field =
        data.hodgeLaplacian field + data.lieDerivativeCorrection field -
          (2 : ℤ) • data.squareCorrection field

/-- Normal-coordinate expansions for Theorem 1.6 and Remark 1.8. -/
structure CCF25NormalFormulaData (Field : Type*) where
  axisScale : ℝ
  thickness : ℝ
  hodgeBoundaryCandidate : Field → Field
  navierBoundaryCandidate : Field → Field
  hodgeLaplacian : Field → Field
  deformationLaplacian : Field → Field
  hasTubularNormalCoordinates : Prop
  hasNormalPowerSeries : Prop

def ccf25NormalDirectionStatement
    {Field : Type*} (data : CCF25NormalFormulaData Field) : Prop :=
  0 < data.axisScale → 0 < data.thickness →
  (∀ field, data.hodgeBoundaryCandidate field = data.hodgeLaplacian field) ∧
    ∀ field, data.navierBoundaryCandidate field = data.deformationLaplacian field

/-- Boundary observables in Propositions 3.1--3.2 and Theorem 1.9. -/
structure CCF25BoundaryData (Field VectorCondition FormCondition : Type*) where
  perfectNavierSlip : Field → VectorCondition
  tangentialNormalLieBracket : Field → VectorCondition
  hodgeCurlCondition : Field → FormCondition
  pulledBackNormalLieDerivative : Field → FormCondition

def ccf25GeometricBoundaryStatement
    {Field VectorCondition FormCondition : Type*}
    (data : CCF25BoundaryData Field VectorCondition FormCondition) : Prop :=
  (∀ field,
    data.perfectNavierSlip field = data.tangentialNormalLieBracket field) ∧
  ∀ field,
    data.hodgeCurlCondition field = data.pulledBackNormalLieDerivative field

/-- Observable operators produced by scaling-direction and normal-direction averaging. -/
structure CCF25AveragingData (Field : Type*) where
  isGenuinelyNonsphericalAxisymmetricEllipsoid : Prop
  scalingDirectionAverage : Field → Field
  normalDirectionAverage : Field → Field

/-- On a genuinely nonspherical ellipsoid, the averaging prescription can change the candidate operator. -/
def ccf25AveragingDependenceStatement
    {Field : Type*} (data : CCF25AveragingData Field) : Prop :=
  data.isGenuinelyNonsphericalAxisymmetricEllipsoid →
    ∃ field, data.scalingDirectionAverage field ≠ data.normalDirectionAverage field


end RiemannianFluids
