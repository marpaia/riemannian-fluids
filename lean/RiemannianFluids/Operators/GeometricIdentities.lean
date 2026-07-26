import RiemannianFluids.Operators.Hodge
import RiemannianFluids.Operators.Viscosity

/-!
# Ricci action and the CCD17 comparison identities

This module states the rough/Hodge and symmetric-gradient identities with the
analysis-positive sign convention.  Their combination is the full form of
CCD17 equation (1.3), and concrete divergence-freeness removes the `d d*`
term.

The first-order `Def` tensor and `d*` on one-forms are concrete.  A Ricci
endomorphism, the formal-adjoint realization `2 Def* Def`, and the missing
degree-one de Rham data remain explicit inputs until the underlying manifold
library provides curvature and integration/formal-adjoint infrastructure.
-/

namespace RiemannianFluids

open Bundle
open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- Linear second-order vector operators with an explicit loss of two derivatives. -/
abbrev SecondOrderVectorOperator (regularity : ℕ∞ω) :=
  SmoothVectorField (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
    SmoothVectorField (M := M) I regularity

/-- Forget excess regularity of a vector field. -/
noncomputable def restrictVectorFieldRegularity
    {lower higher : ℕ∞ω} (h : lower ≤ higher) :
    SmoothVectorField (M := M) I higher →ₗ[ℝ]
      SmoothVectorField (M := M) I lower where
  toFun field :=
    { toFun := field
      contMDiff_toFun := field.contMDiff.of_le h }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem restrictVectorFieldRegularity_apply
    {lower higher : ℕ∞ω} (h : lower ≤ higher)
    (field : SmoothVectorField (M := M) I higher) (x : M) :
    restrictVectorFieldRegularity I h field x = field x :=
  rfl

/-- Pointwise action of a smooth tangent-bundle endomorphism. -/
noncomputable def applyVectorEndomorphism
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (endomorphism : SmoothVectorOneForm (M := M) I regularity) :
    SmoothVectorField (M := M) I regularity →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity where
  toFun field :=
    { toFun := fun x => endomorphism x (field x)
      contMDiff_toFun := endomorphism.contMDiff.clm_bundle_apply field.contMDiff }
  map_add' first second := by
    ext x
    simp
  map_smul' scalar field := by
    ext x
    simp

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem applyVectorEndomorphism_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (endomorphism : SmoothVectorOneForm (M := M) I regularity)
    (field : SmoothVectorField (M := M) I regularity) (x : M) :
    applyVectorEndomorphism I regularity endomorphism field x =
      endomorphism x (field x) :=
  rfl

/--
Ricci curvature as the metric-raised endomorphism field.  Its derivation by
contracting the Riemann curvature tensor is deliberately left outside this
data structure rather than asserted axiomatically.
-/
structure RicciData (regularity : ℕ∞ω) where
  endomorphism : SmoothVectorOneForm (M := M) I regularity

/-- Zeroth-order Ricci action, viewed on the common second-order domain. -/
noncomputable def RicciData.action
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (ricci : RicciData (M := M) I regularity) :
    SecondOrderVectorOperator (M := M) I regularity :=
  (applyVectorEndomorphism I regularity ricci.endomorphism).comp
    (restrictVectorFieldRegularity I
      (le_trans (le_self_add : regularity ≤ regularity + 1) le_self_add))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem RicciData.action_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (ricci : RicciData (M := M) I regularity)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (x : M) :
    ricci.action I regularity field x = ricci.endomorphism x (field x) :=
  rfl

/--
The geometric data entering CCD17.  `deformationLaplacian` denotes the
analysis-positive operator `2 Def* Def`.
-/
structure CCD17OperatorData (regularity : ℕ∞ω) where
  hodge : OneFormHodgeData (M := M) I regularity
  ricci : RicciData (M := M) I regularity
  roughLaplacian : SecondOrderVectorOperator (M := M) I regularity
  deformationLaplacian : SecondOrderVectorOperator (M := M) I regularity

/-- The vector Hodge Laplacian determined by the degree-one de Rham data. -/
noncomputable def CCD17OperatorData.hodgeLaplacian
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) :
    SecondOrderVectorOperator (M := M) I regularity :=
  operators.hodge.hodgeLaplacianVector I regularity connection smooth

/-- Analysis-positive Weitzenböck identity: `∇*∇ = L_Hodge - Ric`. -/
def WeitzenbockIdentity
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  operators.roughLaplacian =
    operators.hodgeLaplacian I regularity connection smooth -
      operators.ricci.action I regularity

/-- Symmetric-gradient identity: `2 Def*Def = ∇*∇ + d d* - Ric`. -/
def SymmetricGradientIdentity
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  operators.deformationLaplacian =
    operators.roughLaplacian +
      exactCodifferentialCorrection I regularity connection smooth -
      operators.ricci.action I regularity

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/--
CCD17 equation (1.3), translated to the analysis-positive convention:
`L_Def = L_Hodge + d d* - 2 Ric`.
-/
theorem ccd17_positive_full
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators) :
    operators.deformationLaplacian =
      operators.hodgeLaplacian I regularity connection smooth +
        exactCodifferentialCorrection I regularity connection smooth -
        (2 : ℝ) • operators.ricci.action I regularity := by
  rw [hSymmetric, hWeitzenbock]
  module

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/--
CCD17 equation (1.3) on a divergence-free field:
`L_Def u = L_Hodge u - 2 Ric(u)`.
-/
theorem ccd17_divfree_def_hodge
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (hdiv : IsDivergenceFree I connection (regularity + 1) smooth field) :
    operators.deformationLaplacian field =
      operators.hodgeLaplacian I regularity connection smooth field -
        (2 : ℝ) • operators.ricci.action I regularity field := by
  rw [ccd17_positive_full I regularity connection smooth operators hWeitzenbock hSymmetric]
  rw [LinearMap.sub_apply, LinearMap.add_apply,
    exactCodifferentialCorrection_eq_zero_of_divergenceFree
      I regularity connection smooth field hdiv]
  simp

end RiemannianFluids
