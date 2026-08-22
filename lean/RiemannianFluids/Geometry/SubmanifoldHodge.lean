import RiemannianFluids.Geometry.SubmanifoldLaplacian

/-!
# Ricci and Hodge Gauss traces

This file completes the pointwise geometric-operator kernel used by CCG25.  The scalar Gauss
equation is contracted against the tangent frame, then combined with the tangent/normal splitting
of the ambient Ricci trace.  Adding that proved Ricci identity to the two proved Bochner identities
is the Bochner--Weitzenbock derivation of the two Hodge formulas.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

noncomputable section

section PointwiseHodge

variable
  {ι κ Tangent Normal Ambient : Type*}
  [Fintype ι] [Fintype κ]
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [FiniteDimensional ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
  [FiniteDimensional ℝ Normal]
  [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

/-- Ricci data tied to the same frame, second fundamental form, field, and tangent lift as the
Bochner Gauss jet. -/
structure PointwiseRicciGaussJet where
  bochner : PointwiseBochnerGaussJet
    (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
  intrinsicCurvature :
    Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent
  ambientTangentialCurvature :
    Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent
  ambientRicci : Ambient
  ambientNormalRicciTrace : Tangent
  ambientRicciNormal : Ambient

/-- The scalar-Gauss tensors associated with a Ricci jet. -/
def PointwiseRicciGaussJet.gaussData
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    PointwiseGaussData (Tangent := Tangent) (Normal := Normal) where
  intrinsicCurvature := jet.intrinsicCurvature
  secondFundamental := jet.bochner.secondFundamental

/-- The ambient Ricci trace splits into its tangent-frame trace, normal-frame tangent trace, and
normal output.  This is the primitive trace-splitting identity used in CCG25 Theorem 1.9. -/
def PointwiseRicciGaussJet.HasAmbientRicciTraceSplitting
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Prop :=
  jet.ambientRicci =
    jet.bochner.tangentLift
      (ricciActionOfCurvatureTensor jet.ambientTangentialCurvature jet.bochner.field +
        jet.ambientNormalRicciTrace) +
      jet.ambientRicciNormal

/-- The intrinsic Ricci action, lifted to the ambient fiber. -/
def PointwiseRicciGaussJet.intrinsicRicci
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.bochner.tangentLift
    (ricciActionOfCurvatureTensor jet.intrinsicCurvature jet.bochner.field)

/-- The normal-frame tangent part of ambient Ricci, lifted to the ambient fiber. -/
def PointwiseRicciGaussJet.ambientNormalRicciTraceValue
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.bochner.tangentLift jet.ambientNormalRicciTrace

/-- CCG25 Theorem 1.9, equation (1.11), obtained by contracting the scalar Gauss equation and
then splitting the ambient Ricci trace. -/
theorem PointwiseRicciGaussJet.ambientRicci_eq_gaussFormula
    [Nonempty ι]
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : jet.gaussData.IsSymmetric)
    (gauss : jet.gaussData.HasGaussEquationRelativeTo jet.ambientTangentialCurvature)
    (traceSplitting : jet.HasAmbientRicciTraceSplitting) :
    jet.ambientRicci =
      jet.intrinsicRicci -
        (Fintype.card ι : ℝ) • jet.bochner.meanShape +
        jet.bochner.normalShapeSquare +
        jet.ambientNormalRicciTraceValue +
        jet.ambientRicciNormal := by
  have contracted := gauss_ricci_relative
    jet.bochner.tangentFrame jet.bochner.normalFrame jet.gaussData
    jet.ambientTangentialCurvature symmetric gauss
  have tangentialRicci :
      ricciActionOfCurvatureTensor jet.ambientTangentialCurvature jet.bochner.field =
        ricciActionOfCurvatureTensor jet.intrinsicCurvature jet.bochner.field -
          (Fintype.card ι : ℝ) •
            shapeOperatorOfSecondFundamental jet.bochner.secondFundamental
              (meanCurvatureOfSecondFundamental jet.bochner.tangentFrame
                jet.bochner.secondFundamental) jet.bochner.field +
          RiemannianFluids.normalShapeSquare jet.bochner.normalFrame
            jet.bochner.secondFundamental jet.bochner.field := by
    have evaluated := congrArg
      (fun operator : Tangent →L[ℝ] Tangent ↦ operator jet.bochner.field) contracted
    have evaluated' :
        ricciActionOfCurvatureTensor jet.intrinsicCurvature jet.bochner.field =
          ricciActionOfCurvatureTensor jet.ambientTangentialCurvature jet.bochner.field +
              (Fintype.card ι : ℝ) •
                shapeOperatorOfSecondFundamental jet.bochner.secondFundamental
                  (meanCurvatureOfSecondFundamental jet.bochner.tangentFrame
                    jet.bochner.secondFundamental) jet.bochner.field -
            RiemannianFluids.normalShapeSquare jet.bochner.normalFrame
              jet.bochner.secondFundamental jet.bochner.field := by
      simpa [PointwiseRicciGaussJet.gaussData, add_apply, sub_apply, smul_apply] using evaluated
    rw [evaluated']
    module
  rw [traceSplitting, tangentialRicci,
    PointwiseRicciGaussJet.intrinsicRicci,
    PointwiseRicciGaussJet.ambientNormalRicciTraceValue,
    PointwiseBochnerGaussJet.meanShape,
    PointwiseBochnerGaussJet.normalShapeSquare]
  simp only [map_add, map_sub, map_smul]

/-- The Hodge values are defined by the analysis-positive Bochner--Weitzenbock sums. -/
def PointwiseRicciGaussJet.ambientHodge
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.bochner.ambientBochner + jet.ambientRicci

/-- Intrinsic Hodge value from intrinsic Bochner plus intrinsic Ricci. -/
def PointwiseRicciGaussJet.intrinsicHodge
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.bochner.intrinsicBochner + jet.intrinsicRicci

/-- The first arbitrary-codimension Hodge Gauss formula of CCG25 Corollary 1.20. -/
theorem PointwiseRicciGaussJet.ambientHodge_eq_firstGaussFormula
    [Nonempty ι]
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : jet.gaussData.IsSymmetric)
    (scalarGauss : jet.gaussData.HasGaussEquationRelativeTo jet.ambientTangentialCurvature)
    (traceSplitting : jet.HasAmbientRicciTraceSplitting)
    (codazzi : jet.bochner.HasContractedCodazzi)
    (bracketWeingarten : jet.bochner.HasMeanBracketWeingarten) :
    jet.ambientHodge =
      jet.intrinsicHodge +
        (2 : ℝ) • jet.bochner.normalShapeSquare -
        (2 * (Fintype.card ι : ℝ)) • jet.bochner.meanShape +
        jet.ambientNormalRicciTraceValue +
        (Fintype.card ι : ℝ) • jet.bochner.meanBracket -
        jet.bochner.normalSecondDerivativeTrace +
        jet.bochner.normalAccelerationDerivativeTrace -
        (2 : ℝ) • jet.bochner.secondFundamentalDerivativeTraceValue -
        jet.bochner.ambientCurvatureNormalTraceValue +
        jet.ambientRicciNormal := by
  rw [PointwiseRicciGaussJet.ambientHodge,
    jet.bochner.ambientBochner_eq_firstGaussFormula symmetric codazzi bracketWeingarten,
    jet.ambientRicci_eq_gaussFormula symmetric scalarGauss traceSplitting,
    PointwiseRicciGaussJet.intrinsicHodge]
  module

/-- The second equivalent arbitrary-codimension Hodge Gauss formula of CCG25 Corollary 1.20. -/
theorem PointwiseRicciGaussJet.ambientHodge_eq_secondGaussFormula
    [Nonempty ι]
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : jet.gaussData.IsSymmetric)
    (scalarGauss : jet.gaussData.HasGaussEquationRelativeTo jet.ambientTangentialCurvature)
    (traceSplitting : jet.HasAmbientRicciTraceSplitting) :
    jet.ambientHodge =
      jet.intrinsicHodge +
        (2 : ℝ) • jet.bochner.normalShapeSquare -
        (Fintype.card ι : ℝ) • jet.bochner.meanShape +
        jet.ambientNormalRicciTraceValue +
        (Fintype.card ι : ℝ) • jet.bochner.meanDerivative -
        jet.bochner.normalSecondDerivativeTrace +
        jet.bochner.normalAccelerationDerivativeTrace -
        jet.bochner.codazziTraceValue -
        (2 : ℝ) • jet.bochner.secondFundamentalDerivativeTraceValue +
        jet.ambientRicciNormal := by
  rw [PointwiseRicciGaussJet.ambientHodge,
    jet.bochner.ambientBochner_eq_secondGaussFormula symmetric,
    jet.ambientRicci_eq_gaussFormula symmetric scalarGauss traceSplitting,
    PointwiseRicciGaussJet.intrinsicHodge]
  module

end PointwiseHodge

/-! ## Actual tangent-fiber realization -/

section ManifoldFibers

variable
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)]

/-- A Ricci/Hodge jet on the actual tangent and kernel-normal fibers of an immersion. -/
abbrev SubmanifoldRicciGaussJetAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M) :=
  PointwiseRicciGaussJet
    (ι := ι) (κ := κ)
    (Tangent := TangentSpace I x)
    (Normal := SubmanifoldNormalSpaceAt immersion splitting x)
    (Ambient := TangentSpace I' (immersion.toFun x))

/-- Extend an actual-fiber Bochner jet with the curvature and Ricci traces required for the
Hodge derivation. -/
def submanifoldRicciGaussJetAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M)
    (bochner : SubmanifoldBochnerGaussJetAt
      (ι := ι) (κ := κ) immersion splitting x)
    (intrinsicCurvature ambientTangentialCurvature :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x)
    (ambientRicci : TangentSpace I' (immersion.toFun x))
    (ambientNormalRicciTrace : TangentSpace I x)
    (ambientRicciNormal : TangentSpace I' (immersion.toFun x)) :
    SubmanifoldRicciGaussJetAt (ι := ι) (κ := κ) immersion splitting x where
  bochner := bochner
  intrinsicCurvature := intrinsicCurvature
  ambientTangentialCurvature := ambientTangentialCurvature
  ambientRicci := ambientRicci
  ambientNormalRicciTrace := ambientNormalRicciTrace
  ambientRicciNormal := ambientRicciNormal

end ManifoldFibers

end

end RiemannianFluids
