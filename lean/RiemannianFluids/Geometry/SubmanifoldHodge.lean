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

/-- The paired arbitrary-codimension Hodge Gauss formulas of CCG25 Corollary 1.20 for one
pointwise Ricci jet. -/
def PointwiseRicciGaussJet.HasHodgeGaussFormulas
    (jet : PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Prop :=
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
        jet.ambientRicciNormal ∧
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
        jet.ambientRicciNormal

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

/-- Extend an actual-fiber Bochner jet by Ricci data constructed from one ambient connection.
The tangent-frame curvature, the ambient Ricci action, the normal-frame tangent trace, and the
normal output are all derived from the same ambient curvature tensor. -/
def isometricConnectionSubmanifoldRicciGaussJetAt
    [IsManifold I' 3 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (bochner : SubmanifoldBochnerGaussJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x)
    (intrinsicCurvature :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x) :
    SubmanifoldRicciGaussJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x :=
  submanifoldRicciGaussJetAt immersion.toSmoothImmersionData
    immersion.orthogonalSplitting x bochner intrinsicCurvature
    (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientConnection x ambientRegular)
    (connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
      (mfderiv I I' immersion.toFun x bochner.field))
    (normalFrameAmbientRicciActionAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientConnection x ambientRegular bochner.normalFrame
      bochner.field)
    (immersion.orthogonalSplitting.normalProjection x
      (connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
        (mfderiv I I' immersion.toFun x bochner.field)))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsManifold I 1 M] in
/-- The connection-constructed Ricci jet satisfies ambient trace splitting as a theorem whenever
its Bochner jet uses the canonical tangent lift `df_x`.  In particular, no Ricci splitting
identity remains to be supplied by a paper-facing adapter. -/
theorem isometricConnectionSubmanifoldRicciGaussJetAt_hasAmbientRicciTraceSplitting
    [IsManifold I' 3 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (bochner : SubmanifoldBochnerGaussJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x)
    (intrinsicCurvature :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x)
    (canonicalTangentLift :
      bochner.tangentLift = mfderiv I I' immersion.toFun x) :
    (isometricConnectionSubmanifoldRicciGaussJetAt immersion ambientConnection x
      ambientRegular bochner intrinsicCurvature).HasAmbientRicciTraceSplitting := by
  rw [PointwiseRicciGaussJet.HasAmbientRicciTraceSplitting]
  change
    connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
        (mfderiv I I' immersion.toFun x bochner.field) =
      bochner.tangentLift
          (ricciActionOfCurvatureTensor
              (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
                immersion.orthogonalSplitting ambientConnection x ambientRegular)
              bochner.field +
            normalFrameAmbientRicciActionAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting ambientConnection x ambientRegular
              bochner.normalFrame bochner.field) +
        immersion.orthogonalSplitting.normalProjection x
          (connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
            (mfderiv I I' immersion.toFun x bochner.field))
  rw [canonicalTangentLift]
  exact immersion.connectionRicciActionAlong_eq_adaptedTraceAt ambientConnection x
    ambientRegular bochner.tangentFrame bochner.normalFrame bochner.field

/-- The single-source Ricci/Hodge jet obtained by adjoining the ambient and intrinsic curvature
traces to the differentiated Gauss--Weingarten jet.  Every curvature term is evaluated from the
same induced/ambient Levi--Civita pair used to construct `II` and `∇ᴮ II`. -/
def inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (field : TangentSpace I x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (normal : AmbientVectorFieldAlong immersion.toSmoothImmersionData) :
    SubmanifoldRicciGaussJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x :=
  isometricConnectionSubmanifoldRicciGaussJetAt
    immersion ambientLeviCivita.connection x ambientRegular
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal
      ).toPointwiseBochnerGaussJet
    (connectionCurvatureTensorAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection
      x intrinsicRegular)

/-- The Gauss tensor carried by the single-source Ricci jet is definitionally the previously
constructed single-source immersion Gauss package. -/
@[simp]
theorem inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt_gaussData
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (field : TangentSpace I x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (normal : AmbientVectorFieldAlong immersion.toSmoothImmersionData) :
    (inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal).gaussData =
      inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
        immersion ambientLeviCivita extensions x intrinsicRegular :=
  rfl

/-- The Ricci trace of the single-source Hodge jet splits over its adapted tangent and normal
frames by construction. -/
theorem inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt_hasAmbientRicciTraceSplitting
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (field : TangentSpace I x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (normal : AmbientVectorFieldAlong immersion.toSmoothImmersionData) :
    (inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal
      ).HasAmbientRicciTraceSplitting := by
  apply isometricConnectionSubmanifoldRicciGaussJetAt_hasAmbientRicciTraceSplitting
  rfl

/-- Both arbitrary-codimension Hodge Gauss formulas of CCG25 Corollary 1.20 on the actual
fibers of one isometric immersion.  Scalar Gauss, the adapted ambient Ricci splitting,
contracted Codazzi, and bracket--Weingarten are discharged by the geometric construction. -/
theorem inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt_hodgeGaussFormulas
    [Nonempty ι]
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (field : TangentSpace I x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (normal : AmbientVectorFieldAlong immersion.toSmoothImmersionData)
    (normalExtension_mdifferentiableAt : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x))
    (normal_mem : ∀ y,
      immersion.orthogonalSplitting.tangentProjection y (normal y) = 0)
    (normal_value : normal x =
      (inducedLeviCivitaSubmanifoldMeanCurvatureAt immersion ambientLeviCivita
        extensions x tangentFrame : TangentSpace I' (immersion.toFun x)))
    (normal_derivative :
      extensions.toSubmanifoldFieldExtensionData.normalDerivative
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field)
          normal x =
        (inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt immersion ambientLeviCivita
          extensions x intrinsicRegular extensionRegular tangentFrame field :
            TangentSpace I' (immersion.toFun x))) :
    let jet := inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal
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
          jet.ambientRicciNormal ∧
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
  dsimp only
  have symmetric :
      (inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative normal).gaussData.IsSymmetric := by
    change (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
      immersion ambientLeviCivita extensions x intrinsicRegular).IsSymmetric
    exact inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_isSymmetric
      immersion ambientLeviCivita extensions x intrinsicRegular
  have scalarGauss :
      (inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative normal).gaussData.HasGaussEquationRelativeTo
          (inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
            immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
            extensionRegular tangentFrame normalFrame field firstDerivative
            intrinsicSecondDerivative ambientNormalSecondDerivative
            ambientNormalAccelerationDerivative normal).ambientTangentialCurvature := by
    change (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
      immersion ambientLeviCivita extensions x intrinsicRegular).HasGaussEquationRelativeTo
        (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection x ambientRegular)
    exact inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasGaussEquationRelativeTo
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
  have traceSplitting :=
    inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt_hasAmbientRicciTraceSplitting
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal
  have codazzi :=
    inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_hasContractedCodazzi
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      (ambientNormalDerivativeOfCanonicalTangentFieldAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection extensions x field)
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative
      (ambientBracketOfNormalAndCanonicalTangentFieldAt immersion.toSmoothImmersionData
        extensions x field normal)
  have bracketWeingarten :=
    inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_hasMeanBracketWeingarten
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal
      normalExtension_mdifferentiableAt normal_mem normal_value normal_derivative
  constructor
  · exact PointwiseRicciGaussJet.ambientHodge_eq_firstGaussFormula _
      symmetric scalarGauss traceSplitting codazzi bracketWeingarten
  · exact PointwiseRicciGaussJet.ambientHodge_eq_secondGaussFormula _
      symmetric scalarGauss traceSplitting

/-- Adjoin the intrinsic and ambient curvature traces to a named CCG25 analytic field-jet
realization. -/
def SubmanifoldLaplacianFieldJetDataAt.toRicciGaussJet
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    {intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x}
    {extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x}
    (data : SubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x)) :
    SubmanifoldRicciGaussJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x :=
  inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    data.tangentFrame data.normalFrame data.field data.firstDerivative
    data.intrinsicSecondDerivative data.ambientNormalSecondDerivative
    data.ambientNormalAccelerationDerivative data.meanNormalField

/-- A named analytic field-jet realization produces both CCG25 Hodge Gauss formulas after all
geometric identities are discharged by the common immersion/connection construction. -/
theorem SubmanifoldLaplacianFieldJetDataAt.hasHodgeGaussFormulas
    [Nonempty ι]
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    {immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N)}
    {ambientLeviCivita : LeviCivitaConnection (M := N) I'}
    {extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData}
    {x : M}
    {intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x}
    {extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x}
    (data : SubmanifoldLaplacianFieldJetDataAt
      (ι := ι) (κ := κ) immersion ambientLeviCivita extensions x intrinsicRegular
        extensionRegular)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x)) :
    (data.toRicciGaussJet ambientRegular).HasHodgeGaussFormulas := by
  rw [PointwiseRicciGaussJet.HasHodgeGaussFormulas]
  exact inducedLeviCivitaSubmanifoldRicciGaussJetOfMeanFieldAt_hodgeGaussFormulas
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    data.tangentFrame data.normalFrame data.field data.firstDerivative
    data.intrinsicSecondDerivative data.ambientNormalSecondDerivative
    data.ambientNormalAccelerationDerivative data.meanNormalField
    data.meanNormalField_extension_mdifferentiableAt data.meanNormalField_mem
    data.meanNormalField_value data.meanNormalField_derivative

end ManifoldFibers

end

end RiemannianFluids
