import RiemannianFluids.Geometry.SubmanifoldGauss
import RiemannianFluids.Geometry.SubmanifoldLaplacian
import RiemannianFluids.Geometry.SubmanifoldHodge

/-!
# CCG25: Gauss formulas for Laplacians on submanifolds

The paper's arbitrary-codimension formulas contain long frame contractions.  The structures below
name each complete contracted term, while the proposition-valued source signatures retain every
coefficient and sign from Theorem 1.1 and Corollary 1.20.  An `Argument` represents a point,
tangent field, smooth ambient extension, and orthonormal tangent/normal frames satisfying the
paper's hypotheses; the values are pointwise tangent or ambient vectors in one common module.
-/

namespace RiemannianFluids.Literature.CCG25

open Bundle
open scoped Bundle ContDiff Manifold

/-- Complete contracted terms in the two equivalent Bochner Gauss formulas (1.5)--(1.6). -/
structure BochnerGaussFormulaData (Argument Value : Type*) where
  ambientBochner : Argument → Value
  intrinsicBochner : Argument → Value
  normalShapeSquare : Argument → Value
  meanShape : Argument → Value
  meanBracket : Argument → Value
  normalSecondDerivative : Argument → Value
  normalAccelerationDerivative : Argument → Value
  secondFundamentalDerivativeTrace : Argument → Value
  ambientCurvatureNormalTrace : Argument → Value
  meanDerivative : Argument → Value
  codazziTrace : Argument → Value

/-- Source signature for CCG25 Theorem 1.1, equations (1.5) and (1.6). -/
def bochner_laplacian_gauss_general_codimension_statement
    {Argument Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    (dimension codimension : ℕ)
    (data : BochnerGaussFormulaData Argument Value) : Prop :=
  2 ≤ dimension → 1 ≤ codimension → ∀ argument,
    data.ambientBochner argument =
      data.intrinsicBochner argument +
        data.normalShapeSquare argument -
        (dimension : ℝ) • data.meanShape argument +
        (dimension : ℝ) • data.meanBracket argument -
        data.normalSecondDerivative argument +
        data.normalAccelerationDerivative argument -
        (2 : ℝ) • data.secondFundamentalDerivativeTrace argument -
        data.ambientCurvatureNormalTrace argument ∧
    data.ambientBochner argument =
      data.intrinsicBochner argument +
        data.normalShapeSquare argument +
        (dimension : ℝ) • data.meanDerivative argument -
        data.normalSecondDerivative argument +
        data.normalAccelerationDerivative argument -
        data.codazziTrace argument -
        (2 : ℝ) • data.secondFundamentalDerivativeTrace argument

/-! ## The proved Gauss--Weingarten trace -/

section BochnerProof

variable
  {ι κ Argument Tangent Normal Ambient : Type*}
  [Fintype ι] [Nonempty ι] [Fintype κ]
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [FiniteDimensional ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
  [FiniteDimensional ℝ Normal]
  [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

/-- Assemble the CCG25 observables from the primitive differentiated Gauss--Weingarten jet. -/
noncomputable def bochnerGaussFormulaDataOfJet
    (jets : Argument → PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    BochnerGaussFormulaData Argument Ambient where
  ambientBochner argument := (jets argument).ambientBochner
  intrinsicBochner argument := (jets argument).intrinsicBochner
  normalShapeSquare argument := (jets argument).normalShapeSquare
  meanShape argument := (jets argument).meanShape
  meanBracket argument := (jets argument).meanBracket
  normalSecondDerivative argument := (jets argument).normalSecondDerivativeTrace
  normalAccelerationDerivative argument := (jets argument).normalAccelerationDerivativeTrace
  secondFundamentalDerivativeTrace argument :=
    (jets argument).secondFundamentalDerivativeTraceValue
  ambientCurvatureNormalTrace argument := (jets argument).ambientCurvatureNormalTraceValue
  meanDerivative argument := (jets argument).meanDerivative
  codazziTrace argument := (jets argument).codazziTraceValue

/-- CCG25 Theorem 1.1, equations (1.5)--(1.6), proved for every member of a family of
pointwise differentiated Gauss--Weingarten jets in arbitrary positive codimension. -/
theorem bochner_laplacian_gauss_general_codimension_of_gaussWeingarten
    (jets : Argument → PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : ∀ argument first second,
      (jets argument).secondFundamental first second =
        (jets argument).secondFundamental second first)
    (codazzi : ∀ argument, (jets argument).HasContractedCodazzi)
    (bracketWeingarten : ∀ argument, (jets argument).HasMeanBracketWeingarten) :
    bochner_laplacian_gauss_general_codimension_statement
      (Fintype.card ι) (Fintype.card κ) (bochnerGaussFormulaDataOfJet jets) := by
  intro _ _ argument
  constructor
  · simpa [bochnerGaussFormulaDataOfJet] using
      (jets argument).ambientBochner_eq_firstGaussFormula
        (symmetric argument) (codazzi argument) (bracketWeingarten argument)
  · simpa [bochnerGaussFormulaDataOfJet] using
      (jets argument).ambientBochner_eq_secondGaussFormula (symmetric argument)

end BochnerProof

/-- Complete contracted terms in the two arbitrary-codimension Hodge Gauss formulas of
CCG25 Corollary 1.20. -/
structure HodgeGaussFormulaData (Argument Value : Type*) where
  ambientHodge : Argument → Value
  intrinsicHodge : Argument → Value
  normalShapeSquare : Argument → Value
  meanShape : Argument → Value
  ambientNormalRicciTrace : Argument → Value
  meanBracket : Argument → Value
  normalSecondDerivative : Argument → Value
  normalAccelerationDerivative : Argument → Value
  secondFundamentalDerivativeTrace : Argument → Value
  ambientCurvatureNormalTrace : Argument → Value
  ambientRicciNormal : Argument → Value
  meanDerivative : Argument → Value
  codazziTrace : Argument → Value

/-- Source signature for the two equivalent general-codimension formulas in Corollary 1.20. -/
def hodge_laplacian_gauss_general_codimension_statement
    {Argument Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    (dimension codimension : ℕ)
    (data : HodgeGaussFormulaData Argument Value) : Prop :=
  2 ≤ dimension → 1 ≤ codimension → ∀ argument,
    data.ambientHodge argument =
      data.intrinsicHodge argument +
        (2 : ℝ) • data.normalShapeSquare argument -
        (2 * (dimension : ℝ)) • data.meanShape argument +
        data.ambientNormalRicciTrace argument +
        (dimension : ℝ) • data.meanBracket argument -
        data.normalSecondDerivative argument +
        data.normalAccelerationDerivative argument -
        (2 : ℝ) • data.secondFundamentalDerivativeTrace argument -
        data.ambientCurvatureNormalTrace argument +
        data.ambientRicciNormal argument ∧
    data.ambientHodge argument =
      data.intrinsicHodge argument +
        (2 : ℝ) • data.normalShapeSquare argument -
        (dimension : ℝ) • data.meanShape argument +
        data.ambientNormalRicciTrace argument +
        (dimension : ℝ) • data.meanDerivative argument -
        data.normalSecondDerivative argument +
        data.normalAccelerationDerivative argument -
        data.codazziTrace argument -
        (2 : ℝ) • data.secondFundamentalDerivativeTrace argument +
        data.ambientRicciNormal argument

/-! ## The proved Bochner--Weitzenbock derivation -/

section HodgeProof

variable
  {ι κ Argument Tangent Normal Ambient : Type*}
  [Fintype ι] [Nonempty ι] [Fintype κ]
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [FiniteDimensional ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
  [FiniteDimensional ℝ Normal]
  [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

/-- Assemble every Corollary 1.20 observable from the common Bochner/Ricci jet. -/
noncomputable def hodgeGaussFormulaDataOfJet
    (jets : Argument → PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    HodgeGaussFormulaData Argument Ambient where
  ambientHodge argument := (jets argument).ambientHodge
  intrinsicHodge argument := (jets argument).intrinsicHodge
  normalShapeSquare argument := (jets argument).bochner.normalShapeSquare
  meanShape argument := (jets argument).bochner.meanShape
  ambientNormalRicciTrace argument := (jets argument).ambientNormalRicciTraceValue
  meanBracket argument := (jets argument).bochner.meanBracket
  normalSecondDerivative argument := (jets argument).bochner.normalSecondDerivativeTrace
  normalAccelerationDerivative argument :=
    (jets argument).bochner.normalAccelerationDerivativeTrace
  secondFundamentalDerivativeTrace argument :=
    (jets argument).bochner.secondFundamentalDerivativeTraceValue
  ambientCurvatureNormalTrace argument :=
    (jets argument).bochner.ambientCurvatureNormalTraceValue
  ambientRicciNormal argument := (jets argument).ambientRicciNormal
  meanDerivative argument := (jets argument).bochner.meanDerivative
  codazziTrace argument := (jets argument).bochner.codazziTraceValue

/-- CCG25 Corollary 1.20, both equivalent arbitrary-codimension Hodge formulas, derived by
adding the proved Ricci Gauss trace to the two proved Bochner Gauss traces. -/
theorem hodge_laplacian_gauss_general_codimension_of_weizenbock
    (jets : Argument → PointwiseRicciGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : ∀ argument, (jets argument).gaussData.IsSymmetric)
    (scalarGauss : ∀ argument,
      (jets argument).gaussData.HasGaussEquationRelativeTo
        (jets argument).ambientTangentialCurvature)
    (traceSplitting : ∀ argument, (jets argument).HasAmbientRicciTraceSplitting)
    (codazzi : ∀ argument, (jets argument).bochner.HasContractedCodazzi)
    (bracketWeingarten : ∀ argument,
      (jets argument).bochner.HasMeanBracketWeingarten) :
    hodge_laplacian_gauss_general_codimension_statement
      (Fintype.card ι) (Fintype.card κ) (hodgeGaussFormulaDataOfJet jets) := by
  intro _ _ argument
  constructor
  · simpa [hodgeGaussFormulaDataOfJet] using
      (jets argument).ambientHodge_eq_firstGaussFormula
        (symmetric argument) (scalarGauss argument) (traceSplitting argument)
        (codazzi argument) (bracketWeingarten argument)
  · simpa [hodgeGaussFormulaDataOfJet] using
      (jets argument).ambientHodge_eq_secondGaussFormula
        (symmetric argument) (scalarGauss argument) (traceSplitting argument)

end HodgeProof

/-! ## Actual-immersion Bochner and Hodge theorems -/

section ActualImmersionProof

variable
  {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
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

/-- CCG25 Theorem 1.1 on actual tangent, kernel-normal, and ambient tangent fibers of an
isometric immersion.  `II`, `∇ᴮ II`, projected ambient curvature, contracted Codazzi, and
bracket--Weingarten are constructed from one Levi--Civita package; `data` names the remaining
analytic field-jet realization boundary. -/
theorem bochner_laplacian_gauss_general_codimension_of_isometric_immersion
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
    (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.HasGaussFormulas :=
  data.hasGaussFormulas ambientRegular

/-- CCG25 Corollary 1.20 on the same actual fibers and analytic field-jet realization.  The
Ricci, scalar Gauss, Codazzi, and bracket--Weingarten inputs are all discharged by the common
Levi--Civita construction. -/
theorem hodge_laplacian_gauss_general_codimension_of_isometric_immersion
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
    (data.toRicciGaussJet ambientRegular).HasHodgeGaussFormulas :=
  data.hasHodgeGaussFormulas ambientRegular

end ActualImmersionProof

/-- Euclidean Gauss-equation terms for the intrinsic Ricci action in codimension two. -/
structure EuclideanCodimensionTwoRicciData (Argument Value : Type*) where
  intrinsicRicci : Argument → Value
  meanShape : Argument → Value
  normalShapeSquare : Argument → Value

/-- Source signature for Theorem 1.9, equation (1.12), specialized to a two-dimensional
submanifold of Euclidean codimension two. -/
def gauss_ricci_codimension_two_statement
    {Argument Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    (data : EuclideanCodimensionTwoRicciData Argument Value) : Prop :=
  ∀ argument,
    data.intrinsicRicci argument =
      (2 : ℝ) • data.meanShape argument - data.normalShapeSquare argument

/-! ## Proved Euclidean Gauss contraction

The source signature above deliberately remains carrier-polymorphic.  The following constructor
and theorem instantiate it with the concrete finite-dimensional Riemannian tensors from
`Geometry.SubmanifoldGauss`: the Ricci action is the trace of an actual continuous curvature
tensor, while the shape and mean-curvature terms are constructed from one symmetric
normal-valued second fundamental form.
-/

section EuclideanRicciProof

variable
  {Tangent Normal : Type*}
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [FiniteDimensional ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
  [FiniteDimensional ℝ Normal]

/-- The exact CCG25 equation (1.12) observables constructed from a two-dimensional tangent
frame, a two-dimensional normal frame, curvature, and `II`. -/
noncomputable def euclideanCodimensionTwoRicciData
    (tangentFrame : OrthonormalBasis (Fin 2) ℝ Tangent)
    (normalFrame : OrthonormalBasis (Fin 2) ℝ Normal)
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal)) :
    EuclideanCodimensionTwoRicciData Tangent Tangent where
  intrinsicRicci := ricciActionOfCurvatureTensor data.intrinsicCurvature
  meanShape :=
    shapeOperatorOfSecondFundamental data.secondFundamental
      (meanCurvatureOfSecondFundamental tangentFrame data.secondFundamental)
  normalShapeSquare := normalShapeSquare normalFrame data.secondFundamental

/-- CCG25 Theorem 1.9, equation (1.12), for intrinsic dimension two and Euclidean codimension
two, proved by contracting the scalar Gauss equation. -/
theorem gauss_ricci_codimension_two_of_euclidean_gauss
    (tangentFrame : OrthonormalBasis (Fin 2) ℝ Tangent)
    (normalFrame : OrthonormalBasis (Fin 2) ℝ Normal)
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (symmetric : data.IsSymmetric)
    (gauss : data.HasEuclideanGaussEquation) :
    gauss_ricci_codimension_two_statement
      (euclideanCodimensionTwoRicciData tangentFrame normalFrame data) := by
  intro field
  have h := congrArg (fun operator : Tangent →L[ℝ] Tangent ↦ operator field)
    (euclidean_gauss_ricci tangentFrame normalFrame data symmetric gauss)
  simpa [euclideanCodimensionTwoRicciData] using h

end EuclideanRicciProof

/-! ## Source-setting Euclidean immersion theorem -/

section ImmersionEuclideanRicciProof

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)]
  [∀ x : N, FiniteDimensional ℝ (TangentSpace I' x)]

/-- CCG25 Theorem 1.9, equation (1.12), on the actual tangent and normal fibers of a
two-dimensional isometric immersion with two-dimensional normal fiber and flat ambient curvature.
The Euclidean Gauss equation is derived from the induced and ambient connections under the exact
differentiated-extension regularity contract; it is not supplied as a premise. -/
theorem gauss_ricci_codimension_two_of_isometric_immersion
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
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
    (ambientFlat : tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection x ambientRegular = 0)
    (tangentFrame : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis (Fin 2) ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x)) :
    gauss_ricci_codimension_two_statement
      (euclideanCodimensionTwoRicciData tangentFrame normalFrame
        (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
          immersion ambientLeviCivita extensions x intrinsicRegular)) := by
  apply gauss_ricci_codimension_two_of_euclidean_gauss
  · exact inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_isSymmetric
      immersion ambientLeviCivita extensions x intrinsicRegular
  · exact inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasEuclideanGaussEquation
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
      extensionRegular ambientFlat

end ImmersionEuclideanRicciProof

end RiemannianFluids.Literature.CCG25
