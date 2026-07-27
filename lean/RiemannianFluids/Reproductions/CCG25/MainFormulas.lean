import RiemannianFluids.Reproductions.CCG25.Preliminaries

/-! # CCG25 Sections 3.1--3.9: proofs of the Gauss formulas -/

namespace RiemannianFluids

/-- Theorem 1.1: both equivalent Bochner Gauss formulas, represented here by equation (1.5). -/
@[proof_obligation]
theorem ccg25_theorem_1_1_bochner_gauss
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector)
    (hDimension : 2 ≤ data.intrinsicDimension)
    (hCodimension : 1 ≤ data.codimension) :
    ∀ vector,
      data.ambientBochner vector =
        data.intrinsicBochner vector + data.normalShapeSquareTerm vector -
          data.meanCurvatureShapeTerm vector + data.meanCurvatureBracketTerm vector -
          data.normalHessianTraceTerm vector -
          (2 : ℤ) • data.mixedSecondFundamentalTerm vector -
          data.ambientCurvatureNormalTerm vector := by
  have hGauss := ccg25_proposition_2_1_gauss_weingarten data
  have hNormal := ccg25_lemma_2_2_normal_frame_derivatives data
  have hSplit := ccg25_lemma_2_3_extension_derivative_splitting data
  have hTrace := ccg25_lemma_3_1_frame_trace data
  sorry

/-- Corollary 1.7's proof: compare the normal components of the two formulas in Theorem 1.1. -/
@[proof_obligation]
theorem ccg25_corollary_1_7_normal_component_comparison
    {TangentVector NormalVector : Type*}
    [AddCommGroup TangentVector] [AddCommGroup NormalVector]
    (data : CCG25CodazziData TangentVector NormalVector)
    (hDimension : 2 ≤ data.laplacian.intrinsicDimension)
    (hCodimension : 1 ≤ data.laplacian.codimension)
    (hBochner : ∀ vector,
      data.laplacian.ambientBochner vector =
        data.laplacian.intrinsicBochner vector +
          data.laplacian.normalShapeSquareTerm vector -
          data.laplacian.meanCurvatureShapeTerm vector +
          data.laplacian.meanCurvatureBracketTerm vector -
          data.laplacian.normalHessianTraceTerm vector -
          (2 : ℤ) • data.laplacian.mixedSecondFundamentalTerm vector -
          data.laplacian.ambientCurvatureNormalTerm vector) :
    HasContractedCodazziIdentity data.contracted ∧
      (data.laplacian.codimension = 1 →
        ∀ vector,
          data.divergenceSecondFundamental vector =
            (data.laplacian.intrinsicDimension : ℝ) *
              data.meanCurvatureDerivative vector -
              data.ambientRicciNormalPairing vector) := by
  sorry

@[literature_terminal]
theorem ccg25_corollary_1_7_contracted_codazzi
    {TangentVector NormalVector : Type*}
    [AddCommGroup TangentVector] [AddCommGroup NormalVector]
    (data : CCG25CodazziData TangentVector NormalVector) :
    ccg25ContractedCodazziStatement data := by
  intro hDimension hCodimension
  have hBochner :=
    ccg25_theorem_1_1_bochner_gauss data.laplacian hDimension hCodimension
  exact ccg25_corollary_1_7_normal_component_comparison data hDimension
    hCodimension hBochner

/-- Theorem 1.9: Gauss' curvature equation contracted to the Ricci endomorphism. -/
@[proof_obligation]
theorem ccg25_theorem_1_9_ricci_gauss
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25RicciData Vector) :
    ccg25GaussRicciArbitraryCodimensionStatement data := by
  sorry

/-- Corollary 1.12 follows from Theorem 1.1 by setting the ambient curvature tensor to zero. -/
@[proof_assembly]
theorem ccg25_corollary_1_12_euclidean_bochner
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) :
    ccg25EuclideanBochnerStatement data := by
  intro hDimension hCodimension hEuclidean vector
  have hBochner :=
    ccg25_theorem_1_1_bochner_gauss data.laplacian hDimension hCodimension vector
  simpa [data.euclideanCurvatureTermsVanish hEuclidean vector] using hBochner

/-- Corollary 1.16: combine Theorem 1.1, Theorem 1.9, and the two Weitzenbock identities for the deformation operator. -/
@[proof_obligation]
theorem ccg25_corollary_1_16_deformation_from_bochner_and_ricci
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector)
    (hDimension : 2 ≤ data.laplacian.intrinsicDimension)
    (hCodimension : 1 ≤ data.laplacian.codimension)
    (hBochner : ∀ vector,
      data.laplacian.ambientBochner vector =
        data.laplacian.intrinsicBochner vector +
          data.laplacian.normalShapeSquareTerm vector -
          data.laplacian.meanCurvatureShapeTerm vector +
          data.laplacian.meanCurvatureBracketTerm vector -
          data.laplacian.normalHessianTraceTerm vector -
          (2 : ℤ) • data.laplacian.mixedSecondFundamentalTerm vector -
          data.laplacian.ambientCurvatureNormalTerm vector)
    (hRicci : ccg25GaussRicciArbitraryCodimensionStatement data.ricci) :
    ∀ vector,
      data.ambientDeformation vector =
        data.intrinsicDeformation vector +
          data.laplacian.meanCurvatureBracketTerm vector -
          data.laplacian.normalHessianTraceTerm vector -
          data.laplacian.ambientCurvatureTangentialTraceTerm vector +
          data.normalDivergenceTangentialGradientTerm vector -
          (2 : ℤ) • data.laplacian.mixedSecondFundamentalTerm vector -
          data.laplacian.ambientCurvatureNormalTerm vector -
          data.laplacian.ambientRicciNormalTerm vector +
          data.ambientDivergenceNormalGradientTerm vector := by
  sorry

@[literature_terminal]
theorem ccg25_corollary_1_16_deformation_gauss
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) :
    ccg25DeformationGaussStatement data := by
  intro hDimension hCodimension
  have hBochner :=
    ccg25_theorem_1_1_bochner_gauss data.laplacian hDimension hCodimension
  have hRicci := ccg25_theorem_1_9_ricci_gauss data.ricci
  exact ccg25_corollary_1_16_deformation_from_bochner_and_ricci data
    hDimension hCodimension hBochner hRicci

/-- Corollary 1.18 is a direct simplification of Corollary 1.16 after both divergence-gradient terms vanish. -/
@[proof_assembly]
theorem ccg25_corollary_1_18_divergence_free_deformation
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) :
    ccg25DivergenceFreeDeformationGaussStatement data := by
  intro hDimension hCodimension vector hIntrinsic hAmbient
  have hFormula :=
    ccg25_corollary_1_16_deformation_gauss data hDimension hCodimension vector
  obtain ⟨hTangential, hNormal⟩ :=
    data.divergenceGradientTermsVanish vector hIntrinsic hAmbient
  simpa [hTangential, hNormal] using hFormula

/-- Corollary 1.20: add Theorem 1.9 to Theorem 1.1 through Weitzenbock to obtain the Hodge formula. -/
@[proof_obligation]
theorem ccg25_corollary_1_20_hodge_gauss
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector)
    (hDimension : 2 ≤ data.intrinsicDimension)
    (hCodimension : 1 ≤ data.codimension)
    (hBochner : ∀ vector,
      data.ambientBochner vector =
        data.intrinsicBochner vector + data.normalShapeSquareTerm vector -
          data.meanCurvatureShapeTerm vector + data.meanCurvatureBracketTerm vector -
          data.normalHessianTraceTerm vector -
          (2 : ℤ) • data.mixedSecondFundamentalTerm vector -
          data.ambientCurvatureNormalTerm vector) :
    ∀ vector,
      data.ambientHodge vector =
        data.intrinsicHodge vector + (2 : ℤ) • data.normalShapeSquareTerm vector -
          (2 : ℤ) • data.meanCurvatureShapeTerm vector +
          data.meanCurvatureBracketTerm vector - data.normalHessianTraceTerm vector -
          (2 : ℤ) • data.mixedSecondFundamentalTerm vector +
          data.ambientCurvatureTangentialTraceTerm vector -
          data.ambientCurvatureNormalTerm vector + data.ambientRicciNormalTerm vector := by
  sorry

/-- The full Bochner/Hodge family assembled without an aggregated extrinsic-correction placeholder. -/
@[literature_terminal]
theorem ccg25_theorem_1_1_and_corollary_1_20
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    ccg25LaplacianGaussFamilyStatement data := by
  intro hDimension hCodimension
  have hBochner := ccg25_theorem_1_1_bochner_gauss data hDimension hCodimension
  exact ⟨hBochner,
    ccg25_corollary_1_20_hodge_gauss data hDimension hCodimension hBochner⟩

/-- Corollary 1.21, equation (1.27): project Theorem 1.1 and use Gauss--Weingarten to identify the surviving tangential terms. -/
@[proof_obligation]
theorem ccg25_corollary_1_21_projected_bochner_from_gauss
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector)
    (hDimension : 2 ≤ data.laplacian.intrinsicDimension)
    (hCodimension : 1 ≤ data.laplacian.codimension)
    (hBochner : ∀ vector,
      data.laplacian.ambientBochner vector =
        data.laplacian.intrinsicBochner vector +
          data.laplacian.normalShapeSquareTerm vector -
          data.laplacian.meanCurvatureShapeTerm vector +
          data.laplacian.meanCurvatureBracketTerm vector -
          data.laplacian.normalHessianTraceTerm vector -
          (2 : ℤ) • data.laplacian.mixedSecondFundamentalTerm vector -
          data.laplacian.ambientCurvatureNormalTerm vector) :
    ∀ vector,
      data.tangentProjection (data.laplacian.ambientBochner vector) =
        data.laplacian.intrinsicBochner vector +
          data.laplacian.normalShapeSquareTerm vector +
          data.meanCurvatureTangentialDerivativeTerm vector -
          data.tangentProjection (data.laplacian.normalHessianTraceTerm vector) := by
  sorry

@[literature_terminal]
theorem ccg25_corollary_1_21_projected_laplacians
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) :
    ccg25ProjectedBochnerStatement data := by
  intro hDimension hCodimension
  have hBochner :=
    ccg25_theorem_1_1_bochner_gauss data.laplacian hDimension hCodimension
  exact ccg25_corollary_1_21_projected_bochner_from_gauss data hDimension
    hCodimension hBochner

/-- Corollary 1.24, equation (1.32), keeps the projection formula unchanged under Euclidean specialization. -/
@[proof_assembly]
theorem ccg25_corollary_1_24_euclidean_projected_laplacians
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) :
    ccg25EuclideanProjectedBochnerStatement data := by
  intro hEuclidean
  exact ccg25_corollary_1_21_projected_laplacians data

/-- The Euclidean codimension-two claim is the direct specialization of Theorem 1.9. -/
@[proof_obligation]
theorem ccg25_ricci_codimension_two_specialization
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25RicciData Vector)
    (hCodimension : data.codimension = 2)
    (hEuclidean : data.isEuclideanAmbient)
    (hRicci : ccg25GaussRicciArbitraryCodimensionStatement data) :
    ∀ vector,
      data.intrinsicRicci vector =
        data.meanCurvatureShapeTerm vector - data.normalShapeSquareTerm vector := by
  sorry

@[literature_terminal]
theorem ccg25_theorem_1_9_codimension_two
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25RicciData Vector)
    (hCodimension : data.codimension = 2)
    (hEuclidean : data.isEuclideanAmbient) :
    ccg25GaussRicciCodimensionTwoStatement data := by
  have hRicci := ccg25_theorem_1_9_ricci_gauss data
  exact ⟨hCodimension, hEuclidean,
    ccg25_ricci_codimension_two_specialization data hCodimension hEuclidean hRicci⟩


end RiemannianFluids
