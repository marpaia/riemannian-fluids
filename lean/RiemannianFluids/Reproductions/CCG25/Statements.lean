import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import RiemannianFluids.Geometry.Submanifolds
import RiemannianFluids.ProofStatus

/-!
# CCG25 statement contracts

Source: Chan--Czubak, *The Gauss formulas for Laplacians on submanifolds*,
arXiv:2212.11928v2, Theorem 1.1, Theorem 1.9, and the Laplacian corollaries.
-/

namespace RiemannianFluids

/-- Pointwise terms in the arbitrary-codimension Gauss formula for the Ricci operator. -/
structure CCG25RicciData (Vector : Type*) where
  codimension : ℕ
  isEuclideanAmbient : Prop
  intrinsicRicci : Vector → Vector
  ambientRicciTangential : Vector → Vector
  meanCurvatureShapeTerm : Vector → Vector
  normalShapeSquareTerm : Vector → Vector
  ambientMixedCurvatureTerm : Vector → Vector

/-- Theorem 1.9, equation (1.11), solved for the intrinsic Ricci operator. -/
def ccg25GaussRicciArbitraryCodimensionStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25RicciData Vector) : Prop :=
  1 ≤ data.codimension ∧
    ∀ vector,
      data.intrinsicRicci vector =
        data.ambientRicciTangential vector + data.meanCurvatureShapeTerm vector -
          data.normalShapeSquareTerm vector - data.ambientMixedCurvatureTerm vector

/-- The Euclidean codimension-two specialization of Theorem 1.9, equation (1.12). -/
def ccg25GaussRicciCodimensionTwoStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25RicciData Vector) : Prop :=
  data.codimension = 2 ∧
    data.isEuclideanAmbient ∧
    ∀ vector,
      data.intrinsicRicci vector =
        data.meanCurvatureShapeTerm vector - data.normalShapeSquareTerm vector

/-- Operator-valued terms in the paper's Gauss families for arbitrary intrinsic dimension and codimension. -/
structure CCG25LaplacianData (Vector : Type*) where
  intrinsicDimension : ℕ
  codimension : ℕ
  ambientBochner : Vector → Vector
  intrinsicBochner : Vector → Vector
  normalShapeSquareTerm : Vector → Vector
  meanCurvatureShapeTerm : Vector → Vector
  meanCurvatureBracketTerm : Vector → Vector
  normalHessianTraceTerm : Vector → Vector
  mixedSecondFundamentalTerm : Vector → Vector
  ambientCurvatureNormalTerm : Vector → Vector
  ambientCurvatureTangentialTraceTerm : Vector → Vector
  ambientRicciNormalTerm : Vector → Vector
  ambientHodge : Vector → Vector
  intrinsicHodge : Vector → Vector
  hasGaussAndWeingartenDefinitions : Prop
  hasNormalFrameDerivativeIdentity : Prop
  hasExtensionDerivativeSplitting : Prop
  hasOneFormCovariantDerivativeIdentity : Prop
  hasLieDerivativeComponentIdentity : Prop
  hasDefiningFunctionShapeIdentity : Prop
  hasFrameTraceIdentity : Prop
  hasInvariantMixedCurvatureTrace : Prop

/-- The two formulas in Corollary 1.7: contracted Codazzi in arbitrary codimension and its scalar hypersurface specialization. -/
structure CCG25CodazziData (TangentVector NormalVector : Type*) where
  laplacian : CCG25LaplacianData TangentVector
  contracted : ContractedCodazziData TangentVector NormalVector
  divergenceSecondFundamental : TangentVector → ℝ
  meanCurvatureDerivative : TangentVector → ℝ
  ambientRicciNormalPairing : TangentVector → ℝ

/-- Corollary 1.7, equations (1.9)--(1.10), without identifying the normal bundle with a single scalar outside codimension one. -/
def ccg25ContractedCodazziStatement
    {TangentVector NormalVector : Type*} [AddCommGroup NormalVector]
    (data : CCG25CodazziData TangentVector NormalVector) : Prop :=
  2 ≤ data.laplacian.intrinsicDimension →
    1 ≤ data.laplacian.codimension →
      HasContractedCodazziIdentity data.contracted ∧
        (data.laplacian.codimension = 1 →
          ∀ vector,
            data.divergenceSecondFundamental vector =
              (data.laplacian.intrinsicDimension : ℝ) *
                data.meanCurvatureDerivative vector -
                data.ambientRicciNormalPairing vector)

/-- Additional operators needed for Corollaries 1.12, 1.16, 1.18, 1.21, and 1.24. -/
structure CCG25DerivedLaplacianData (Vector : Type*) [Zero Vector] where
  laplacian : CCG25LaplacianData Vector
  ricci : CCG25RicciData Vector
  isEuclideanAmbient : Prop
  tangentProjection : Vector → Vector
  ambientDeformation : Vector → Vector
  intrinsicDeformation : Vector → Vector
  normalDivergenceTangentialGradientTerm : Vector → Vector
  ambientDivergenceNormalGradientTerm : Vector → Vector
  meanCurvatureTangentialDerivativeTerm : Vector → Vector
  isIntrinsicDivergenceFree : Vector → Prop
  isAmbientDivergenceFree : Vector → Prop
  euclideanCurvatureTermsVanish :
    isEuclideanAmbient → ∀ vector, laplacian.ambientCurvatureNormalTerm vector = 0
  divergenceGradientTermsVanish :
    ∀ vector,
      isIntrinsicDivergenceFree vector →
      isAmbientDivergenceFree vector →
        normalDivergenceTangentialGradientTerm vector = 0 ∧
          ambientDivergenceNormalGradientTerm vector = 0

/-- Corollary 1.12, equation (1.15): the Euclidean Bochner formula has no ambient-curvature term. -/
def ccg25EuclideanBochnerStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) : Prop :=
  2 ≤ data.laplacian.intrinsicDimension →
    1 ≤ data.laplacian.codimension →
      data.isEuclideanAmbient →
        ∀ vector,
          data.laplacian.ambientBochner vector =
            data.laplacian.intrinsicBochner vector +
              data.laplacian.normalShapeSquareTerm vector -
              data.laplacian.meanCurvatureShapeTerm vector +
              data.laplacian.meanCurvatureBracketTerm vector -
              data.laplacian.normalHessianTraceTerm vector -
              (2 : ℤ) • data.laplacian.mixedSecondFundamentalTerm vector

/-- Corollary 1.16, equation (1.21), with `E₁` and `N₁` expanded into their tangential, normal, curvature, and divergence pieces. -/
def ccg25DeformationGaussStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) : Prop :=
  2 ≤ data.laplacian.intrinsicDimension →
    1 ≤ data.laplacian.codimension →
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
            data.ambientDivergenceNormalGradientTerm vector

/-- Corollary 1.18: when both divergences vanish, the two divergence-gradient terms in (1.21) disappear. -/
def ccg25DivergenceFreeDeformationGaussStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) : Prop :=
  2 ≤ data.laplacian.intrinsicDimension →
    1 ≤ data.laplacian.codimension →
      ∀ vector,
        data.isIntrinsicDivergenceFree vector →
        data.isAmbientDivergenceFree vector →
          data.ambientDeformation vector =
            data.intrinsicDeformation vector +
              data.laplacian.meanCurvatureBracketTerm vector -
              data.laplacian.normalHessianTraceTerm vector -
              data.laplacian.ambientCurvatureTangentialTraceTerm vector -
              (2 : ℤ) • data.laplacian.mixedSecondFundamentalTerm vector -
              data.laplacian.ambientCurvatureNormalTerm vector -
              data.laplacian.ambientRicciNormalTerm vector

/-- Corollary 1.21, equation (1.27): tangential projection removes every normal-valued term from the Bochner formula. -/
def ccg25ProjectedBochnerStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) : Prop :=
  2 ≤ data.laplacian.intrinsicDimension →
    1 ≤ data.laplacian.codimension →
      ∀ vector,
        data.tangentProjection (data.laplacian.ambientBochner vector) =
          data.laplacian.intrinsicBochner vector +
            data.laplacian.normalShapeSquareTerm vector +
            data.meanCurvatureTangentialDerivativeTerm vector -
            data.tangentProjection (data.laplacian.normalHessianTraceTerm vector)

/-- Corollary 1.24, equation (1.32): the projected Bochner identity specialized to Euclidean submanifolds. -/
def ccg25EuclideanProjectedBochnerStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25DerivedLaplacianData Vector) : Prop :=
  data.isEuclideanAmbient → ccg25ProjectedBochnerStatement data

/-- Pointwise observables in Theorem 1.27 and Corollary 1.30 for a surface of revolution in `R³`. -/
structure CCG25SurfaceOfRevolutionData (Form : Type*) where
  preliminaries : CCG25LaplacianData Form
  isSurfaceOfRevolutionInR3 : Prop
  everyRadialLineIsTransverse : Prop
  isSurfaceDivergenceFree : Form → Prop
  isAmbientDivergenceFree : Form → Prop
  definingGradientNorm : ℝ
  firstPrincipalCurvature : ℝ
  secondPrincipalCurvature : ℝ
  meridionalGradientDerivative : ℝ
  normalGradientNormDerivative : ℝ
  restrictedAmbientHodge : Form → Form
  intrinsicHodge : Form → Form
  doubleNormalLie : Form → Form
  normalLie : Form → Form
  meridionalLie : Form → Form
  normalLieMeridionalComponent : Form → ℝ
  gradientLieMeridionalComponent : Form → ℝ
  meridionalComponent : Form → ℝ
  meridionalCovector : Form
  errorOperator : Form → Form
  weightedSecondGradientLie : Form → Form
  gradientLie : Form → Form
  hasCorollary1_24ProjectedIdentity : Prop
  hasProposition4_1ConnectionIdentities : Prop

/-- Theorem 1.27, equation (1.41), with both directional coefficients retained literally. -/
def ccg25SurfaceOfRevolutionLieFormulaStatement
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form) : Prop :=
  data.isSurfaceOfRevolutionInR3 →
    data.everyRadialLineIsTransverse →
    0 < data.definingGradientNorm →
      ∀ form,
        data.isSurfaceDivergenceFree form →
        data.isAmbientDivergenceFree form →
          data.restrictedAmbientHodge form =
            data.intrinsicHodge form - data.doubleNormalLie form +
              (data.firstPrincipalCurvature - data.secondPrincipalCurvature) •
                data.normalLie form +
              (1 / data.definingGradientNorm ^ 2) • data.meridionalLie form +
              (2 * (data.secondPrincipalCurvature - data.firstPrincipalCurvature) *
                  data.normalLieMeridionalComponent form -
                2 * (data.meridionalGradientDerivative /
                    data.definingGradientNorm) ^ 2 * data.meridionalComponent form) •
                data.meridionalCovector

/-- Corollary 1.30, equation (1.42), including the paper's explicit definition of the operator `E`. -/
def ccg25SurfaceOfRevolutionComparisonStatement
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form) : Prop :=
  data.isSurfaceOfRevolutionInR3 →
    data.everyRadialLineIsTransverse →
    0 < data.definingGradientNorm →
      (∀ form,
        data.errorOperator form =
          data.weightedSecondGradientLie form +
            ((data.firstPrincipalCurvature - data.secondPrincipalCurvature) /
                data.definingGradientNorm -
              data.normalGradientNormDerivative /
                data.definingGradientNorm ^ 2) • data.gradientLie form) ∧
      ∀ form,
        data.isSurfaceDivergenceFree form →
        data.isAmbientDivergenceFree form →
          data.restrictedAmbientHodge form =
            data.intrinsicHodge form + data.errorOperator form +
              (1 / data.definingGradientNorm ^ 2) • data.meridionalLie form +
              (2 / data.definingGradientNorm *
                (data.secondPrincipalCurvature - data.firstPrincipalCurvature) *
                data.gradientLieMeridionalComponent form) • data.meridionalCovector

/-- Equations (1.5) and Corollary 1.20 with every normal-connection and curvature term exposed. -/
def ccg25LaplacianGaussFamilyStatement
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) : Prop :=
  2 ≤ data.intrinsicDimension →
    1 ≤ data.codimension →
    (∀ vector,
      data.ambientBochner vector =
        data.intrinsicBochner vector + data.normalShapeSquareTerm vector -
          data.meanCurvatureShapeTerm vector + data.meanCurvatureBracketTerm vector -
          data.normalHessianTraceTerm vector -
          (2 : ℤ) • data.mixedSecondFundamentalTerm vector -
          data.ambientCurvatureNormalTerm vector) ∧
    ∀ vector,
      data.ambientHodge vector =
        data.intrinsicHodge vector + (2 : ℤ) • data.normalShapeSquareTerm vector -
          (2 : ℤ) • data.meanCurvatureShapeTerm vector +
          data.meanCurvatureBracketTerm vector - data.normalHessianTraceTerm vector -
          (2 : ℤ) • data.mixedSecondFundamentalTerm vector +
          data.ambientCurvatureTangentialTraceTerm vector -
          data.ambientCurvatureNormalTerm vector + data.ambientRicciNormalTerm vector


end RiemannianFluids
