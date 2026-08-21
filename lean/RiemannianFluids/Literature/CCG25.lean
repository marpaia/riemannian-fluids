import RiemannianFluids.Geometry.Submanifolds

/-!
# CCG25: Gauss formulas for Laplacians on submanifolds

The paper's arbitrary-codimension formulas contain long frame contractions.  The structures below
name each complete contracted term, while the proposition-valued source signatures retain every
coefficient and sign from Theorem 1.1 and Corollary 1.20.  An `Argument` represents a point,
tangent field, smooth ambient extension, and orthonormal tangent/normal frames satisfying the
paper's hypotheses; the values are pointwise tangent or ambient vectors in one common module.
-/

namespace RiemannianFluids.Literature.CCG25

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

end RiemannianFluids.Literature.CCG25
