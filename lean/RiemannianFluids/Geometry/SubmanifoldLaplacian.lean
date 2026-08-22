import RiemannianFluids.Geometry.SubmanifoldGauss

/-!
# Pointwise Gauss--Weingarten trace for the Bochner Laplacian

This file formalizes the contraction at the heart of CCG25 Theorem 1.1.  A pointwise jet records
the primitive objects produced by differentiating the Gauss and Weingarten formulas in an
adapted orthonormal frame: the intrinsic Hessian, `II`, the first derivative of the tangent field,
the normal derivative of `II`, and the two normal-direction ambient Hessian terms.  The ambient
Bochner value is constructed from those primitives.

The two output formulas are then theorems.  The first trace theorem proves formula (1.6)
algebraically.  Contracted Codazzi and the bracket--Weingarten identity convert it into formula
(1.5).  In particular, neither displayed CCG25 conclusion is stored in the jet.
-/

namespace RiemannianFluids

open Bundle
open scoped BigOperators Bundle ContDiff Manifold

noncomputable section

section PointwiseBochner

variable
  {ι κ Tangent Normal Ambient : Type*}
  [Fintype ι] [Fintype κ]
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [FiniteDimensional ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
  [FiniteDimensional ℝ Normal]
  [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

/-- The primitive pointwise two-jet entering the differentiated Gauss--Weingarten calculation.
The tangent and normal lifts allow the result to live in any ambient module, including an actual
ambient tangent fiber. -/
structure PointwiseBochnerGaussJet where
  tangentFrame : OrthonormalBasis ι ℝ Tangent
  normalFrame : OrthonormalBasis κ ℝ Normal
  tangentLift : Tangent →L[ℝ] Ambient
  normalLift : Normal →L[ℝ] Ambient
  field : Tangent
  secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal
  firstDerivative : Tangent →L[ℝ] Tangent
  intrinsicSecondDerivative : Tangent →L[ℝ] Tangent →L[ℝ] Tangent
  normalDerivativeSecondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal
  ambientNormalDerivative : Normal →L[ℝ] Ambient
  ambientNormalSecondDerivative : Normal →L[ℝ] Normal →L[ℝ] Ambient
  ambientNormalAccelerationDerivative : Normal →L[ℝ] Normal →L[ℝ] Ambient
  meanBracket : Ambient
  meanNormalDerivative : Normal
  ambientCurvatureNormalTrace : Normal

/-- A tensorial version of the differentiated Gauss--Weingarten jet.  Instead of storing the
contracted Codazzi terms independently, it stores the full covariant derivative `∇ᴮ II` and the
normal projection of ambient curvature.  The field-specific Bochner jet and its contractions are
constructed below. -/
structure PointwiseDifferentiatedGaussWeingartenJet where
  tangentFrame : OrthonormalBasis ι ℝ Tangent
  normalFrame : OrthonormalBasis κ ℝ Normal
  tangentLift : Tangent →L[ℝ] Ambient
  normalLift : Normal →L[ℝ] Ambient
  field : Tangent
  secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal
  firstDerivative : Tangent →L[ℝ] Tangent
  intrinsicSecondDerivative : Tangent →L[ℝ] Tangent →L[ℝ] Tangent
  covariantDerivativeSecondFundamental :
    Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Normal
  ambientNormalCurvature :
    Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Normal
  ambientNormalDerivative : Normal →L[ℝ] Ambient
  ambientNormalSecondDerivative : Normal →L[ℝ] Normal →L[ℝ] Ambient
  ambientNormalAccelerationDerivative : Normal →L[ℝ] Normal →L[ℝ] Ambient
  meanBracket : Ambient

/-- Symmetry of `∇ᴮ II` in its two second-fundamental-form arguments. -/
def PointwiseDifferentiatedGaussWeingartenJet.IsSymmetricDerivative
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) : Prop :=
  ∀ direction first second,
    jet.covariantDerivativeSecondFundamental direction first second =
      jet.covariantDerivativeSecondFundamental direction second first

/-- The uncontracted normal Codazzi equation in the CCG25 convention
`(R̃(W,X)Y)⊥ = (∇ᴮ_W II)(X,Y) - (∇ᴮ_X II)(W,Y)`. -/
def PointwiseDifferentiatedGaussWeingartenJet.HasCodazziEquation
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) : Prop :=
  ∀ first second field,
    jet.ambientNormalCurvature first second field =
      jet.covariantDerivativeSecondFundamental first second field -
        jet.covariantDerivativeSecondFundamental second first field

/-- The derivative of the normal field `II(second, field)` is the tensorial derivative of `II`
plus the derivative of the fixed tangent field.  This is the field-specific bilinear term used
by the Bochner trace. -/
def PointwiseDifferentiatedGaussWeingartenJet.normalDerivativeSecondFundamental
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Tangent →L[ℝ] Tangent →L[ℝ] Normal :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ LinearMap.toContinuousLinearMap {
      toFun := fun second ↦
        jet.covariantDerivativeSecondFundamental first second jet.field +
          jet.secondFundamental second (jet.firstDerivative first)
      map_add' := by
        intro second second'
        simp
        abel
      map_smul' := by
        intro scalar second
        simp [smul_add] }
    map_add' := by
      intro first first'
      ext second
      simp
      abel
    map_smul' := by
      intro scalar first
      ext second
      simp [smul_add] }

/-- The normal derivative of mean curvature obtained by differentiating the normalized trace of
`II` with the metric connection. -/
def PointwiseDifferentiatedGaussWeingartenJet.meanNormalDerivative
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) : Normal :=
  (Fintype.card ι : ℝ)⁻¹ •
    ∑ i, jet.covariantDerivativeSecondFundamental jet.field
      (jet.tangentFrame i) (jet.tangentFrame i)

/-- The normal ambient-curvature term occurring in the contracted Codazzi equation. -/
def PointwiseDifferentiatedGaussWeingartenJet.ambientCurvatureNormalTrace
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) : Normal :=
  ∑ i, jet.ambientNormalCurvature (jet.tangentFrame i) jet.field (jet.tangentFrame i)

/-- Forget the full differentiated tensors after constructing every field-specific term of the
Bochner Gauss jet from them. -/
def PointwiseDifferentiatedGaussWeingartenJet.toPointwiseBochnerGaussJet
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient) where
  tangentFrame := jet.tangentFrame
  normalFrame := jet.normalFrame
  tangentLift := jet.tangentLift
  normalLift := jet.normalLift
  field := jet.field
  secondFundamental := jet.secondFundamental
  firstDerivative := jet.firstDerivative
  intrinsicSecondDerivative := jet.intrinsicSecondDerivative
  normalDerivativeSecondFundamental := jet.normalDerivativeSecondFundamental
  ambientNormalDerivative := jet.ambientNormalDerivative
  ambientNormalSecondDerivative := jet.ambientNormalSecondDerivative
  ambientNormalAccelerationDerivative := jet.ambientNormalAccelerationDerivative
  meanBracket := jet.meanBracket
  meanNormalDerivative := jet.meanNormalDerivative
  ambientCurvatureNormalTrace := jet.ambientCurvatureNormalTrace

/-- Tangent trace of the intrinsic second derivative. -/
def PointwiseBochnerGaussJet.intrinsicSecondTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Tangent :=
  ∑ i, jet.intrinsicSecondDerivative (jet.tangentFrame i) (jet.tangentFrame i)

/-- Unnormalized mean-curvature trace `Σ_i II(E_i,E_i)`. -/
def PointwiseBochnerGaussJet.secondFundamentalTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Normal :=
  ∑ i, jet.secondFundamental (jet.tangentFrame i) (jet.tangentFrame i)

/-- The contraction `Σ_i II(E_i,∇_{E_i}v)`. -/
def PointwiseBochnerGaussJet.secondFundamentalDerivativeTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Normal :=
  ∑ i, jet.secondFundamental (jet.tangentFrame i)
    (jet.firstDerivative (jet.tangentFrame i))

/-- The contraction of `∇⊥(II(·,v))` in a geodesic tangent frame. -/
def PointwiseBochnerGaussJet.normalDerivativeTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Normal :=
  ∑ i,
    jet.normalDerivativeSecondFundamental (jet.tangentFrame i) (jet.tangentFrame i)

/-- The traced covariant derivative `(tr ∇ᴮ II)(v)` in a geodesic tangent frame. -/
def PointwiseBochnerGaussJet.covariantDerivativeSecondFundamentalTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Normal :=
  jet.normalDerivativeTrace - jet.secondFundamentalDerivativeTrace

/-- The normal-direction second-derivative trace. -/
def PointwiseBochnerGaussJet.normalSecondDerivativeTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  ∑ l, jet.ambientNormalSecondDerivative (jet.normalFrame l) (jet.normalFrame l)

/-- The normal-acceleration derivative trace. -/
def PointwiseBochnerGaussJet.normalAccelerationDerivativeTrace
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  ∑ l,
    jet.ambientNormalAccelerationDerivative (jet.normalFrame l) (jet.normalFrame l)

/-- The intrinsic analysis-positive Bochner value, lifted to the ambient fiber. -/
def PointwiseBochnerGaussJet.intrinsicBochner
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.tangentLift (-jet.intrinsicSecondTrace)

/-- The normal-frame shape-square term, lifted to the ambient fiber. -/
def PointwiseBochnerGaussJet.normalShapeSquare
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.tangentLift
    (RiemannianFluids.normalShapeSquare jet.normalFrame jet.secondFundamental jet.field)

/-- The shape operator of vectorial mean curvature, applied to the field. -/
def PointwiseBochnerGaussJet.meanShape
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.tangentLift
    (shapeOperatorOfSecondFundamental jet.secondFundamental
      (meanCurvatureOfSecondFundamental jet.tangentFrame jet.secondFundamental) jet.field)

/-- The ambient derivative `\widetilde∇_H v`. -/
def PointwiseBochnerGaussJet.meanDerivative
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.ambientNormalDerivative
    (meanCurvatureOfSecondFundamental jet.tangentFrame jet.secondFundamental)

/-- The CCG25 curvature trace, lifted from the normal fiber. -/
def PointwiseBochnerGaussJet.ambientCurvatureNormalTraceValue
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.normalLift jet.ambientCurvatureNormalTrace

/-- The `II(E_i,∇_{E_i}v)` trace, lifted from the normal fiber. -/
def PointwiseBochnerGaussJet.secondFundamentalDerivativeTraceValue
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.normalLift jet.secondFundamentalDerivativeTrace

/-- The `(tr ∇ᴮ II)(v)` trace, lifted from the normal fiber. -/
def PointwiseBochnerGaussJet.codazziTraceValue
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.normalLift jet.covariantDerivativeSecondFundamentalTrace

/-- The ambient Bochner value obtained by tracing the differentiated Gauss--Weingarten
decomposition over the adapted tangent and normal frames. -/
def PointwiseBochnerGaussJet.ambientBochner
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Ambient :=
  jet.tangentLift
      (-jet.intrinsicSecondTrace +
        ∑ i,
          shapeOperatorOfSecondFundamental jet.secondFundamental
            (jet.secondFundamental (jet.tangentFrame i) jet.field)
            (jet.tangentFrame i)) +
    jet.normalLift
      (-(jet.secondFundamentalDerivativeTrace + jet.normalDerivativeTrace)) +
    jet.ambientNormalDerivative jet.secondFundamentalTrace -
    jet.normalSecondDerivativeTrace +
    jet.normalAccelerationDerivativeTrace

/-- Contracted Codazzi in the geodesic-frame trace used by the jet. -/
def PointwiseBochnerGaussJet.HasContractedCodazzi
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Prop :=
  jet.covariantDerivativeSecondFundamentalTrace =
    (Fintype.card ι : ℝ) • jet.meanNormalDerivative +
      jet.ambientCurvatureNormalTrace

omit [FiniteDimensional ℝ Normal] in
/-- For a tensorial differentiated jet, the field-specific trace stored by the Bochner jet is
exactly `Σ_i (∇ᴮ_{E_i} II)(E_i,v)`. -/
theorem PointwiseDifferentiatedGaussWeingartenJet.toPointwiseBochnerGaussJet_covariantTrace
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    jet.toPointwiseBochnerGaussJet.covariantDerivativeSecondFundamentalTrace =
      ∑ i, jet.covariantDerivativeSecondFundamental
        (jet.tangentFrame i) (jet.tangentFrame i) jet.field := by
  rw [PointwiseBochnerGaussJet.covariantDerivativeSecondFundamentalTrace,
    PointwiseBochnerGaussJet.normalDerivativeTrace,
    PointwiseBochnerGaussJet.secondFundamentalDerivativeTrace]
  simp only [PointwiseDifferentiatedGaussWeingartenJet.toPointwiseBochnerGaussJet,
    PointwiseDifferentiatedGaussWeingartenJet.normalDerivativeSecondFundamental]
  change
    (∑ i, (jet.covariantDerivativeSecondFundamental
          (jet.tangentFrame i) (jet.tangentFrame i) jet.field +
        jet.secondFundamental (jet.tangentFrame i)
          (jet.firstDerivative (jet.tangentFrame i)))) -
      ∑ i, jet.secondFundamental (jet.tangentFrame i)
        (jet.firstDerivative (jet.tangentFrame i)) =
      ∑ i, jet.covariantDerivativeSecondFundamental
        (jet.tangentFrame i) (jet.tangentFrame i) jet.field
  rw [Finset.sum_add_distrib]
  abel

omit [FiniteDimensional ℝ Normal] in
/-- Contracting the uncontracted Codazzi equation proves the Bochner jet's contracted Codazzi
identity.  Thus the CCG25 trace formula no longer needs contracted Codazzi as an independent
primitive once `∇ᴮ II` and normal ambient curvature have been constructed. -/
theorem PointwiseDifferentiatedGaussWeingartenJet.hasContractedCodazzi
    [Nonempty ι]
    (jet : PointwiseDifferentiatedGaussWeingartenJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : jet.IsSymmetricDerivative)
    (codazzi : jet.HasCodazziEquation) :
    jet.toPointwiseBochnerGaussJet.HasContractedCodazzi := by
  rw [PointwiseBochnerGaussJet.HasContractedCodazzi,
    jet.toPointwiseBochnerGaussJet_covariantTrace]
  change
    (∑ i, jet.covariantDerivativeSecondFundamental
      (jet.tangentFrame i) (jet.tangentFrame i) jet.field) =
      (Fintype.card ι : ℝ) •
          ((Fintype.card ι : ℝ)⁻¹ •
            ∑ i, jet.covariantDerivativeSecondFundamental jet.field
              (jet.tangentFrame i) (jet.tangentFrame i)) +
        ∑ i, jet.ambientNormalCurvature
          (jet.tangentFrame i) jet.field (jet.tangentFrame i)
  have tracedCodazzi :
      (∑ i, jet.covariantDerivativeSecondFundamental
        (jet.tangentFrame i) (jet.tangentFrame i) jet.field) =
        ∑ i,
          (jet.covariantDerivativeSecondFundamental jet.field
              (jet.tangentFrame i) (jet.tangentFrame i) +
            jet.ambientNormalCurvature
              (jet.tangentFrame i) jet.field (jet.tangentFrame i)) := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      jet.covariantDerivativeSecondFundamental
          (jet.tangentFrame i) (jet.tangentFrame i) jet.field =
        jet.covariantDerivativeSecondFundamental
          (jet.tangentFrame i) jet.field (jet.tangentFrame i) :=
        symmetric (jet.tangentFrame i) (jet.tangentFrame i) jet.field
      _ = jet.covariantDerivativeSecondFundamental jet.field
            (jet.tangentFrame i) (jet.tangentFrame i) +
          jet.ambientNormalCurvature
            (jet.tangentFrame i) jet.field (jet.tangentFrame i) := by
        rw [codazzi (jet.tangentFrame i) jet.field (jet.tangentFrame i)]
        abel
  rw [tracedCodazzi, Finset.sum_add_distrib]
  have card_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [smul_smul, mul_inv_cancel₀ card_ne, one_smul]

/-- The bracket identity obtained from torsion-freeness and Weingarten:
`∇̃_H v - ∇⊥_v H = [H,v] - W_H v`. -/
def PointwiseBochnerGaussJet.HasMeanBracketWeingarten
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Prop :=
  jet.meanDerivative - jet.normalLift jet.meanNormalDerivative =
    jet.meanBracket - jet.meanShape

/-- The paired CCG25 Bochner Gauss formulas (1.5)--(1.6) for one pointwise jet. -/
def PointwiseBochnerGaussJet.HasGaussFormulas
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Prop :=
  jet.ambientBochner =
      jet.intrinsicBochner + jet.normalShapeSquare -
        (Fintype.card ι : ℝ) • jet.meanShape +
        (Fintype.card ι : ℝ) • jet.meanBracket -
        jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue -
        jet.ambientCurvatureNormalTraceValue ∧
    jet.ambientBochner =
      jet.intrinsicBochner + jet.normalShapeSquare +
        (Fintype.card ι : ℝ) • jet.meanDerivative -
        jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
        jet.codazziTraceValue -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue

/-- The differentiated Gauss--Weingarten trace proves CCG25 equation (1.6). -/
theorem PointwiseBochnerGaussJet.ambientBochner_eq_secondGaussFormula
    [Nonempty ι]
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : ∀ first second,
      jet.secondFundamental first second = jet.secondFundamental second first) :
    jet.ambientBochner =
      jet.intrinsicBochner + jet.normalShapeSquare +
        (Fintype.card ι : ℝ) • jet.meanDerivative -
        jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
        jet.codazziTraceValue -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue := by
  rw [PointwiseBochnerGaussJet.ambientBochner,
    PointwiseBochnerGaussJet.intrinsicBochner,
    PointwiseBochnerGaussJet.normalShapeSquare,
    PointwiseBochnerGaussJet.meanDerivative,
    PointwiseBochnerGaussJet.secondFundamentalTrace,
    PointwiseBochnerGaussJet.codazziTraceValue,
    PointwiseBochnerGaussJet.covariantDerivativeSecondFundamentalTrace,
    PointwiseBochnerGaussJet.secondFundamentalDerivativeTraceValue,
    sum_shape_secondFundamental_eq_normalShapeSquare
      jet.tangentFrame jet.normalFrame jet.secondFundamental symmetric jet.field,
    card_smul_map_meanCurvature
      jet.tangentFrame jet.secondFundamental jet.ambientNormalDerivative]
  simp only [map_add, map_neg, map_sub]
  module

/-- Contracted Codazzi and the bracket--Weingarten identity convert equation (1.6) into CCG25
equation (1.5). -/
theorem PointwiseBochnerGaussJet.ambientBochner_eq_firstGaussFormula
    [Nonempty ι]
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient))
    (symmetric : ∀ first second,
      jet.secondFundamental first second = jet.secondFundamental second first)
    (codazzi : jet.HasContractedCodazzi)
    (bracketWeingarten : jet.HasMeanBracketWeingarten) :
    jet.ambientBochner =
      jet.intrinsicBochner + jet.normalShapeSquare -
        (Fintype.card ι : ℝ) • jet.meanShape +
        (Fintype.card ι : ℝ) • jet.meanBracket -
        jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue -
        jet.ambientCurvatureNormalTraceValue := by
  rw [jet.ambientBochner_eq_secondGaussFormula symmetric]
  have codazziLift : jet.codazziTraceValue =
      (Fintype.card ι : ℝ) • jet.normalLift jet.meanNormalDerivative +
        jet.ambientCurvatureNormalTraceValue := by
    rw [PointwiseBochnerGaussJet.codazziTraceValue,
      PointwiseBochnerGaussJet.ambientCurvatureNormalTraceValue, codazzi]
    simp
  rw [codazziLift]
  have meanConversion :
      (Fintype.card ι : ℝ) • jet.meanDerivative -
          ((Fintype.card ι : ℝ) • jet.normalLift jet.meanNormalDerivative +
            jet.ambientCurvatureNormalTraceValue) =
        -(Fintype.card ι : ℝ) • jet.meanShape +
          (Fintype.card ι : ℝ) • jet.meanBracket -
          jet.ambientCurvatureNormalTraceValue := by
    calc
      _ = (Fintype.card ι : ℝ) •
            (jet.meanDerivative - jet.normalLift jet.meanNormalDerivative) -
          jet.ambientCurvatureNormalTraceValue := by module
      _ = (Fintype.card ι : ℝ) •
            (jet.meanBracket - jet.meanShape) -
          jet.ambientCurvatureNormalTraceValue := by rw [bracketWeingarten]
      _ = _ := by module
  calc
    jet.intrinsicBochner + jet.normalShapeSquare +
              (Fintype.card ι : ℝ) • jet.meanDerivative -
            jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
          ((Fintype.card ι : ℝ) • jet.normalLift jet.meanNormalDerivative +
            jet.ambientCurvatureNormalTraceValue) -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue =
      jet.intrinsicBochner + jet.normalShapeSquare +
          ((Fintype.card ι : ℝ) • jet.meanDerivative -
            ((Fintype.card ι : ℝ) • jet.normalLift jet.meanNormalDerivative +
              jet.ambientCurvatureNormalTraceValue)) -
        jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue := by module
    _ = jet.intrinsicBochner + jet.normalShapeSquare +
          (-(Fintype.card ι : ℝ) • jet.meanShape +
            (Fintype.card ι : ℝ) • jet.meanBracket -
            jet.ambientCurvatureNormalTraceValue) -
        jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
        (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue := by
          rw [meanConversion]
    _ = _ := by module

end PointwiseBochner

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

/-- A Bochner Gauss jet whose three vector spaces are the intrinsic tangent fiber, the kernel
normal fiber, and the ambient tangent fiber of a concrete Mathlib-backed immersion. -/
abbrev SubmanifoldBochnerGaussJetAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M) :=
  PointwiseBochnerGaussJet
    (ι := ι) (κ := κ)
    (Tangent := TangentSpace I x)
    (Normal := SubmanifoldNormalSpaceAt immersion splitting x)
    (Ambient := TangentSpace I' (immersion.toFun x))

/-- A differentiated Gauss--Weingarten jet on the actual tangent, kernel-normal, and ambient
fibers of an immersion. -/
abbrev SubmanifoldDifferentiatedGaussWeingartenJetAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M) :=
  PointwiseDifferentiatedGaussWeingartenJet
    (ι := ι) (κ := κ)
    (Tangent := TangentSpace I x)
    (Normal := SubmanifoldNormalSpaceAt immersion splitting x)
    (Ambient := TangentSpace I' (immersion.toFun x))

/-- Construct the differentiated actual-fiber jet with canonical tangent lift `df_x` and
canonical inclusion of the kernel-normal fiber. -/
def submanifoldDifferentiatedGaussWeingartenJetAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x))
    (field : TangentSpace I x)
    (secondFundamental : SubmanifoldSecondFundamentalFormAt immersion splitting x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (covariantDerivativeSecondFundamental :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x)
    (ambientNormalCurvature :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x)
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    SubmanifoldDifferentiatedGaussWeingartenJetAt
      (ι := ι) (κ := κ) immersion splitting x where
  tangentFrame := tangentFrame
  normalFrame := normalFrame
  tangentLift := mfderiv I I' immersion.toFun x
  normalLift := (LinearMap.ker (splitting.tangentProjection x).toLinearMap).subtypeL
  field := field
  secondFundamental := secondFundamental
  firstDerivative := firstDerivative
  intrinsicSecondDerivative := intrinsicSecondDerivative
  covariantDerivativeSecondFundamental := covariantDerivativeSecondFundamental
  ambientNormalCurvature := ambientNormalCurvature
  ambientNormalDerivative := ambientNormalDerivative
  ambientNormalSecondDerivative := ambientNormalSecondDerivative
  ambientNormalAccelerationDerivative := ambientNormalAccelerationDerivative
  meanBracket := meanBracket

/-- Specialize the actual-fiber differentiated jet so its normal curvature is necessarily the
normal projection of one supplied ambient connection's curvature tensor. -/
def connectionSubmanifoldDifferentiatedGaussWeingartenJetAt
    [IsManifold I' 3 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x))
    (field : TangentSpace I x)
    (secondFundamental : SubmanifoldSecondFundamentalFormAt immersion splitting x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (covariantDerivativeSecondFundamental :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x)
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    SubmanifoldDifferentiatedGaussWeingartenJetAt
      (ι := ι) (κ := κ) immersion splitting x :=
  submanifoldDifferentiatedGaussWeingartenJetAt immersion splitting x tangentFrame normalFrame
    field secondFundamental firstDerivative intrinsicSecondDerivative
    covariantDerivativeSecondFundamental
    (normalAmbientConnectionCurvatureAt immersion splitting ambientConnection decomposition
      leftInverse x ambientRegular)
    ambientNormalDerivative ambientNormalSecondDerivative ambientNormalAccelerationDerivative
    meanBracket

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem connectionSubmanifoldDifferentiatedGaussWeingartenJetAt_ambientNormalCurvature
    [IsManifold I' 3 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x))
    (field : TangentSpace I x)
    (secondFundamental : SubmanifoldSecondFundamentalFormAt immersion splitting x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (covariantDerivativeSecondFundamental :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x)
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    (connectionSubmanifoldDifferentiatedGaussWeingartenJetAt immersion splitting
      ambientConnection decomposition leftInverse x ambientRegular tangentFrame normalFrame
      field secondFundamental firstDerivative intrinsicSecondDerivative
      covariantDerivativeSecondFundamental ambientNormalDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative meanBracket).ambientNormalCurvature =
        normalAmbientConnectionCurvatureAt immersion splitting ambientConnection decomposition
          leftInverse x ambientRegular :=
  rfl

/-- Differentiate the canonical ambient extension of a tangent-fiber vector in an actual normal
direction.  This constructs the normal-direction first derivative used by the CCG25 trace. -/
def ambientNormalDerivativeOfCanonicalTangentFieldAt
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (x : M) (field : TangentSpace I x) :
    SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
      TangentSpace I' (immersion.toFun x) :=
  (ambientConnection
    (extensions.toSubmanifoldFieldExtensionData.tangentExtension
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field))
    (immersion.toFun x)).comp
      (LinearMap.ker (splitting.tangentProjection x).toLinearMap).subtypeL

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
@[simp]
theorem ambientNormalDerivativeOfCanonicalTangentFieldAt_apply
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (x : M) (field : TangentSpace I x)
    (normal : SubmanifoldNormalSpaceAt immersion splitting x) :
    ambientNormalDerivativeOfCanonicalTangentFieldAt immersion splitting ambientConnection
        extensions x field normal =
      ambientConnection
        (extensions.toSubmanifoldFieldExtensionData.tangentExtension
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field))
        (immersion.toFun x) normal :=
  rfl

/-- The actual ambient Lie bracket between a chosen normal field along the immersion (after its
ambient extension) and the canonical ambient extension of a tangent-fiber vector. -/
def ambientBracketOfNormalAndCanonicalTangentFieldAt
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (x : M) (field : TangentSpace I x)
    (normal : AmbientVectorFieldAlong immersion) :
    TangentSpace I' (immersion.toFun x) :=
  VectorField.mlieBracket I'
    (extensions.toSubmanifoldFieldExtensionData.alongExtension normal)
    (extensions.toSubmanifoldFieldExtensionData.tangentExtension
      (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field))
    (immersion.toFun x)

/-- The single-source differentiated Gauss--Weingarten jet for a boundaryless isometric
immersion.  Its second fundamental form, covariant derivative of `II`, and normal ambient
curvature are all constructed from the same immersion, ambient Levi--Civita connection, and
extension operator.  Only the field-specific first/second derivatives and normal-direction
ambient jets remain explicit analytic inputs. -/
def inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
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
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
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
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    SubmanifoldDifferentiatedGaussWeingartenJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x :=
  connectionSubmanifoldDifferentiatedGaussWeingartenJetAt
    immersion.toSmoothImmersionData immersion.orthogonalSplitting
    ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
    immersion.hasTangentProjectionLeftInverse x ambientRegular tangentFrame normalFrame field
    (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x)
    firstDerivative intrinsicSecondDerivative
    (projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita extensions
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      x intrinsicRegular extensionRegular)
    ambientNormalDerivative ambientNormalSecondDerivative
    ambientNormalAccelerationDerivative meanBracket

/-- The single-source differentiated jet inherits the geometrically proved symmetry of
`∇ᴮ II`; symmetry is not supplied by the caller. -/
theorem inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_isSymmetricDerivative
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
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
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
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
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalDerivative ambientNormalSecondDerivative
      ambientNormalAccelerationDerivative meanBracket).IsSymmetricDerivative := by
  intro direction first second
  change projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita extensions
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      x intrinsicRegular extensionRegular direction first second =
    projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita extensions
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      x intrinsicRegular extensionRegular direction second first
  exact projectedCovariantDerivativeSecondFundamentalAt_comm immersion ambientLeviCivita
    extensions x intrinsicRegular extensionRegular direction first second

/-- The single-source differentiated jet satisfies the uncontracted normal Codazzi equation;
the equation is inherited from the differentiated Gauss formula for the same immersion and
connection, not accepted as jet data. -/
theorem inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_hasCodazziEquation
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
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
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
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
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalDerivative ambientNormalSecondDerivative
      ambientNormalAccelerationDerivative meanBracket).HasCodazziEquation := by
  intro first second test
  change normalAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      x ambientRegular first second test =
    projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita extensions
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x intrinsicRegular extensionRegular first second test -
      projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita extensions
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x intrinsicRegular extensionRegular second first test
  exact normalAmbientConnectionCurvatureAt_eq_projectedCovariantDerivativeSecondFundamental_sub
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    first second test

/-- Contracted Codazzi for the actual-fiber differentiated jet, obtained by tracing the proved
uncontracted equation and the proved symmetry of `∇ᴮ II`. -/
theorem inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_hasContractedCodazzi
    [Nonempty ι]
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
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
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
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
    (meanBracket : TangentSpace I' (immersion.toFun x)) :
    PointwiseBochnerGaussJet.HasContractedCodazzi
      ((inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative meanBracket).toPointwiseBochnerGaussJet) := by
  let jet := inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
    ambientNormalDerivative ambientNormalSecondDerivative
    ambientNormalAccelerationDerivative meanBracket
  exact jet.hasContractedCodazzi
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_isSymmetricDerivative
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalDerivative ambientNormalSecondDerivative
      ambientNormalAccelerationDerivative meanBracket)
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_hasCodazziEquation
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalDerivative ambientNormalSecondDerivative
      ambientNormalAccelerationDerivative meanBracket)

/-- Mean curvature in the actual kernel-normal fiber, constructed from the immersion's projected
second fundamental form and a tangent orthonormal frame. -/
def inducedLeviCivitaSubmanifoldMeanCurvatureAt
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M) (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
  meanCurvatureOfSecondFundamental tangentFrame
    (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x)

/-- The tensorial normal derivative of mean curvature in the field direction, obtained by
tracing the geometrically constructed `∇ᴮ II`. -/
def inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse) x)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (field : TangentSpace I x) :
    SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
  (Fintype.card ι : ℝ)⁻¹ •
    ∑ i, projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita extensions
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      x intrinsicRegular extensionRegular field (tangentFrame i) (tangentFrame i)

/-- Torsion-freeness and the constructed Weingarten formula prove the CCG25 mean-bracket
identity from an actual normal field realizing the value and normal derivative of mean curvature
at the base point.  The hypotheses describe that first-order realization and its regularity;
they do not assume the bracket identity. -/
theorem ambientNormalDerivative_sub_meanNormalDerivative_eq_bracket_sub_meanShape
    [IsManifold I 3 M] [IsManifold I' 3 N]
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
      (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse) x)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (field : TangentSpace I x)
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
    ambientNormalDerivativeOfCanonicalTangentFieldAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection extensions x field
          (inducedLeviCivitaSubmanifoldMeanCurvatureAt immersion ambientLeviCivita
            extensions x tangentFrame) -
        (inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt immersion ambientLeviCivita
          extensions x intrinsicRegular extensionRegular tangentFrame field :
            TangentSpace I' (immersion.toFun x)) =
      ambientBracketOfNormalAndCanonicalTangentFieldAt immersion.toSmoothImmersionData
          extensions x field normal -
        mfderiv I I' immersion.toFun x
          (shapeOperatorOfSecondFundamental
            (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
              immersion.hasTangentProjectionLeftInverse x)
            (inducedLeviCivitaSubmanifoldMeanCurvatureAt immersion ambientLeviCivita
              extensions x tangentFrame) field) := by
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  let meanNormal :=
    inducedLeviCivitaSubmanifoldMeanCurvatureAt immersion ambientLeviCivita
      extensions x tangentFrame
  let meanNormalDerivative :=
    inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt immersion ambientLeviCivita
      extensions x intrinsicRegular extensionRegular tangentFrame field
  let fieldExtension :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field
  let ambientField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldExtension
  let ambientNormal :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension normal
  let shapeAlong :=
    extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection fieldExtension normal x
  have hfield : MDiffAt (T% fieldExtension) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x field
  have hambientField : MDiffAt (T% ambientField) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hfield
  have normalOrthogonal : ∀ y tangent,
      inner ℝ (normal y) (mfderiv I I' immersion.toFun y tangent) = 0 := by
    intro y tangent
    exact (immersion.mem_normalSpace_iff y (normal y)).mp (normal_mem y) tangent
  have shapeEquality :
      shapeOperatorOfSecondFundamental pointII meanNormal field = shapeAlong := by
    apply ext_inner_right ℝ
    intro test
    let testField :=
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x test
    have shapePairing := shapeOperatorAlong_inner_secondFundamentalFormAlong
      immersion ambientLeviCivita extensions normal
      (x := x) (hfirst := hfield)
      (htest := SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
        (I := I) x test)
      (hnormalExtension := normalExtension_mdifferentiableAt) normalOrthogonal
    rw [shapeOperatorOfSecondFundamental_inner]
    have shapePairing' :
        inner ℝ shapeAlong test =
          inner ℝ
            (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
              immersion.toSmoothImmersionData immersion.orthogonalSplitting
              ambientLeviCivita.connection fieldExtension testField x)
            (normal x) := by
      simpa [shapeAlong, testField] using shapePairing
    rw [shapePairing']
    rw [normal_value]
    simp [pointII, fieldExtension, testField,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
    rfl
  have ambientNormalValue : ambientNormal (immersion.toFun x) = normal x :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees normal x
  have ambientFieldValue : ambientField (immersion.toFun x) =
      mfderiv I I' immersion.toFun x field := by
    simpa [ambientField, fieldExtension] using
      (extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees fieldExtension x)
  have torsionIdentity := ambientLeviCivita.connection.torsion_eq_zero_iff.mp
    ambientLeviCivita.torsionFree normalExtension_mdifferentiableAt hambientField
  have torsionAt :
      ambientLeviCivita.connection ambientField (immersion.toFun x) (normal x) -
          ambientLeviCivita.connection ambientNormal (immersion.toFun x)
            (mfderiv I I' immersion.toFun x field) =
        VectorField.mlieBracket I' ambientNormal ambientField (immersion.toFun x) := by
    dsimp only [ambientNormal] at ambientNormalValue ⊢
    rw [← ambientNormalValue, ← ambientFieldValue]
    exact torsionIdentity
  have weingartenAt :
      ambientLeviCivita.connection ambientNormal (immersion.toFun x)
          (mfderiv I I' immersion.toFun x field) =
        -(mfderiv I I' immersion.toFun x shapeAlong) +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection fieldExtension normal x := by
    simpa [SubmanifoldFieldExtensionData.ambientDerivativeAlong, ambientNormal,
      fieldExtension, shapeAlong] using
      (extensions.toSubmanifoldFieldExtensionData.ambientDerivativeAlong_eq_weingarten
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
        fieldExtension normal x)
  change ambientLeviCivita.connection ambientField (immersion.toFun x)
        (meanNormal : TangentSpace I' (immersion.toFun x)) -
      (meanNormalDerivative : TangentSpace I' (immersion.toFun x)) =
    VectorField.mlieBracket I' ambientNormal ambientField (immersion.toFun x) -
      mfderiv I I' immersion.toFun x
        (shapeOperatorOfSecondFundamental pointII meanNormal field)
  rw [← normal_value, ← normal_derivative, shapeEquality, ← torsionAt, weingartenAt]
  module

/-- Specialize the single-source differentiated jet by constructing its normal-direction first
derivative and mean bracket from the ambient connection and a chosen normal mean-curvature
field. -/
def inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
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
    SubmanifoldDifferentiatedGaussWeingartenJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x :=
  inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
    (ambientNormalDerivativeOfCanonicalTangentFieldAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection extensions x field)
    ambientNormalSecondDerivative ambientNormalAccelerationDerivative
    (ambientBracketOfNormalAndCanonicalTangentFieldAt immersion.toSmoothImmersionData
      extensions x field normal)

/-- The second fundamental form stored by the mean-field jet is symmetric because it is the
one constructed from the ambient torsion-free connection and the canonical bracket-compatible
tangent extensions. -/
theorem inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_secondFundamental_comm
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
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
    (first second : TangentSpace I x) :
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative normal).secondFundamental first second =
      (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative normal).secondFundamental second first := by
  change
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x first second =
      CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x second first
  exact extensions.projectedSecondFundamentalFormAt_comm
    immersion.toSmoothImmersionData immersion.orthogonalSplitting
    ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
    immersion.hasTangentProjectionLeftInverse ambientLeviCivita.torsionFree
    (extensions.hasBracketCompatibility immersion.toSmoothImmersionData) x first second

/-- The mean-field specialization satisfies the bracket--Weingarten identity once the chosen
normal field realizes the constructed mean curvature and its normal covariant derivative to
first order at the base point. -/
theorem inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_hasMeanBracketWeingarten
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
    (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
      tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
      ambientNormalSecondDerivative ambientNormalAccelerationDerivative normal
      ).toPointwiseBochnerGaussJet.HasMeanBracketWeingarten := by
  simpa [PointwiseBochnerGaussJet.HasMeanBracketWeingarten,
    PointwiseBochnerGaussJet.meanDerivative, PointwiseBochnerGaussJet.meanShape,
    inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt,
    inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt,
    connectionSubmanifoldDifferentiatedGaussWeingartenJetAt,
    submanifoldDifferentiatedGaussWeingartenJetAt,
    PointwiseDifferentiatedGaussWeingartenJet.toPointwiseBochnerGaussJet,
    PointwiseDifferentiatedGaussWeingartenJet.meanNormalDerivative,
    inducedLeviCivitaSubmanifoldMeanCurvatureAt,
    inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt] using
    (ambientNormalDerivative_sub_meanNormalDerivative_eq_bracket_sub_meanShape
      immersion ambientLeviCivita extensions x intrinsicRegular extensionRegular tangentFrame
      field normal normalExtension_mdifferentiableAt normal_mem normal_value normal_derivative)

/-- CCG25 equations (1.5) and (1.6) on the actual tangent, kernel-normal, and ambient tangent
fibers of one isometric immersion.  The second fundamental form, `∇ᴮ II`, normal ambient
curvature, contracted Codazzi identity, and bracket--Weingarten conversion are all derived from
the immersion and its Levi--Civita connection.  The remaining explicit inputs are precisely the
field-specific intrinsic two-jet, the two normal-direction ambient second-jet terms, and a
first-order normal-field realization of mean curvature. -/
theorem inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_gaussFormulas
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
    let jet :=
      (inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative normal).toPointwiseBochnerGaussJet
    jet.ambientBochner =
        jet.intrinsicBochner + jet.normalShapeSquare -
          (Fintype.card ι : ℝ) • jet.meanShape +
          (Fintype.card ι : ℝ) • jet.meanBracket -
          jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
          (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue -
          jet.ambientCurvatureNormalTraceValue ∧
      jet.ambientBochner =
        jet.intrinsicBochner + jet.normalShapeSquare +
          (Fintype.card ι : ℝ) • jet.meanDerivative -
          jet.normalSecondDerivativeTrace + jet.normalAccelerationDerivativeTrace -
          jet.codazziTraceValue -
          (2 : ℝ) • jet.secondFundamentalDerivativeTraceValue := by
  dsimp only
  constructor
  · apply PointwiseBochnerGaussJet.ambientBochner_eq_firstGaussFormula
    · intro first second
      exact
        inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_secondFundamental_comm
          immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
          extensionRegular tangentFrame normalFrame field firstDerivative
          intrinsicSecondDerivative ambientNormalSecondDerivative
          ambientNormalAccelerationDerivative normal first second
    · exact inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetAt_hasContractedCodazzi
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
        tangentFrame normalFrame field firstDerivative intrinsicSecondDerivative
        (ambientNormalDerivativeOfCanonicalTangentFieldAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection extensions x field)
        ambientNormalSecondDerivative ambientNormalAccelerationDerivative
        (ambientBracketOfNormalAndCanonicalTangentFieldAt immersion.toSmoothImmersionData
          extensions x field normal)
    · exact
        inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_hasMeanBracketWeingarten
          immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
          extensionRegular tangentFrame normalFrame field firstDerivative
          intrinsicSecondDerivative ambientNormalSecondDerivative
          ambientNormalAccelerationDerivative normal normalExtension_mdifferentiableAt
          normal_mem normal_value normal_derivative
  · apply PointwiseBochnerGaussJet.ambientBochner_eq_secondGaussFormula
    intro first second
    exact
      inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_secondFundamental_comm
        immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
        extensionRegular tangentFrame normalFrame field firstDerivative
        intrinsicSecondDerivative ambientNormalSecondDerivative
        ambientNormalAccelerationDerivative normal first second

/-- The remaining analytic data needed to realize the CCG25 pointwise Laplacian formulas from a
single smooth tangent field and its ambient extension.  The geometric identities are deliberately
absent: `II`, `∇ᴮ II`, Codazzi, and bracket--Weingarten are constructed by the theorems above.
A tubular-neighborhood adapter closes the source setting by constructing a value of this
structure and identifying its derivative fields with the paper's smooth extension. -/
structure SubmanifoldLaplacianFieldJetDataAt
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
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x) where
  tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x)
  normalFrame : OrthonormalBasis κ ℝ
    (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x)
  field : TangentSpace I x
  firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x
  intrinsicSecondDerivative :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x
  ambientNormalSecondDerivative :
    SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x →L[ℝ]
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x)
  ambientNormalAccelerationDerivative :
    SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x →L[ℝ]
      SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x)
  meanNormalField : AmbientVectorFieldAlong immersion.toSmoothImmersionData
  meanNormalField_extension_mdifferentiableAt : MDiffAt
    (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension meanNormalField))
    (immersion.toFun x)
  meanNormalField_mem : ∀ y,
    immersion.orthogonalSplitting.tangentProjection y (meanNormalField y) = 0
  meanNormalField_value : meanNormalField x =
    (inducedLeviCivitaSubmanifoldMeanCurvatureAt immersion ambientLeviCivita
      extensions x tangentFrame : TangentSpace I' (immersion.toFun x))
  meanNormalField_derivative :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection
        (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field)
        meanNormalField x =
      (inducedLeviCivitaSubmanifoldMeanNormalDerivativeAt immersion ambientLeviCivita
        extensions x intrinsicRegular extensionRegular tangentFrame field :
          TangentSpace I' (immersion.toFun x))

/-- Build the actual-fiber differentiated Gauss--Weingarten jet from the named analytic
realization boundary. -/
def SubmanifoldLaplacianFieldJetDataAt.toDifferentiatedGaussWeingartenJet
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
    SubmanifoldDifferentiatedGaussWeingartenJetAt
      (ι := ι) (κ := κ) immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x :=
  inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    data.tangentFrame data.normalFrame data.field data.firstDerivative
    data.intrinsicSecondDerivative data.ambientNormalSecondDerivative
    data.ambientNormalAccelerationDerivative data.meanNormalField

/-- Every value of the explicit analytic realization boundary produces both CCG25 Bochner
Gauss formulas; none of the geometric compatibility identities is requested from the caller. -/
theorem SubmanifoldLaplacianFieldJetDataAt.hasGaussFormulas
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
    (data.toDifferentiatedGaussWeingartenJet ambientRegular
      ).toPointwiseBochnerGaussJet.HasGaussFormulas := by
  rw [PointwiseBochnerGaussJet.HasGaussFormulas]
  exact inducedLeviCivitaSubmanifoldDifferentiatedGaussWeingartenJetOfMeanFieldAt_gaussFormulas
    immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular
    data.tangentFrame data.normalFrame data.field data.firstDerivative
    data.intrinsicSecondDerivative data.ambientNormalSecondDerivative
    data.ambientNormalAccelerationDerivative data.meanNormalField
    data.meanNormalField_extension_mdifferentiableAt data.meanNormalField_mem
    data.meanNormalField_value data.meanNormalField_derivative

/-- Construct the actual-fiber jet with canonical tangent lift `df_x` and canonical inclusion of
the normal kernel into the ambient tangent fiber. -/
def submanifoldBochnerGaussJetAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x))
    (field : TangentSpace I x)
    (secondFundamental : SubmanifoldSecondFundamentalFormAt immersion splitting x)
    (firstDerivative : TangentSpace I x →L[ℝ] TangentSpace I x)
    (intrinsicSecondDerivative :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (normalDerivativeSecondFundamental :
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x)
    (ambientNormalDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        TangentSpace I' (immersion.toFun x))
    (ambientNormalSecondDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (ambientNormalAccelerationDerivative :
      SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
        SubmanifoldNormalSpaceAt immersion splitting x →L[ℝ]
          TangentSpace I' (immersion.toFun x))
    (meanBracket : TangentSpace I' (immersion.toFun x))
    (meanNormalDerivative ambientCurvatureNormalTrace :
      SubmanifoldNormalSpaceAt immersion splitting x) :
    SubmanifoldBochnerGaussJetAt (ι := ι) (κ := κ) immersion splitting x where
  tangentFrame := tangentFrame
  normalFrame := normalFrame
  tangentLift := mfderiv I I' immersion.toFun x
  normalLift := (LinearMap.ker (splitting.tangentProjection x).toLinearMap).subtypeL
  field := field
  secondFundamental := secondFundamental
  firstDerivative := firstDerivative
  intrinsicSecondDerivative := intrinsicSecondDerivative
  normalDerivativeSecondFundamental := normalDerivativeSecondFundamental
  ambientNormalDerivative := ambientNormalDerivative
  ambientNormalSecondDerivative := ambientNormalSecondDerivative
  ambientNormalAccelerationDerivative := ambientNormalAccelerationDerivative
  meanBracket := meanBracket
  meanNormalDerivative := meanNormalDerivative
  ambientCurvatureNormalTrace := ambientCurvatureNormalTrace

end ManifoldFibers

end

end RiemannianFluids
