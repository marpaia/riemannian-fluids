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

/-- The bracket identity obtained from torsion-freeness and Weingarten:
`∇̃_H v - ∇⊥_v H = [H,v] - W_H v`. -/
def PointwiseBochnerGaussJet.HasMeanBracketWeingarten
    (jet : PointwiseBochnerGaussJet
      (ι := ι) (κ := κ) (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)) :
    Prop :=
  jet.meanDerivative - jet.normalLift jet.meanNormalDerivative =
    jet.meanBracket - jet.meanShape

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
