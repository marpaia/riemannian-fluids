import RiemannianFluids.Geometry.SubmanifoldInducedConnection
import RiemannianFluids.Geometry.Curvature
import RiemannianFluids.Tensors.Contraction

/-!
# Pointwise Gauss geometry of a Riemannian submanifold

The differential Gauss--Weingarten layer produces, at each point of an embedded submanifold,
an intrinsic curvature tensor and a normal-valued second fundamental form.  This file performs
the coordinate-free finite-dimensional contraction that turns the scalar Gauss equation into
the Ricci equation used by CCG25.

No Ricci or shape-square conclusion is stored as data.  Shape operators are constructed from the
second fundamental form by Riesz duality, mean curvature is the normalized tangent trace, and the
normal shape square is the trace over an orthonormal normal frame.  The main theorem proves their
relationship by expanding both tangent and normal traces.
-/

namespace RiemannianFluids

open Bundle
open scoped BigOperators Bundle ContDiff Manifold

noncomputable section

section PointwiseGauss

variable
  {Tangent Normal : Type*}
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [FiniteDimensional ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
  [FiniteDimensional ℝ Normal]

/-- Pointwise tensors entering the Gauss equation.  The curvature convention is
`R(X,Y)Z`; the second fundamental form has values in the normal space. -/
structure PointwiseGaussData where
  intrinsicCurvature :
    Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent
  secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal

/-- Symmetry of the pointwise second fundamental form. -/
def PointwiseGaussData.IsSymmetric
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal)) : Prop :=
  ∀ first second,
    data.secondFundamental first second = data.secondFundamental second first

/-- The Euclidean scalar Gauss equation in the curvature convention used by the repository:

`<R(X,Y)Z,W> = <II(X,W),II(Y,Z)> - <II(X,Z),II(Y,W)>`.
-/
def PointwiseGaussData.HasEuclideanGaussEquation
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal)) : Prop :=
  ∀ first second field test,
    inner ℝ (data.intrinsicCurvature first second field) test =
      inner ℝ (data.secondFundamental first test)
          (data.secondFundamental second field) -
        inner ℝ (data.secondFundamental first field)
          (data.secondFundamental second test)

/-- The scalar Gauss equation relative to the tangential part of an ambient curvature tensor. -/
def PointwiseGaussData.HasGaussEquationRelativeTo
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (ambientTangentialCurvature :
      Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent) : Prop :=
  ∀ first second field test,
    inner ℝ (data.intrinsicCurvature first second field) test =
      inner ℝ (ambientTangentialCurvature first second field) test +
        inner ℝ (data.secondFundamental first test)
          (data.secondFundamental second field) -
        inner ℝ (data.secondFundamental first field)
          (data.secondFundamental second test)

/-- Lower a normal-valued second fundamental form against a fixed normal vector. -/
def secondFundamentalFormAgainst
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal)
    (normal : Normal) : Tangent →L[ℝ] Tangent →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ Tangent Normal ℝ (innerSL ℝ normal)).comp
    secondFundamental

omit [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal] in
@[simp]
theorem secondFundamentalFormAgainst_apply
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal)
    (normal : Normal) (first second : Tangent) :
    secondFundamentalFormAgainst secondFundamental normal first second =
      inner ℝ (secondFundamental first second) normal := by
  simp [secondFundamentalFormAgainst, real_inner_comm]

/-- The family of shape operators constructed from `II` by Riesz duality:

`<W_N X,Y> = <II(X,Y),N>`.
-/
def shapeOperatorOfSecondFundamental
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal) :
    Normal →L[ℝ] Tangent →L[ℝ] Tangent :=
  LinearMap.toContinuousLinearMap {
    toFun := fun normal ↦
      InnerProductSpace.continuousLinearMapOfBilin
        (secondFundamentalFormAgainst secondFundamental normal)
    map_add' := by
      intro firstNormal secondNormal
      ext first
      apply ext_inner_right ℝ
      intro second
      simp only [add_apply, InnerProductSpace.continuousLinearMapOfBilin_apply,
        inner_add_left]
      simp [secondFundamentalFormAgainst]
    map_smul' := by
      intro scalar normal
      ext first
      apply ext_inner_right ℝ
      intro second
      simp only [smul_apply, RingHom.id_apply,
        InnerProductSpace.continuousLinearMapOfBilin_apply,
        real_inner_smul_left]
      simp [secondFundamentalFormAgainst]
  }

@[simp]
theorem shapeOperatorOfSecondFundamental_inner
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal)
    (normal : Normal) (first second : Tangent) :
    inner ℝ (shapeOperatorOfSecondFundamental secondFundamental normal first) second =
      inner ℝ (secondFundamental first second) normal := by
  change inner ℝ
      (InnerProductSpace.continuousLinearMapOfBilin
        (secondFundamentalFormAgainst secondFundamental normal) first) second = _
  rw [
    InnerProductSpace.continuousLinearMapOfBilin_apply,
    secondFundamentalFormAgainst_apply]

/-- The uncontracted tangential Gauss equation.  Its two shape terms are constructed from the
same normal-valued second fundamental form; taking an inner product yields the scalar Gauss
equation used by all Ricci contractions below. -/
def PointwiseGaussData.HasVectorGaussEquationRelativeTo
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (ambientTangentialCurvature :
      Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent) : Prop :=
  ∀ first second field,
    data.intrinsicCurvature first second field =
      ambientTangentialCurvature first second field +
        shapeOperatorOfSecondFundamental data.secondFundamental
          (data.secondFundamental second field) first -
        shapeOperatorOfSecondFundamental data.secondFundamental
          (data.secondFundamental first field) second

/-- The vector Gauss equation implies its scalar contraction.  This theorem fixes the sign and
argument-order bridge between differentiated Gauss--Weingarten geometry and the Ricci trace
theorems in this file. -/
theorem PointwiseGaussData.hasGaussEquationRelativeTo_of_vector
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (ambientTangentialCurvature :
      Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent)
    (vectorGauss : data.HasVectorGaussEquationRelativeTo ambientTangentialCurvature) :
    data.HasGaussEquationRelativeTo ambientTangentialCurvature := by
  intro first second field test
  rw [vectorGauss, inner_sub_left, inner_add_left,
    shapeOperatorOfSecondFundamental_inner,
    shapeOperatorOfSecondFundamental_inner]
  rw [real_inner_comm (data.secondFundamental second test)
    (data.secondFundamental first field)]

omit [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal] in
/-- If the ambient tangential curvature vanishes, the relative scalar Gauss equation is exactly
the Euclidean scalar Gauss equation. -/
theorem PointwiseGaussData.hasEuclideanGaussEquation_of_relative_eq_zero
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (ambientTangentialCurvature :
      Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent)
    (gauss : data.HasGaussEquationRelativeTo ambientTangentialCurvature)
    (flat : ambientTangentialCurvature = 0) :
    data.HasEuclideanGaussEquation := by
  intro first second field test
  rw [gauss, flat]
  simp

/-- Vectorial mean curvature computed in a tangent orthonormal frame. -/
def meanCurvatureOfSecondFundamental
    {ι : Type*} [Fintype ι]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal) : Normal :=
  ((Fintype.card ι : ℝ)⁻¹) •
    ∑ i, secondFundamental (tangentFrame i) (tangentFrame i)

/-- Multiplying the shape operator of the normalized mean-curvature vector by the tangent
dimension recovers the shape operator of the unnormalized trace of `II`. -/
theorem card_smul_shapeOperator_meanCurvature
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal) :
    (Fintype.card ι : ℝ) •
        shapeOperatorOfSecondFundamental secondFundamental
          (meanCurvatureOfSecondFundamental tangentFrame secondFundamental) =
      shapeOperatorOfSecondFundamental secondFundamental
        (∑ i, secondFundamental (tangentFrame i) (tangentFrame i)) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [meanCurvatureOfSecondFundamental, map_smul, smul_smul,
    mul_inv_cancel₀ hcard, one_smul]

omit [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal] in
/-- The same normalization cancellation through any continuous linear map out of the normal
space.  This is used for the ambient derivative in the Bochner Gauss formula. -/
theorem card_smul_map_meanCurvature
    {ι Ambient : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal)
    (map : Normal →L[ℝ] Ambient) :
    (Fintype.card ι : ℝ) •
        map (meanCurvatureOfSecondFundamental tangentFrame secondFundamental) =
      map (∑ i, secondFundamental (tangentFrame i) (tangentFrame i)) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [meanCurvatureOfSecondFundamental, map_smul, smul_smul,
    mul_inv_cancel₀ hcard, one_smul]

/-- The normal-frame contraction `Σ_l W_{N_l} W_{N_l}`. -/
def normalShapeSquare
    {κ : Type*} [Fintype κ]
    (normalFrame : OrthonormalBasis κ ℝ Normal)
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal) :
    Tangent →L[ℝ] Tangent :=
  ∑ l,
    (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l)).comp
      (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l))

private theorem inner_normalShapeSquare
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (normalFrame : OrthonormalBasis κ ℝ Normal)
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal)
    (symmetric : ∀ first second,
      secondFundamental first second = secondFundamental second first)
    (field test : Tangent) :
    inner ℝ (normalShapeSquare normalFrame secondFundamental field) test =
      ∑ i, inner ℝ (secondFundamental (tangentFrame i) test)
        (secondFundamental field (tangentFrame i)) := by
  rw [normalShapeSquare, sum_apply, sum_inner]
  simp_rw [ContinuousLinearMap.comp_apply,
    shapeOperatorOfSecondFundamental_inner]
  calc
    ∑ l,
        inner ℝ
          (secondFundamental
            (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) field)
            test)
          (normalFrame l) =
      ∑ l,
        inner ℝ
          (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) field)
          (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) test) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [symmetric]
        calc
          inner ℝ
              (secondFundamental test
                (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) field))
              (normalFrame l) =
            inner ℝ
              (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) test)
              (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) field) :=
            (shapeOperatorOfSecondFundamental_inner secondFundamental
              (normalFrame l) test
              (shapeOperatorOfSecondFundamental secondFundamental
                (normalFrame l) field)).symm
          _ = _ := real_inner_comm _ _
    _ = ∑ l, ∑ i,
          inner ℝ
            (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) field)
            (tangentFrame i) *
          inner ℝ (tangentFrame i)
            (shapeOperatorOfSecondFundamental secondFundamental (normalFrame l) test) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [tangentFrame.sum_inner_mul_inner]
    _ = ∑ i, ∑ l,
          inner ℝ (secondFundamental field (tangentFrame i)) (normalFrame l) *
          inner ℝ (normalFrame l)
            (secondFundamental (tangentFrame i) test) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        rw [shapeOperatorOfSecondFundamental_inner]
        conv_lhs =>
          rhs
          rw [real_inner_comm,
            shapeOperatorOfSecondFundamental_inner,
            symmetric test,
            real_inner_comm]
    _ = ∑ i,
          inner ℝ (secondFundamental field (tangentFrame i))
            (secondFundamental (tangentFrame i) test) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [normalFrame.sum_inner_mul_inner]
    _ = ∑ i, inner ℝ (secondFundamental (tangentFrame i) test)
          (secondFundamental field (tangentFrame i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm]

/-- Tracing the Weingarten shape term produced by differentiating the Gauss formula gives the
normal-frame shape square. -/
theorem sum_shape_secondFundamental_eq_normalShapeSquare
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (normalFrame : OrthonormalBasis κ ℝ Normal)
    (secondFundamental : Tangent →L[ℝ] Tangent →L[ℝ] Normal)
    (symmetric : ∀ first second,
      secondFundamental first second = secondFundamental second first)
    (field : Tangent) :
    ∑ i,
        shapeOperatorOfSecondFundamental secondFundamental
          (secondFundamental (tangentFrame i) field) (tangentFrame i) =
      normalShapeSquare normalFrame secondFundamental field := by
  apply ext_inner_right ℝ
  intro test
  rw [sum_inner,
    inner_normalShapeSquare tangentFrame normalFrame secondFundamental symmetric]
  apply Finset.sum_congr rfl
  intro i _
  rw [shapeOperatorOfSecondFundamental_inner, symmetric field]

/-- Contracting the Euclidean Gauss equation proves the arbitrary-dimensional,
arbitrary-codimension Ricci formula

`Ric(v) = n W_H(v) - Σ_l W_{N_l}(W_{N_l}(v))`.

The theorem is pointwise and basis-independent in content: both sides are constructed from
complete orthonormal bases of the tangent and normal spaces. -/
theorem euclidean_gauss_ricci
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (normalFrame : OrthonormalBasis κ ℝ Normal)
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (symmetric : data.IsSymmetric)
    (gauss : data.HasEuclideanGaussEquation) :
    ricciActionOfCurvatureTensor data.intrinsicCurvature =
      (Fintype.card ι : ℝ) •
          shapeOperatorOfSecondFundamental data.secondFundamental
            (meanCurvatureOfSecondFundamental tangentFrame data.secondFundamental) -
        normalShapeSquare normalFrame data.secondFundamental := by
  rw [card_smul_shapeOperator_meanCurvature tangentFrame data.secondFundamental]
  ext field
  apply ext_inner_right ℝ
  intro test
  rw [ricciActionOfCurvatureTensor_inner,
    ricciFormOfCurvatureTensor_eq_sum_inner data.intrinsicCurvature tangentFrame]
  rw [show
      (∑ i, inner ℝ (tangentFrame i)
        (data.intrinsicCurvature (tangentFrame i) field test)) =
        ∑ i,
          (inner ℝ (data.secondFundamental (tangentFrame i) (tangentFrame i))
              (data.secondFundamental field test) -
            inner ℝ (data.secondFundamental (tangentFrame i) test)
              (data.secondFundamental field (tangentFrame i))) by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm, gauss]]
  rw [sub_apply, inner_sub_left,
    inner_normalShapeSquare tangentFrame normalFrame data.secondFundamental symmetric]
  rw [shapeOperatorOfSecondFundamental_inner, inner_sum,
    Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]

/-- Contracting the scalar Gauss equation relative to ambient tangential curvature gives the
arbitrary-dimensional and arbitrary-codimension Ricci contraction. -/
theorem gauss_ricci_relative
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (tangentFrame : OrthonormalBasis ι ℝ Tangent)
    (normalFrame : OrthonormalBasis κ ℝ Normal)
    (data : PointwiseGaussData (Tangent := Tangent) (Normal := Normal))
    (ambientTangentialCurvature :
      Tangent →L[ℝ] Tangent →L[ℝ] Tangent →L[ℝ] Tangent)
    (symmetric : data.IsSymmetric)
    (gauss : data.HasGaussEquationRelativeTo ambientTangentialCurvature) :
    ricciActionOfCurvatureTensor data.intrinsicCurvature =
      ricciActionOfCurvatureTensor ambientTangentialCurvature +
        (Fintype.card ι : ℝ) •
          shapeOperatorOfSecondFundamental data.secondFundamental
            (meanCurvatureOfSecondFundamental tangentFrame data.secondFundamental) -
        normalShapeSquare normalFrame data.secondFundamental := by
  rw [card_smul_shapeOperator_meanCurvature tangentFrame data.secondFundamental]
  ext field
  apply ext_inner_right ℝ
  intro test
  rw [ricciActionOfCurvatureTensor_inner,
    ricciFormOfCurvatureTensor_eq_sum_inner data.intrinsicCurvature tangentFrame,
    sub_apply, add_apply, inner_sub_left, inner_add_left,
    ricciActionOfCurvatureTensor_inner,
    ricciFormOfCurvatureTensor_eq_sum_inner ambientTangentialCurvature tangentFrame,
    shapeOperatorOfSecondFundamental_inner, inner_sum,
    inner_normalShapeSquare tangentFrame normalFrame data.secondFundamental symmetric]
  rw [show
      (∑ i, inner ℝ (tangentFrame i)
        (data.intrinsicCurvature (tangentFrame i) field test)) =
        ∑ i,
          (inner ℝ (tangentFrame i)
              (ambientTangentialCurvature (tangentFrame i) field test) +
            inner ℝ (data.secondFundamental (tangentFrame i) (tangentFrame i))
              (data.secondFundamental field test) -
            inner ℝ (data.secondFundamental (tangentFrame i) test)
              (data.secondFundamental field (tangentFrame i))) by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm]
      rw [gauss]
      rw [real_inner_comm
        (ambientTangentialCurvature (tangentFrame i) field test) (tangentFrame i)]]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  apply congrArg (fun value : ℝ ↦
    (∑ i, inner ℝ (tangentFrame i)
      (ambientTangentialCurvature (tangentFrame i) field test)) + value -
        ∑ i, inner ℝ (data.secondFundamental (tangentFrame i) test)
          (data.secondFundamental field (tangentFrame i)))
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]

end PointwiseGauss

/-! ## Specialization to actual Mathlib tangent and normal fibers -/

section ManifoldFibers

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

/-- The normal fiber at `x`, realized exactly as the kernel of tangential projection inside the
pulled-back ambient tangent fiber. -/
abbrev SubmanifoldNormalSpaceAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M) :=
  LinearMap.ker (splitting.tangentProjection x).toLinearMap

/-- A continuous second fundamental form whose codomain is the actual normal fiber. -/
abbrev SubmanifoldSecondFundamentalFormAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M) :=
  TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
    SubmanifoldNormalSpaceAt immersion splitting x

/-- Pointwise Gauss data on actual tangent and normal fibers of a Mathlib-backed immersion. -/
abbrev SubmanifoldPointwiseGaussDataAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) (x : M) :=
  PointwiseGaussData
    (Tangent := TangentSpace I x)
    (Normal := SubmanifoldNormalSpaceAt immersion splitting x)

/-- The union of an intrinsic orthonormal tangent frame, lifted by `df_x`, and an orthonormal
frame of the kernel-normal fiber is an orthonormal basis of the ambient tangent fiber.  This is
the adapted frame needed to split ambient traces into tangent and normal contributions. -/
def SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (x : M)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x)) :
    OrthonormalBasis (ι ⊕ κ) ℝ (TangentSpace I' (immersion.toFun x)) := by
  classical
  let frame : ι ⊕ κ → TangentSpace I' (immersion.toFun x) :=
    Sum.elim
      (fun i ↦ mfderiv I I' immersion.toFun x (tangentFrame i))
      (fun l ↦ (normalFrame l : TangentSpace I' (immersion.toFun x)))
  have orthonormal : Orthonormal ℝ frame := by
    rw [orthonormal_iff_ite]
    intro first second
    cases first with
    | inl i =>
        cases second with
        | inl j =>
            simpa [frame, immersion.mfderiv_inner] using
              (orthonormal_iff_ite.mp tangentFrame.orthonormal i j)
        | inr l =>
            have normalOrthogonal := (immersion.mem_normalSpace_iff x (normalFrame l)).mp
              (normalFrame l).property (tangentFrame i)
            simpa [frame, real_inner_comm] using normalOrthogonal
    | inr l =>
        cases second with
        | inl i =>
            have normalOrthogonal := (immersion.mem_normalSpace_iff x (normalFrame l)).mp
              (normalFrame l).property (tangentFrame i)
            simpa [frame] using normalOrthogonal
        | inr k =>
            simpa [frame] using (orthonormal_iff_ite.mp normalFrame.orthonormal l k)
  refine OrthonormalBasis.mk orthonormal ?_
  intro ambient _
  let normalValue : SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
    ⟨immersion.orthogonalSplitting.normalProjection x ambient,
      tangentProjection_normalProjection_eq_zero immersion.toSmoothImmersionData
        immersion.orthogonalSplitting immersion.hasTangentNormalDecomposition
        immersion.hasTangentProjectionLeftInverse x ambient⟩
  have tangentMem : mfderiv I I' immersion.toFun x
      (immersion.orthogonalSplitting.tangentProjection x ambient) ∈
        Submodule.span ℝ (Set.range frame) := by
    rw [← tangentFrame.sum_repr
      (immersion.orthogonalSplitting.tangentProjection x ambient), map_sum]
    exact Submodule.sum_mem _ fun i _ ↦ by
      rw [map_smul]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self (Sum.inl i)))
  have normalMem : (normalValue : TangentSpace I' (immersion.toFun x)) ∈
      Submodule.span ℝ (Set.range frame) := by
    let normalLift :=
      (LinearMap.ker
        (immersion.orthogonalSplitting.tangentProjection x).toLinearMap).subtypeL
    change normalLift normalValue ∈ Submodule.span ℝ (Set.range frame)
    rw [← normalFrame.sum_repr normalValue, map_sum]
    exact Submodule.sum_mem _ fun l _ ↦ by
      rw [map_smul]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self (Sum.inr l)))
  rw [← immersion.hasTangentNormalDecomposition x ambient]
  exact Submodule.add_mem _ tangentMem normalMem

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [IsManifold I 1 M] [IsManifold I' 1 N] in
@[simp]
theorem SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt_apply_inl
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (x : M)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (i : ι) :
    immersion.adaptedAmbientOrthonormalBasisAt x tangentFrame normalFrame (Sum.inl i) =
      mfderiv I I' immersion.toFun x (tangentFrame i) := by
  classical
  simp [SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [IsManifold I 1 M] [IsManifold I' 1 N] in
@[simp]
theorem SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt_apply_inr
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (x : M)
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (l : κ) :
    immersion.adaptedAmbientOrthonormalBasisAt x tangentFrame normalFrame (Sum.inr l) =
      (normalFrame l : TangentSpace I' (immersion.toFun x)) := by
  classical
  simp [SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt]

/-- Populate the intrinsic curvature slot from an actual bundled connection.  The only supplied
tensor is the normal-valued second fundamental form; Ricci is still constructed later by trace. -/
def connectionSubmanifoldPointwiseGaussDataAt
    [IsManifold I 3 M]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (regular : HasConnectionCurvatureRegularityAt I connection x)
    (secondFundamental : SubmanifoldSecondFundamentalFormAt immersion splitting x) :
    SubmanifoldPointwiseGaussDataAt immersion splitting x where
  intrinsicCurvature := connectionCurvatureTensorAt I connection x regular
  secondFundamental := secondFundamental

/-- Actual-fiber Gauss data whose curvature comes from the intrinsic connection and whose second
fundamental form is obtained by differentiating chosen ambient extensions and applying the normal
projection.  No second-fundamental-form tensor is supplied independently. -/
def projectedConnectionSubmanifoldPointwiseGaussDataAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : SubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (intrinsicRegular : HasConnectionCurvatureRegularityAt I intrinsicConnection x)
    (extensionRegular :
      extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x) :
    SubmanifoldPointwiseGaussDataAt immersion splitting x :=
  connectionSubmanifoldPointwiseGaussDataAt immersion splitting intrinsicConnection x
    intrinsicRegular
    (extensions.projectedSecondFundamentalFormAt immersion splitting ambientConnection
      decomposition leftInverse x extensionRegular)

/-- The second fundamental form in the actual-fiber Gauss data above is symmetric whenever the
ambient connection is torsion free and brackets of the chosen tangent extensions remain tangent.
This discharges CCG25's symmetry input from connection geometry rather than assuming it on an
unrelated bilinear map. -/
theorem projectedConnectionSubmanifoldPointwiseGaussDataAt_isSymmetric
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : SubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (intrinsicRegular : HasConnectionCurvatureRegularityAt I intrinsicConnection x)
    (extensionRegular :
      extensions.HasDifferentiableCanonicalTangentExtensionsAt immersion x)
    (tangentBracket : extensions.HasTangentCanonicalBracketAt immersion splitting x)
    (ambientTorsionFree : ambientConnection.torsion = 0) :
    (projectedConnectionSubmanifoldPointwiseGaussDataAt immersion splitting intrinsicConnection
      ambientConnection extensions decomposition leftInverse x intrinsicRegular
      extensionRegular).IsSymmetric := by
  intro first second
  exact extensions.projectedSecondFundamentalFormAt_comm immersion splitting ambientConnection
    decomposition leftInverse x extensionRegular tangentBracket ambientTorsionFree first second

/-- The preceding construction specialized to the canonical orthogonal splitting of an
isometric immersion.  Reconstruction and the tangential left-inverse law are now theorems of the
immersion and disappear from the caller-facing data. -/
def isometricConnectionSubmanifoldPointwiseGaussDataAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : SubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M) (intrinsicRegular : HasConnectionCurvatureRegularityAt I intrinsicConnection x)
    (extensionRegular :
      extensions.HasDifferentiableCanonicalTangentExtensionsAt
        immersion.toSmoothImmersionData x) :
    SubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
  projectedConnectionSubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
    immersion.orthogonalSplitting intrinsicConnection ambientConnection extensions
    immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse x
    intrinsicRegular extensionRegular

/-- For an isometric immersion, ambient torsion-freeness and the single remaining bracket
tangency condition prove symmetry of the canonically constructed second fundamental form. -/
theorem isometricConnectionSubmanifoldPointwiseGaussDataAt_isSymmetric
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (intrinsicConnection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : SubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M) (intrinsicRegular : HasConnectionCurvatureRegularityAt I intrinsicConnection x)
    (extensionRegular :
      extensions.HasDifferentiableCanonicalTangentExtensionsAt
        immersion.toSmoothImmersionData x)
    (tangentBracket : extensions.HasTangentCanonicalBracketAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting x)
    (ambientTorsionFree : ambientConnection.torsion = 0) :
    (isometricConnectionSubmanifoldPointwiseGaussDataAt immersion intrinsicConnection
      ambientConnection extensions x intrinsicRegular extensionRegular).IsSymmetric :=
  projectedConnectionSubmanifoldPointwiseGaussDataAt_isSymmetric
    immersion.toSmoothImmersionData immersion.orthogonalSplitting intrinsicConnection
    ambientConnection extensions immersion.hasTangentNormalDecomposition
    immersion.hasTangentProjectionLeftInverse x intrinsicRegular extensionRegular tangentBracket
    ambientTorsionFree

/-! ## Ambient curvature transported to the source tangent fiber -/

/-- Regard the normal projection as a continuous linear map into the actual kernel-normal fiber.
The codomain restriction is justified by the tangent/normal reconstruction and tangential
left-inverse laws, so normal-valuedness is carried by the type rather than by a later hypothesis. -/
def normalProjectionToNormalSpaceAt
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) :
    TangentSpace I' (immersion.toFun x) →L[ℝ]
      SubmanifoldNormalSpaceAt immersion splitting x :=
  ContinuousLinearMap.codRestrict (splitting.normalProjection x)
    (LinearMap.ker (splitting.tangentProjection x).toLinearMap)
    (fun ambient ↦ tangentProjection_normalProjection_eq_zero immersion splitting
      decomposition leftInverse x ambient)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E'] [IsManifold I' 1 N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
@[simp]
theorem normalProjectionToNormalSpaceAt_coe
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (ambient : TangentSpace I' (immersion.toFun x)) :
    ((normalProjectionToNormalSpaceAt immersion splitting decomposition leftInverse x ambient :
        SubmanifoldNormalSpaceAt immersion splitting x) :
      TangentSpace I' (immersion.toFun x)) =
        splitting.normalProjection x ambient :=
  rfl

/-- Pull all three input slots of the ambient connection-curvature tensor through `df_x`, then
project its output tangentially.  This is the actual ambient tensor occurring in the vector and
scalar Gauss equations; it is constructed from the ambient connection rather than supplied as an
unrelated trilinear map. -/
def tangentialAmbientConnectionCurvatureAt
    [IsManifold I' 3 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ LinearMap.toContinuousLinearMap {
      toFun := fun second ↦ LinearMap.toContinuousLinearMap {
        toFun := fun field ↦ splitting.tangentProjection x
          (connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x)
            ambientRegular
            (mfderiv I I' immersion.toFun x first)
            (mfderiv I I' immersion.toFun x second)
            (mfderiv I I' immersion.toFun x field))
        map_add' := by simp
        map_smul' := by simp }
      map_add' := by
        intro second second'
        ext field
        simp
      map_smul' := by
        intro scalar second
        ext field
        simp }
    map_add' := by
      intro first first'
      ext second field
      simp
    map_smul' := by
      intro scalar first
      ext second field
      simp }

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem tangentialAmbientConnectionCurvatureAt_apply
    [IsManifold I' 3 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (first second field : TangentSpace I x) :
    tangentialAmbientConnectionCurvatureAt immersion splitting ambientConnection x
        ambientRegular first second field =
      splitting.tangentProjection x
        (connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x)
          ambientRegular
          (mfderiv I I' immersion.toFun x first)
          (mfderiv I I' immersion.toFun x second)
          (mfderiv I I' immersion.toFun x field)) :=
  rfl

set_option synthInstance.maxHeartbeats 100000 in
/-- Pull all three input slots of ambient connection curvature through `df_x` and project its
output into the actual kernel-normal fiber.  This is the normal ambient-curvature tensor in the
uncontracted Codazzi equation. -/
def normalAmbientConnectionCurvatureAt
    [IsManifold I' 3 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] SubmanifoldNormalSpaceAt immersion splitting x :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first ↦ LinearMap.toContinuousLinearMap {
      toFun := fun second ↦ LinearMap.toContinuousLinearMap {
        toFun := fun field ↦
          normalProjectionToNormalSpaceAt immersion splitting decomposition leftInverse x
            (connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x)
              ambientRegular
              (mfderiv I I' immersion.toFun x first)
              (mfderiv I I' immersion.toFun x second)
              (mfderiv I I' immersion.toFun x field))
        map_add' := by simp
        map_smul' := by simp }
      map_add' := by
        intro second second'
        ext field
        simp
      map_smul' := by
        intro scalar second
        ext field
        simp }
    map_add' := by
      intro first first'
      ext second field
      simp
    map_smul' := by
      intro scalar first
      ext second field
      simp }

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem normalAmbientConnectionCurvatureAt_coe
    [IsManifold I' 3 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (first second field : TangentSpace I x) :
    ((normalAmbientConnectionCurvatureAt immersion splitting ambientConnection decomposition
        leftInverse x ambientRegular first second field :
      SubmanifoldNormalSpaceAt immersion splitting x) :
      TangentSpace I' (immersion.toFun x)) =
      splitting.normalProjection x
        (connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x)
          ambientRegular
          (mfderiv I I' immersion.toFun x first)
          (mfderiv I I' immersion.toFun x second)
          (mfderiv I I' immersion.toFun x field)) :=
  rfl

/-! ## Ambient Ricci trace in an adapted frame -/

/-- The contribution to the ambient Ricci form obtained by tracing its first curvature slot over
an orthonormal frame of the normal fiber.  Its two remaining arguments live in the source tangent
fiber and are transported into the ambient fiber by `df_x`. -/
def normalFrameAmbientRicciFormAt
    [IsManifold I' 3 N]
    {κ : Type*} [Fintype κ]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x)) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let df := mfderiv I I' immersion.toFun x
  let ambientCurvature :=
    connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x) ambientRegular
  ∑ l,
    (ContinuousLinearMap.compL ℝ (TangentSpace I x)
      (TangentSpace I' (immersion.toFun x)) ℝ
      (innerSL ℝ (normalFrame l : TangentSpace I' (immersion.toFun x)))).comp
      (((ContinuousLinearMap.compL ℝ (TangentSpace I x)
        (TangentSpace I' (immersion.toFun x))
        (TangentSpace I' (immersion.toFun x))).flip df).comp
        ((ambientCurvature (normalFrame l : TangentSpace I' (immersion.toFun x))).comp df))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsManifold I 1 M]
  [∀ y : M, FiniteDimensional ℝ (TangentSpace I y)] in
@[simp]
theorem normalFrameAmbientRicciFormAt_apply
    [IsManifold I' 3 N]
    {κ : Type*} [Fintype κ]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x))
    (field test : TangentSpace I x) :
    normalFrameAmbientRicciFormAt immersion splitting ambientConnection x ambientRegular
        normalFrame field test =
      ∑ l, inner ℝ
        (normalFrame l : TangentSpace I' (immersion.toFun x))
        (connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x)
          ambientRegular
          (normalFrame l : TangentSpace I' (immersion.toFun x))
          (mfderiv I I' immersion.toFun x field)
          (mfderiv I I' immersion.toFun x test)) := by
  simp [normalFrameAmbientRicciFormAt]

/-- Raise the normal-frame part of the ambient Ricci form to a source tangent endomorphism. -/
noncomputable def normalFrameAmbientRicciActionAt
    [IsManifold I' 3 N]
    {κ : Type*} [Fintype κ]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x)) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  InnerProductSpace.continuousLinearMapOfBilin
    (normalFrameAmbientRicciFormAt immersion splitting ambientConnection x ambientRegular
      normalFrame)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsManifold I 1 M] in
@[simp]
theorem normalFrameAmbientRicciActionAt_inner
    [IsManifold I' 3 N]
    {κ : Type*} [Fintype κ]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion splitting x))
    (field test : TangentSpace I x) :
    inner ℝ
        (normalFrameAmbientRicciActionAt immersion splitting ambientConnection x ambientRegular
          normalFrame field) test =
      ∑ l, inner ℝ
        (normalFrame l : TangentSpace I' (immersion.toFun x))
        (connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x)
          ambientRegular
          (normalFrame l : TangentSpace I' (immersion.toFun x))
          (mfderiv I I' immersion.toFun x field)
          (mfderiv I I' immersion.toFun x test)) := by
  rw [normalFrameAmbientRicciActionAt,
    InnerProductSpace.continuousLinearMapOfBilin_apply,
    normalFrameAmbientRicciFormAt_apply]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsManifold I 1 M] in
/-- The ambient Ricci action along an isometric immersion splits canonically into the
tangent-frame trace, the normal-frame trace with tangent output, and the normal projection of
the output.  This derives the trace-splitting identity used by the Hodge Gauss formula from an
adapted orthonormal basis; it is not an additional curvature hypothesis. -/
theorem SmoothIsometricImmersionData.connectionRicciActionAlong_eq_adaptedTraceAt
    [IsManifold I' 3 N]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (x : M)
    (ambientRegular : HasConnectionCurvatureRegularityAt I' ambientConnection
      (immersion.toFun x))
    (tangentFrame : OrthonormalBasis ι ℝ (TangentSpace I x))
    (normalFrame : OrthonormalBasis κ ℝ
      (SubmanifoldNormalSpaceAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting x))
    (field : TangentSpace I x) :
    connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
        (mfderiv I I' immersion.toFun x field) =
      mfderiv I I' immersion.toFun x
          (ricciActionOfCurvatureTensor
              (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
                immersion.orthogonalSplitting ambientConnection x ambientRegular) field +
            normalFrameAmbientRicciActionAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting ambientConnection x ambientRegular normalFrame
              field) +
        immersion.orthogonalSplitting.normalProjection x
          (connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
            (mfderiv I I' immersion.toFun x field)) := by
  let ambientCurvature :=
    connectionCurvatureTensorAt I' ambientConnection (immersion.toFun x) ambientRegular
  let ambientRicci :=
    connectionRicciActionAt I' ambientConnection (immersion.toFun x) ambientRegular
      (mfderiv I I' immersion.toFun x field)
  let adaptedFrame :=
    immersion.adaptedAmbientOrthonormalBasisAt x tangentFrame normalFrame
  have ambientTrace (test : TangentSpace I x) :
      inner ℝ ambientRicci (mfderiv I I' immersion.toFun x test) =
        ∑ q : ι ⊕ κ,
          inner ℝ (adaptedFrame q)
            (ambientCurvature (adaptedFrame q)
              (mfderiv I I' immersion.toFun x field)
              (mfderiv I I' immersion.toFun x test)) := by
    dsimp only [ambientRicci]
    rw [connectionRicciActionAt_inner,
      connectionRicciFormAt_eq_sum_inner I' ambientConnection (immersion.toFun x)
        ambientRegular adaptedFrame]
  have tangentTrace (test : TangentSpace I x) :
      inner ℝ
          (ricciActionOfCurvatureTensor
            (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting ambientConnection x ambientRegular) field)
          test =
        ∑ i, inner ℝ
          (mfderiv I I' immersion.toFun x (tangentFrame i))
          (ambientCurvature
            (mfderiv I I' immersion.toFun x (tangentFrame i))
            (mfderiv I I' immersion.toFun x field)
            (mfderiv I I' immersion.toFun x test)) := by
    rw [ricciActionOfCurvatureTensor_inner,
      ricciFormOfCurvatureTensor_eq_sum_inner _ tangentFrame]
    apply Finset.sum_congr rfl
    intro i _
    rw [tangentialAmbientConnectionCurvatureAt_apply]
    change inner ℝ (tangentFrame i)
      ((mfderiv I I' immersion.toFun x).adjoint
        (ambientCurvature
          (mfderiv I I' immersion.toFun x (tangentFrame i))
          (mfderiv I I' immersion.toFun x field)
          (mfderiv I I' immersion.toFun x test))) = _
    calc
      _ = inner ℝ
          ((mfderiv I I' immersion.toFun x).adjoint
            (ambientCurvature
              (mfderiv I I' immersion.toFun x (tangentFrame i))
              (mfderiv I I' immersion.toFun x field)
              (mfderiv I I' immersion.toFun x test)))
          (tangentFrame i) := real_inner_comm _ _
      _ = inner ℝ
          (ambientCurvature
            (mfderiv I I' immersion.toFun x (tangentFrame i))
            (mfderiv I I' immersion.toFun x field)
            (mfderiv I I' immersion.toFun x test))
          (mfderiv I I' immersion.toFun x (tangentFrame i)) :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = _ := real_inner_comm _ _
  have tangentProjectionIdentity :
      immersion.orthogonalSplitting.tangentProjection x ambientRicci =
        ricciActionOfCurvatureTensor
            (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting ambientConnection x ambientRegular) field +
          normalFrameAmbientRicciActionAt immersion.toSmoothImmersionData
            immersion.orthogonalSplitting ambientConnection x ambientRegular normalFrame
            field := by
    apply ext_inner_right ℝ
    intro test
    change inner ℝ ((mfderiv I I' immersion.toFun x).adjoint ambientRicci) test = _
    calc
      _ = inner ℝ ambientRicci (mfderiv I I' immersion.toFun x test) :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = (∑ i, inner ℝ
              (mfderiv I I' immersion.toFun x (tangentFrame i))
              (ambientCurvature
                (mfderiv I I' immersion.toFun x (tangentFrame i))
                (mfderiv I I' immersion.toFun x field)
                (mfderiv I I' immersion.toFun x test))) +
            ∑ l, inner ℝ
              (normalFrame l : TangentSpace I' (immersion.toFun x))
              (ambientCurvature
                (normalFrame l : TangentSpace I' (immersion.toFun x))
                (mfderiv I I' immersion.toFun x field)
                (mfderiv I I' immersion.toFun x test)) := by
        rw [ambientTrace, Fintype.sum_sum_type]
        simp only [adaptedFrame,
          SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt_apply_inl,
          SmoothIsometricImmersionData.adaptedAmbientOrthonormalBasisAt_apply_inr]
      _ = inner ℝ
            (ricciActionOfCurvatureTensor
              (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
                immersion.orthogonalSplitting ambientConnection x ambientRegular) field)
            test +
          inner ℝ
            (normalFrameAmbientRicciActionAt immersion.toSmoothImmersionData
              immersion.orthogonalSplitting ambientConnection x ambientRegular normalFrame
              field) test := by
        rw [tangentTrace,
          normalFrameAmbientRicciActionAt_inner]
      _ = _ := (inner_add_left _ _ _).symm
  change ambientRicci = _
  rw [← immersion.hasTangentNormalDecomposition x ambientRicci,
    tangentProjectionIdentity]

/-! ## The differentiated Gauss identity -/

/-- The covariant derivative of the second fundamental form, constructed from the normal
connection, the induced tangent connection, and the same field-level second fundamental form:

`(∇ᴮ_W II)(X,Y) = ∇⊥_W (II(X,Y)) - II(∇_W X,Y) - II(X,∇_W Y)`.

This is an actual field along the immersion.  Its pointwise tensor realization is constructed
later from canonical linear extensions. -/
def CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (direction first second : (y : M) → TangentSpace I y) :
    AmbientVectorFieldAlong immersion :=
  let induced := extensions.inducedCovariantDerivative immersion splitting ambientConnection
    leftInverse
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientConnection
  extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientConnection direction (secondFundamental first second) -
    secondFundamental (covariantDerivativeAlong I induced direction first) second -
    secondFundamental first (covariantDerivativeAlong I induced direction second)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- The constructed covariant derivative of `II` remains in the normal summand. -/
theorem CovariantSubmanifoldFieldExtensionData.tangentProjection_covariantDerivativeSecondFundamentalAlong_eq_zero
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (direction first second : (y : M) → TangentSpace I y) (x : M) :
    splitting.tangentProjection x
        (extensions.covariantDerivativeSecondFundamentalAlong immersion splitting
          ambientConnection leftInverse direction first second x) = 0 := by
  let induced := extensions.inducedCovariantDerivative immersion splitting ambientConnection
    leftInverse
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientConnection
  rw [CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong]
  simp only [Pi.sub_apply, map_sub]
  rw [extensions.toSubmanifoldFieldExtensionData.tangentProjection_normalDerivative_eq_zero
      immersion splitting ambientConnection decomposition leftInverse,
    extensions.toSubmanifoldFieldExtensionData.tangentProjection_secondFundamentalFormAlong_eq_zero
      immersion splitting ambientConnection decomposition leftInverse,
    extensions.toSubmanifoldFieldExtensionData.tangentProjection_secondFundamentalFormAlong_eq_zero
      immersion splitting ambientConnection decomposition leftInverse]
  simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Additivity of the field-level second fundamental form in its differentiated field, under
the exact differentiability hypotheses consumed by the ambient connection. -/
theorem CovariantSubmanifoldFieldExtensionData.secondFundamentalFormAlong_add_second_at
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {first second second' : (y : M) → TangentSpace I y} {x : M}
    (hsecond : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension second))
      (immersion.toFun x))
    (hsecond' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension second'))
      (immersion.toFun x)) :
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientConnection first (second + second') x =
      extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion splitting ambientConnection first second x +
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion splitting ambientConnection first second' x := by
  have connectionAdd := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.add hsecond hsecond')
    (mfderiv I I' immersion.toFun x (first x))
  simpa only [SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
    SubmanifoldFieldExtensionData.ambientDerivativeTangent, LinearMap.map_add,
    Pi.add_apply, add_apply, map_add] using
    congrArg (splitting.normalProjection x) connectionAdd

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Constant real scalars pull through the differentiated-field slot of the field-level second
fundamental form. -/
theorem CovariantSubmanifoldFieldExtensionData.secondFundamentalFormAlong_smul_second_at
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {first second : (y : M) → TangentSpace I y} {x : M}
    (scalar : ℝ)
    (hsecond : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension second))
      (immersion.toFun x)) :
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientConnection first (scalar • second) x =
      scalar • extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientConnection first second x := by
  have connectionSmul := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.smul_const scalar hsecond)
    (mfderiv I I' immersion.toFun x (first x))
  simpa only [SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
    SubmanifoldFieldExtensionData.ambientDerivativeTangent, LinearMap.map_smul,
    Pi.smul_apply, smul_apply, map_smul] using
    congrArg (splitting.normalProjection x) connectionSmul

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Additivity of the constructed normal connection in the normal-field slot. -/
theorem CovariantSubmanifoldFieldExtensionData.normalDerivative_add_normal_at
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction : (y : M) → TangentSpace I y}
    {normal normal' : AmbientVectorFieldAlong immersion} {x : M}
    (hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x))
    (hnormal' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal'))
      (immersion.toFun x)) :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientConnection direction (normal + normal') x =
      extensions.toSubmanifoldFieldExtensionData.normalDerivative
          immersion splitting ambientConnection direction normal x +
        extensions.toSubmanifoldFieldExtensionData.normalDerivative
          immersion splitting ambientConnection direction normal' x := by
  have connectionAdd := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.add hnormal hnormal')
    (mfderiv I I' immersion.toFun x (direction x))
  simpa only [SubmanifoldFieldExtensionData.normalDerivative,
    SubmanifoldFieldExtensionData.ambientDerivativeAlong, LinearMap.map_add,
    Pi.add_apply, add_apply, map_add] using
    congrArg (splitting.normalProjection x) connectionAdd

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Constant real scalars pull through the normal-field slot of the constructed normal
connection. -/
theorem CovariantSubmanifoldFieldExtensionData.normalDerivative_smul_normal_at
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction : (y : M) → TangentSpace I y}
    {normal : AmbientVectorFieldAlong immersion} {x : M}
    (scalar : ℝ)
    (hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x)) :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientConnection direction (scalar • normal) x =
      scalar • extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientConnection direction normal x := by
  have connectionSmul := DFunLike.congr_fun
    (ambientConnection.isCovariantDerivativeOn.smul_const scalar hnormal)
    (mfderiv I I' immersion.toFun x (direction x))
  simpa only [SubmanifoldFieldExtensionData.normalDerivative,
    SubmanifoldFieldExtensionData.ambientDerivativeAlong, LinearMap.map_smul,
    Pi.smul_apply, smul_apply, map_smul] using
    congrArg (splitting.normalProjection x) connectionSmul

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Levi--Civita restriction locality transports equality of normal-field germs through one
normal derivative. -/
theorem CovariantSubmanifoldFieldExtensionData.normalDerivative_eq_of_eventuallyEq
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction : (y : M) → TangentSpace I y}
    {normal normal' : AmbientVectorFieldAlong immersion} {x : M}
    (hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x))
    (hnormal' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal'))
      (immersion.toFun x))
    (agreement : normal =ᶠ[nhds x] normal') :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientLeviCivita.connection direction normal x =
      extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientLeviCivita.connection direction normal' x := by
  let eNormal := extensions.toSubmanifoldFieldExtensionData.alongExtension normal
  let eNormal' := extensions.toSubmanifoldFieldExtensionData.alongExtension normal'
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have restrictionAgreement :
      (fun y ↦ eNormal (immersion.toFun y)) =ᶠ[nhds x]
        (fun y ↦ eNormal' (immersion.toFun y)) :=
    agreement.mono fun y hy ↦ by
      simpa only [eNormal, eNormal',
        extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees] using hy
  have locality := ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    hImmersion hnormal hnormal' restrictionAgreement (direction x)
  exact congrArg (splitting.normalProjection x) locality

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Levi--Civita restriction locality transports an eventual additive identity between normal
fields along the immersion through one normal derivative.  This is the germ-level principle
needed when a chosen global extension operator does not itself preserve source germs. -/
theorem CovariantSubmanifoldFieldExtensionData.normalDerivative_eq_add_of_eventuallyEq
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction : (y : M) → TangentSpace I y}
    {normalSum normal normal' : AmbientVectorFieldAlong immersion} {x : M}
    (hnormalSum : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normalSum))
      (immersion.toFun x))
    (hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x))
    (hnormal' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal'))
      (immersion.toFun x))
    (agreement : normalSum =ᶠ[nhds x] normal + normal') :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientLeviCivita.connection direction normalSum x =
      extensions.toSubmanifoldFieldExtensionData.normalDerivative
          immersion splitting ambientLeviCivita.connection direction normal x +
        extensions.toSubmanifoldFieldExtensionData.normalDerivative
          immersion splitting ambientLeviCivita.connection direction normal' x := by
  let eSum := extensions.toSubmanifoldFieldExtensionData.alongExtension normalSum
  let eNormal := extensions.toSubmanifoldFieldExtensionData.alongExtension normal
  let eNormal' := extensions.toSubmanifoldFieldExtensionData.alongExtension normal'
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have hAdded : MDiffAt (T% (eNormal + eNormal')) (immersion.toFun x) :=
    mdifferentiableAt_add_section hnormal hnormal'
  have restrictionAgreement :
      (fun y ↦ eSum (immersion.toFun y)) =ᶠ[nhds x]
        (fun y ↦ (eNormal + eNormal') (immersion.toFun y)) :=
    agreement.mono fun y hy ↦ by
      simpa only [eSum, eNormal, eNormal', Pi.add_apply,
        extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees] using hy
  have locality := ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    hImmersion hnormalSum hAdded restrictionAgreement (direction x)
  have connectionAdd := DFunLike.congr_fun
    (ambientLeviCivita.connection.isCovariantDerivativeOn.add hnormal hnormal')
    (mfderiv I I' immersion.toFun x (direction x))
  change splitting.normalProjection x
      (ambientLeviCivita.connection eSum (immersion.toFun x)
        (mfderiv I I' immersion.toFun x (direction x))) =
    splitting.normalProjection x
        (ambientLeviCivita.connection eNormal (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (direction x))) +
      splitting.normalProjection x
        (ambientLeviCivita.connection eNormal' (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (direction x)))
  rw [locality, connectionAdd]
  simp only [add_apply, map_add]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Scalar version of the preceding germ-local normal-derivative principle. -/
theorem CovariantSubmanifoldFieldExtensionData.normalDerivative_eq_smul_of_eventuallyEq
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction : (y : M) → TangentSpace I y}
    {normalScaled normal : AmbientVectorFieldAlong immersion} {x : M}
    (scalar : ℝ)
    (hnormalScaled : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normalScaled))
      (immersion.toFun x))
    (hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x))
    (agreement : normalScaled =ᶠ[nhds x] scalar • normal) :
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientLeviCivita.connection direction normalScaled x =
      scalar • extensions.toSubmanifoldFieldExtensionData.normalDerivative
        immersion splitting ambientLeviCivita.connection direction normal x := by
  let eScaled := extensions.toSubmanifoldFieldExtensionData.alongExtension normalScaled
  let eNormal := extensions.toSubmanifoldFieldExtensionData.alongExtension normal
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have hAmbientScaled : MDiffAt (T% (scalar • eNormal)) (immersion.toFun x) :=
    mdifferentiableAt_const.smul_section hnormal
  have restrictionAgreement :
      (fun y ↦ eScaled (immersion.toFun y)) =ᶠ[nhds x]
        (fun y ↦ (scalar • eNormal) (immersion.toFun y)) :=
    agreement.mono fun y hy ↦ by
      simpa only [eScaled, eNormal, Pi.smul_apply,
        extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees] using hy
  have locality := ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    hImmersion hnormalScaled hAmbientScaled restrictionAgreement (direction x)
  have connectionSmul := DFunLike.congr_fun
    (ambientLeviCivita.connection.isCovariantDerivativeOn.smul_const scalar hnormal)
    (mfderiv I I' immersion.toFun x (direction x))
  change splitting.normalProjection x
      (ambientLeviCivita.connection eScaled (immersion.toFun x)
        (mfderiv I I' immersion.toFun x (direction x))) =
    scalar • splitting.normalProjection x
      (ambientLeviCivita.connection eNormal (immersion.toFun x)
        (mfderiv I I' immersion.toFun x (direction x)))
  rw [locality, connectionSmul]
  simp only [smul_apply, map_smul]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Germ-local additive transport for the differentiated-field slot of the second fundamental
form, obtained from Levi--Civita restriction locality and the tangent-extension agreement law. -/
theorem CovariantSubmanifoldFieldExtensionData.secondFundamentalFormAlong_eq_add_of_eventuallyEq
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction fieldSum field field' : (y : M) → TangentSpace I y} {x : M}
    (hfieldSum : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldSum))
      (immersion.toFun x))
    (hfield : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension field))
      (immersion.toFun x))
    (hfield' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension field'))
      (immersion.toFun x))
    (agreement : fieldSum =ᶠ[nhds x] field + field') :
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientLeviCivita.connection direction fieldSum x =
      extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion splitting ambientLeviCivita.connection direction field x +
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion splitting ambientLeviCivita.connection direction field' x := by
  let eSum := extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldSum
  let eField := extensions.toSubmanifoldFieldExtensionData.tangentExtension field
  let eField' := extensions.toSubmanifoldFieldExtensionData.tangentExtension field'
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have hAdded : MDiffAt (T% (eField + eField')) (immersion.toFun x) :=
    mdifferentiableAt_add_section hfield hfield'
  have restrictionAgreement :
      (fun y ↦ eSum (immersion.toFun y)) =ᶠ[nhds x]
        (fun y ↦ (eField + eField') (immersion.toFun y)) :=
    agreement.mono fun y hy ↦ by
      calc
        eSum (immersion.toFun y) =
            mfderiv I I' immersion.toFun y (fieldSum y) :=
          extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees fieldSum y
        _ = mfderiv I I' immersion.toFun y ((field + field') y) :=
          congrArg (mfderiv I I' immersion.toFun y) hy
        _ = extensions.toSubmanifoldFieldExtensionData.tangentExtension
            (field + field') (immersion.toFun y) :=
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
            (field + field') y).symm
        _ = (eField + eField') (immersion.toFun y) := by
          exact congrFun
            (extensions.toSubmanifoldFieldExtensionData.tangentExtension.map_add field field')
            (immersion.toFun y)
  have locality := ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    hImmersion hfieldSum hAdded restrictionAgreement (direction x)
  have connectionAdd := DFunLike.congr_fun
    (ambientLeviCivita.connection.isCovariantDerivativeOn.add hfield hfield')
    (mfderiv I I' immersion.toFun x (direction x))
  change splitting.normalProjection x
      (ambientLeviCivita.connection eSum (immersion.toFun x)
        (mfderiv I I' immersion.toFun x (direction x))) =
    splitting.normalProjection x
        (ambientLeviCivita.connection eField (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (direction x))) +
      splitting.normalProjection x
        (ambientLeviCivita.connection eField' (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (direction x)))
  rw [locality, connectionAdd]
  simp only [add_apply, map_add]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Scalar version of germ-local transport for the differentiated-field slot of `II`. -/
theorem CovariantSubmanifoldFieldExtensionData.secondFundamentalFormAlong_eq_smul_of_eventuallyEq
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    {direction fieldScaled field : (y : M) → TangentSpace I y} {x : M}
    (scalar : ℝ)
    (hfieldScaled : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldScaled))
      (immersion.toFun x))
    (hfield : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension field))
      (immersion.toFun x))
    (agreement : fieldScaled =ᶠ[nhds x] scalar • field) :
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientLeviCivita.connection direction fieldScaled x =
      scalar • extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
        immersion splitting ambientLeviCivita.connection direction field x := by
  let eScaled := extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldScaled
  let eField := extensions.toSubmanifoldFieldExtensionData.tangentExtension field
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have hAmbientScaled : MDiffAt (T% (scalar • eField)) (immersion.toFun x) :=
    mdifferentiableAt_const.smul_section hfield
  have restrictionAgreement :
      (fun y ↦ eScaled (immersion.toFun y)) =ᶠ[nhds x]
        (fun y ↦ (scalar • eField) (immersion.toFun y)) :=
    agreement.mono fun y hy ↦ by
      calc
        eScaled (immersion.toFun y) =
            mfderiv I I' immersion.toFun y (fieldScaled y) :=
          extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees fieldScaled y
        _ = mfderiv I I' immersion.toFun y ((scalar • field) y) :=
          congrArg (mfderiv I I' immersion.toFun y) hy
        _ = extensions.toSubmanifoldFieldExtensionData.tangentExtension
            (scalar • field) (immersion.toFun y) :=
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
            (scalar • field) y).symm
        _ = (scalar • eField) (immersion.toFun y) := by
          exact congrFun
            (extensions.toSubmanifoldFieldExtensionData.tangentExtension.map_smul scalar field)
            (immersion.toFun y)
  have locality := ambientLeviCivita.eq_on_mfderiv_of_comp_eventuallyEq I'
    hImmersion hfieldScaled hAmbientScaled restrictionAgreement (direction x)
  have connectionSmul := DFunLike.congr_fun
    (ambientLeviCivita.connection.isCovariantDerivativeOn.smul_const scalar hfield)
    (mfderiv I I' immersion.toFun x (direction x))
  change splitting.normalProjection x
      (ambientLeviCivita.connection eScaled (immersion.toFun x)
        (mfderiv I I' immersion.toFun x (direction x))) =
    scalar • splitting.normalProjection x
      (ambientLeviCivita.connection eField (immersion.toFun x)
        (mfderiv I I' immersion.toFun x (direction x)))
  rw [locality, connectionSmul]
  simp only [smul_apply, map_smul]
  rfl

/-- The analytic regularity needed to differentiate the Gauss splitting on the canonical fields
used by the pointwise second fundamental form.  The fields of this structure are regularity
statements only: no curvature, bracket, Gauss, or shape identity is assumed.

The first field says that extending a canonical source tangent field into the ambient manifold
preserves the `C²` regularity required by the curvature tensor.  The second says that the chosen
ambient extension of each normal Gauss term is differentiable, so it may be differentiated once
in the Weingarten term. -/
structure CovariantSubmanifoldFieldExtensionData.HasDifferentiatedGaussRegularityAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (x : M) : Prop where
  tangentExtension_contMDiffAt_two : ∀ field : TangentSpace I x,
    CMDiffAt 2
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension
        (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field)))
      (immersion.toFun x)
  normalGaussExtension_mdifferentiableAt : ∀ first field : TangentSpace I x,
    MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion splitting ambientConnection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field))))
      (immersion.toFun x)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- The field-level shape operator is adjoint to the constructed second fundamental form.
The normal field is allowed to vary; only differentiability of its chosen ambient extension and
pointwise orthogonality to the immersed tangent spaces are required. -/
theorem shapeOperatorAlong_inner_secondFundamentalFormAlong
    [IsManifold I 2 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    {first test : (y : M) → TangentSpace I y}
    (normal : AmbientVectorFieldAlong immersion.toSmoothImmersionData)
    {x : M}
    (hfirst : MDiffAt (T% first) x)
    (htest : MDiffAt (T% test) x)
    (hnormalExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x))
    (normalOrthogonal : ∀ y tangent,
      inner ℝ (normal y) (mfderiv I I' immersion.toFun y tangent) = 0) :
    inner ℝ
        (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection first normal x)
        (test x) =
      inner ℝ
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection first test x)
        (normal x) := by
  let eFirst :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension first
  let eTest := extensions.toSubmanifoldFieldExtensionData.tangentExtension test
  let eNormal := extensions.toSubmanifoldFieldExtensionData.alongExtension normal
  let ambientInner : N → ℝ := fun y ↦ inner ℝ (eTest y) (eNormal y)
  have hfirstExtension : MDiffAt (T% eFirst) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hfirst
  have htestExtension : MDiffAt (T% eTest) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt htest
  have hnormalExtension' : MDiffAt (T% eNormal) (immersion.toFun x) := by
    exact hnormalExtension
  have hambientInner : MDiffAt ambientInner (immersion.toFun x) :=
    MDifferentiableAt.inner_bundle
      (E := (TangentSpace I' : N → Type _)) htestExtension hnormalExtension'
  have innerAlong_zero : ambientInner ∘ immersion.toFun = fun _ : M ↦ 0 := by
    funext y
    change inner ℝ (eTest (immersion.toFun y)) (eNormal (immersion.toFun y)) = 0
    dsimp only [eTest, eNormal]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees test y]
    rw [extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees normal y]
    rw [real_inner_comm, normalOrthogonal]
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have chain := mfderiv_comp_apply x hambientInner hImmersion (first x)
  have ambientDerivative_zero :
      d% ambientInner (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (first x)) = 0 := by
    calc
      _ = d% (ambientInner ∘ immersion.toFun) x (first x) := chain.symm
      _ = d% (fun _ : M ↦ (0 : ℝ)) x (first x) := by rw [innerAlong_zero]
      _ = 0 := by
        rw [mvfderiv_const]
        rfl
  have eFirstValue : eFirst (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (first x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x
  have eTestValue : eTest (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (test x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees test x
  have eNormalValue : eNormal (immersion.toFun x) = normal x :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees normal x
  have metricIdentity := ambientLeviCivita.metricCompatible
    hfirstExtension htestExtension hnormalExtension'
  rw [eFirstValue, eTestValue, eNormalValue, ambientDerivative_zero] at metricIdentity
  have gaussIdentity :=
    extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse first test x
  have pairedGauss := congrArg (fun ambient : TangentSpace I' (immersion.toFun x) ↦
    inner ℝ ambient (normal x)) gaussIdentity
  have tangentPairingZero :
      inner ℝ
          (mfderiv I I' immersion.toFun x
            (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
              immersion.orthogonalSplitting ambientLeviCivita.connection
              immersion.hasTangentProjectionLeftInverse test x (first x)))
          (normal x) = 0 := by
    rw [real_inner_comm]
    exact normalOrthogonal x _
  rw [inner_add_left, tangentPairingZero, zero_add] at pairedGauss
  have firstPairing :
      inner ℝ
          (ambientLeviCivita.connection eTest (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (first x)))
          (normal x) =
        inner ℝ
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first test x)
          (normal x) := by
    simpa [SubmanifoldFieldExtensionData.ambientDerivativeTangent, eTest] using pairedGauss
  have shapePairing :
      inner ℝ
          (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first normal x)
          (test x) =
        -inner ℝ
          (ambientLeviCivita.connection eNormal (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (first x)))
          (mfderiv I I' immersion.toFun x (test x)) := by
    change inner ℝ
        (-((mfderiv I I' immersion.toFun x).adjoint
          (ambientLeviCivita.connection eNormal (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (first x))))) (test x) = _
    rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  rw [shapePairing]
  rw [← firstPairing]
  rw [real_inner_comm
    (ambientLeviCivita.connection eNormal (immersion.toFun x)
      (mfderiv I I' immersion.toFun x (first x)))
    (mfderiv I I' immersion.toFun x (test x))] at metricIdentity
  linarith

/-- On the canonical source extensions used to construct the pointwise second fundamental form,
the Riesz-defined pointwise shape operator agrees with the differentiate-then-project field-level
shape operator.  The only extra premise is differentiability of the chosen ambient extension of
the normal Gauss term being differentiated. -/
theorem shapeOperatorOfProjectedSecondFundamentalAt_eq_shapeOperatorAlong
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : N, FiniteDimensional ℝ (TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (x : M) (first second field : TangentSpace I x)
    (hnormalExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second)
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field))))
      (immersion.toFun x)) :
    shapeOperatorOfSecondFundamental
        (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
          immersion.hasTangentProjectionLeftInverse x)
        (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
          immersion.hasTangentProjectionLeftInverse x second field)
        first =
      extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection
        (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second)
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field)) x := by
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let fieldField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field
  let normal :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection secondField fieldField
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  apply ext_inner_right ℝ
  intro test
  let testField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x test
  have normalOrthogonal : ∀ y tangent,
      inner ℝ (normal y) (mfderiv I I' immersion.toFun y tangent) = 0 := by
    intro y tangent
    exact immersion.hasOrthogonalNormalProjection y
      (extensions.toSubmanifoldFieldExtensionData.ambientDerivativeTangent
        immersion.toSmoothImmersionData ambientLeviCivita.connection
        secondField fieldField y) tangent
  have shapePairing :=
    shapeOperatorAlong_inner_secondFundamentalFormAlong
      immersion ambientLeviCivita extensions normal
      (x := x)
      (hfirst := SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
        (I := I) x first)
      (htest := SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
        (I := I) x test)
      (hnormalExtension := by simpa [normal, secondField, fieldField] using hnormalExtension)
      normalOrthogonal
  change inner ℝ
      (shapeOperatorOfSecondFundamental pointII (pointII second field) first) test = _
  rw [shapeOperatorOfSecondFundamental_inner]
  have shapePairing' :
      inner ℝ
          (extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection firstField normal x)
          test =
        inner ℝ
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection firstField testField x)
          (normal x) := by
    simpa [testField] using shapePairing
  rw [shapePairing']
  simp [pointII, normal, firstField, secondField, fieldField, testField,
    SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
    SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  rfl

omit [FiniteDimensional ℝ E]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Field-level tangential Gauss equation obtained by differentiating the constructed Gauss
splitting.  The two explicit extension hypotheses are regularity statements, not geometric
identities: the differentiated tangent extension is `C²`, and the ambient extensions of the two
normal Gauss terms are differentiable. -/
theorem inducedCurvatureAction_eq_tangentialAmbient_add_shape
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
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
      (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse) x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    {first second field : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) x)
    (hsecond : MDiffAt (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x)
    (hfieldExtension : CMDiffAt 2
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension field))
      (immersion.toFun x))
    (hnormalSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection second field)))
      (immersion.toFun x))
    (hnormalFirstExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection first field)))
      (immersion.toFun x)) :
    connectionCurvatureAction I
        (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection
          immersion.hasTangentProjectionLeftInverse)
        first second field x =
      immersion.orthogonalSplitting.tangentProjection x
        (connectionCurvatureAction I' ambientLeviCivita.connection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension first)
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension field)
          (immersion.toFun x)) +
        extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection first
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second field) x -
        extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection second
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first field) x := by
  let induced :=
    extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentProjectionLeftInverse
  let eFirst :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension first
  let eSecond :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension second
  let eField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension field
  let intrinsicSecond := covariantDerivativeAlong I induced second field
  let intrinsicFirst := covariantDerivativeAlong I induced first field
  let normalSecond :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection second field
  let normalFirst :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection first field
  let tangentSecondExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension intrinsicSecond
  let tangentFirstExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension intrinsicFirst
  let normalSecondExtension :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension normalSecond
  let normalFirstExtension :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension normalFirst
  let comparisonSecond := tangentSecondExtension + normalSecondExtension
  let comparisonFirst := tangentFirstExtension + normalFirstExtension
  let ambientSecond :=
    covariantDerivativeAlong I' ambientLeviCivita.connection eSecond eField
  let ambientFirst :=
    covariantDerivativeAlong I' ambientLeviCivita.connection eFirst eField
  have hfirstExtension : MDiffAt (T% eFirst) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hfirst
  have hsecondExtension : MDiffAt (T% eSecond) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hsecond
  have hintrinsicSecond : MDiffAt (T% intrinsicSecond) x :=
    intrinsicRegular second field hsecond hfield
  have hintrinsicFirst : MDiffAt (T% intrinsicFirst) x :=
    intrinsicRegular first field hfirst hfield
  have htangentSecondExtension :
      MDiffAt (T% tangentSecondExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hintrinsicSecond
  have htangentFirstExtension :
      MDiffAt (T% tangentFirstExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hintrinsicFirst
  have hnormalSecondExtension' :
      MDiffAt (T% normalSecondExtension) (immersion.toFun x) := by
    exact hnormalSecondExtension
  have hnormalFirstExtension' :
      MDiffAt (T% normalFirstExtension) (immersion.toFun x) := by
    exact hnormalFirstExtension
  have hcomparisonSecond : MDiffAt (T% comparisonSecond) (immersion.toFun x) :=
    mdifferentiableAt_add_section htangentSecondExtension hnormalSecondExtension'
  have hcomparisonFirst : MDiffAt (T% comparisonFirst) (immersion.toFun x) :=
    mdifferentiableAt_add_section htangentFirstExtension hnormalFirstExtension'
  have hambientSecond : MDiffAt (T% ambientSecond) (immersion.toFun x) :=
    ambientRegular eSecond eField hsecondExtension hfieldExtension
  have hambientFirst : MDiffAt (T% ambientFirst) (immersion.toFun x) :=
    ambientRegular eFirst eField hfirstExtension hfieldExtension
  have ambientSecond_agrees (y : M) :
      ambientSecond (immersion.toFun y) = comparisonSecond (immersion.toFun y) := by
    dsimp only [ambientSecond, comparisonSecond, tangentSecondExtension,
      normalSecondExtension, intrinsicSecond, normalSecond, eSecond, eField,
      covariantDerivativeAlong]
    simp only [Pi.add_apply]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second y]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
      (covariantDerivativeAlong I induced second field) y]
    rw [extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees]
    exact extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse second field y
  have ambientFirst_agrees (y : M) :
      ambientFirst (immersion.toFun y) = comparisonFirst (immersion.toFun y) := by
    dsimp only [ambientFirst, comparisonFirst, tangentFirstExtension,
      normalFirstExtension, intrinsicFirst, normalFirst, eFirst, eField,
      covariantDerivativeAlong]
    simp only [Pi.add_apply]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first y]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
      (covariantDerivativeAlong I induced first field) y]
    rw [extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees]
    exact extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse first field y
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have outerFirst := ambientLeviCivita.eq_on_mfderiv_of_comp_eq I'
    hImmersion hambientSecond hcomparisonSecond ambientSecond_agrees (first x)
  have outerSecond := ambientLeviCivita.eq_on_mfderiv_of_comp_eq I'
    hImmersion hambientFirst hcomparisonFirst ambientFirst_agrees (second x)
  have projectedComparisonSecond :
      immersion.orthogonalSplitting.tangentProjection x
          (ambientLeviCivita.connection comparisonSecond (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (first x))) =
        induced intrinsicSecond x (first x) -
          extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first normalSecond x := by
    change immersion.orthogonalSplitting.tangentProjection x
        (ambientLeviCivita.connection
          (tangentSecondExtension + normalSecondExtension) (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (first x))) = _
    rw [DFunLike.congr_fun
      (ambientLeviCivita.connection.isCovariantDerivativeOn.add
        htangentSecondExtension hnormalSecondExtension')]
    simp only [add_apply, map_add]
    simp [induced, intrinsicSecond, tangentSecondExtension, normalSecondExtension,
      SubmanifoldFieldExtensionData.shapeOperatorAlong]
    rfl
  have projectedComparisonFirst :
      immersion.orthogonalSplitting.tangentProjection x
          (ambientLeviCivita.connection comparisonFirst (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (second x))) =
        induced intrinsicFirst x (second x) -
          extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second normalFirst x := by
    change immersion.orthogonalSplitting.tangentProjection x
        (ambientLeviCivita.connection
          (tangentFirstExtension + normalFirstExtension) (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (second x))) = _
    rw [DFunLike.congr_fun
      (ambientLeviCivita.connection.isCovariantDerivativeOn.add
        htangentFirstExtension hnormalFirstExtension')]
    simp only [add_apply, map_add]
    simp [induced, intrinsicFirst, tangentFirstExtension, normalFirstExtension,
      SubmanifoldFieldExtensionData.shapeOperatorAlong]
    rfl
  have eFirstValue : eFirst (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (first x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x
  have eSecondValue : eSecond (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (second x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second x
  have projectedOuterFirst :
      immersion.orthogonalSplitting.tangentProjection x
          (ambientLeviCivita.connection ambientSecond (immersion.toFun x)
            (eFirst (immersion.toFun x))) =
        induced intrinsicSecond x (first x) -
          extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first normalSecond x := by
    rw [eFirstValue, outerFirst, projectedComparisonSecond]
  have projectedOuterSecond :
      immersion.orthogonalSplitting.tangentProjection x
          (ambientLeviCivita.connection ambientFirst (immersion.toFun x)
            (eSecond (immersion.toFun x))) =
        induced intrinsicFirst x (second x) -
          extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second normalFirst x := by
    rw [eSecondValue, outerSecond, projectedComparisonFirst]
  have bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData :=
    extensions.hasBracketCompatibility immersion.toSmoothImmersionData
  have projectedBracket :
      immersion.orthogonalSplitting.tangentProjection x
          (ambientLeviCivita.connection eField (immersion.toFun x)
            (VectorField.mlieBracket I' eFirst eSecond (immersion.toFun x))) =
        induced field x (VectorField.mlieBracket I first second x) := by
    rw [bracketCompatibility hfirst hsecond]
    rfl
  rw [connectionCurvatureAction, connectionCurvatureAction]
  simp only [Pi.sub_apply, map_sub]
  change
    induced intrinsicSecond x (first x) - induced intrinsicFirst x (second x) -
          induced field x (VectorField.mlieBracket I first second x) =
      (immersion.orthogonalSplitting.tangentProjection x
            (ambientLeviCivita.connection ambientSecond (immersion.toFun x)
              (eFirst (immersion.toFun x))) -
          immersion.orthogonalSplitting.tangentProjection x
            (ambientLeviCivita.connection ambientFirst (immersion.toFun x)
              (eSecond (immersion.toFun x))) -
          immersion.orthogonalSplitting.tangentProjection x
            (ambientLeviCivita.connection eField (immersion.toFun x)
              (VectorField.mlieBracket I' eFirst eSecond (immersion.toFun x)))) + _ - _
  rw [projectedOuterFirst, projectedOuterSecond, projectedBracket]
  abel

omit [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- The normal projection of the same differentiated Gauss identity is the uncontracted
Codazzi equation in the CCG25 convention:

`(R̃(W,X)Y)⊥ = (∇ᴮ_W II)(X,Y) - (∇ᴮ_X II)(W,Y)`.

Both sides are constructed from the one isometric immersion, its induced connection, the
ambient Levi--Civita connection, and the covariant extension operator.  The hypotheses beyond
that geometry are exactly the regularity needed by the twice-differentiated Gauss calculation. -/
theorem ambientCurvatureAction_normalProjection_eq_covariantDerivativeSecondFundamental_sub
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
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
      (extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentProjectionLeftInverse) x)
    (ambientRegular : HasConnectionCurvatureRegularityAt I'
      ambientLeviCivita.connection (immersion.toFun x))
    {first second field : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) x)
    (hsecond : MDiffAt (T% second) x)
    (hfield : CMDiffAt 2 (T% field) x)
    (hfieldExtension : CMDiffAt 2
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension field))
      (immersion.toFun x))
    (hnormalSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection second field)))
      (immersion.toFun x))
    (hnormalFirstExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection first field)))
      (immersion.toFun x)) :
    immersion.orthogonalSplitting.normalProjection x
        (connectionCurvatureAction I' ambientLeviCivita.connection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension first)
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension second)
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension field)
          (immersion.toFun x)) =
      extensions.covariantDerivativeSecondFundamentalAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
          first second field x -
        extensions.covariantDerivativeSecondFundamentalAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
          second first field x := by
  let induced :=
    extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentProjectionLeftInverse
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let eFirst :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension first
  let eSecond :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension second
  let eField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension field
  let intrinsicSecond := covariantDerivativeAlong I induced second field
  let intrinsicFirst := covariantDerivativeAlong I induced first field
  let normalSecond :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection second field
  let normalFirst :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection first field
  let tangentSecondExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension intrinsicSecond
  let tangentFirstExtension :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension intrinsicFirst
  let normalSecondExtension :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension normalSecond
  let normalFirstExtension :=
    extensions.toSubmanifoldFieldExtensionData.alongExtension normalFirst
  let comparisonSecond := tangentSecondExtension + normalSecondExtension
  let comparisonFirst := tangentFirstExtension + normalFirstExtension
  let ambientSecond :=
    covariantDerivativeAlong I' ambientLeviCivita.connection eSecond eField
  let ambientFirst :=
    covariantDerivativeAlong I' ambientLeviCivita.connection eFirst eField
  have hfirstExtension : MDiffAt (T% eFirst) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hfirst
  have hsecondExtension : MDiffAt (T% eSecond) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hsecond
  have hintrinsicSecond : MDiffAt (T% intrinsicSecond) x :=
    intrinsicRegular second field hsecond hfield
  have hintrinsicFirst : MDiffAt (T% intrinsicFirst) x :=
    intrinsicRegular first field hfirst hfield
  have htangentSecondExtension :
      MDiffAt (T% tangentSecondExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hintrinsicSecond
  have htangentFirstExtension :
      MDiffAt (T% tangentFirstExtension) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hintrinsicFirst
  have hnormalSecondExtension' :
      MDiffAt (T% normalSecondExtension) (immersion.toFun x) := by
    exact hnormalSecondExtension
  have hnormalFirstExtension' :
      MDiffAt (T% normalFirstExtension) (immersion.toFun x) := by
    exact hnormalFirstExtension
  have hcomparisonSecond : MDiffAt (T% comparisonSecond) (immersion.toFun x) :=
    mdifferentiableAt_add_section htangentSecondExtension hnormalSecondExtension'
  have hcomparisonFirst : MDiffAt (T% comparisonFirst) (immersion.toFun x) :=
    mdifferentiableAt_add_section htangentFirstExtension hnormalFirstExtension'
  have hambientSecond : MDiffAt (T% ambientSecond) (immersion.toFun x) :=
    ambientRegular eSecond eField hsecondExtension hfieldExtension
  have hambientFirst : MDiffAt (T% ambientFirst) (immersion.toFun x) :=
    ambientRegular eFirst eField hfirstExtension hfieldExtension
  have ambientSecond_agrees (y : M) :
      ambientSecond (immersion.toFun y) = comparisonSecond (immersion.toFun y) := by
    dsimp only [ambientSecond, comparisonSecond, tangentSecondExtension,
      normalSecondExtension, intrinsicSecond, normalSecond, eSecond, eField,
      covariantDerivativeAlong]
    simp only [Pi.add_apply]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second y]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
      (covariantDerivativeAlong I induced second field) y]
    rw [extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees]
    exact extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse second field y
  have ambientFirst_agrees (y : M) :
      ambientFirst (immersion.toFun y) = comparisonFirst (immersion.toFun y) := by
    dsimp only [ambientFirst, comparisonFirst, tangentFirstExtension,
      normalFirstExtension, intrinsicFirst, normalFirst, eFirst, eField,
      covariantDerivativeAlong]
    simp only [Pi.add_apply]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first y]
    rw [extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees
      (covariantDerivativeAlong I induced first field) y]
    rw [extensions.toSubmanifoldFieldExtensionData.alongExtension_agrees]
    exact extensions.ambientDerivativeTangent_eq_gauss_inducedCovariantDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse first field y
  have hImmersion : MDiffAt immersion.toFun x :=
    immersion.contMDiff.mdifferentiableAt (by simp)
  have outerFirst := ambientLeviCivita.eq_on_mfderiv_of_comp_eq I'
    hImmersion hambientSecond hcomparisonSecond ambientSecond_agrees (first x)
  have outerSecond := ambientLeviCivita.eq_on_mfderiv_of_comp_eq I'
    hImmersion hambientFirst hcomparisonFirst ambientFirst_agrees (second x)
  have projectedComparisonSecond :
      immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection comparisonSecond (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (first x))) =
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first intrinsicSecond x +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first normalSecond x := by
    change immersion.orthogonalSplitting.normalProjection x
        (ambientLeviCivita.connection
          (tangentSecondExtension + normalSecondExtension) (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (first x))) = _
    rw [DFunLike.congr_fun
      (ambientLeviCivita.connection.isCovariantDerivativeOn.add
        htangentSecondExtension hnormalSecondExtension')]
    simp only [add_apply, map_add]
    simp [intrinsicSecond, tangentSecondExtension, normalSecondExtension,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent,
      SubmanifoldFieldExtensionData.ambientDerivativeAlong,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.normalDerivative]
  have projectedComparisonFirst :
      immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection comparisonFirst (immersion.toFun x)
            (mfderiv I I' immersion.toFun x (second x))) =
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second intrinsicFirst x +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second normalFirst x := by
    change immersion.orthogonalSplitting.normalProjection x
        (ambientLeviCivita.connection
          (tangentFirstExtension + normalFirstExtension) (immersion.toFun x)
          (mfderiv I I' immersion.toFun x (second x))) = _
    rw [DFunLike.congr_fun
      (ambientLeviCivita.connection.isCovariantDerivativeOn.add
        htangentFirstExtension hnormalFirstExtension')]
    simp only [add_apply, map_add]
    simp [intrinsicFirst, tangentFirstExtension, normalFirstExtension,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent,
      SubmanifoldFieldExtensionData.ambientDerivativeAlong,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.normalDerivative]
  have eFirstValue : eFirst (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (first x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees first x
  have eSecondValue : eSecond (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (second x) :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees second x
  have projectedOuterFirst :
      immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection ambientSecond (immersion.toFun x)
            (eFirst (immersion.toFun x))) =
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first intrinsicSecond x +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection first normalSecond x := by
    rw [eFirstValue, outerFirst, projectedComparisonSecond]
  have projectedOuterSecond :
      immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection ambientFirst (immersion.toFun x)
            (eSecond (immersion.toFun x))) =
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second intrinsicFirst x +
          extensions.toSubmanifoldFieldExtensionData.normalDerivative
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection second normalFirst x := by
    rw [eSecondValue, outerSecond, projectedComparisonFirst]
  have bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData :=
    extensions.hasBracketCompatibility immersion.toSmoothImmersionData
  have projectedBracket :
      immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection eField (immersion.toFun x)
            (VectorField.mlieBracket I' eFirst eSecond (immersion.toFun x))) =
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection (VectorField.mlieBracket I first second) field x := by
    rw [bracketCompatibility hfirst hsecond]
    rfl
  have inducedTorsion :
      induced second x (first x) - induced first x (second x) =
        VectorField.mlieBracket I first second x := by
    exact (CovariantDerivative.torsion_eq_zero_iff induced).mp
      (extensions.inducedCovariantDerivative_torsionFree
        immersion.toSmoothImmersionData immersion.orthogonalSplitting
        ambientLeviCivita.connection immersion.hasTangentProjectionLeftInverse
        ambientLeviCivita.torsionFree bracketCompatibility) hfirst hsecond
  have bracketSecondFundamental :
      extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection (VectorField.mlieBracket I first second) field x =
        extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection
          (covariantDerivativeAlong I induced first second -
            covariantDerivativeAlong I induced second first) field x := by
    change immersion.orthogonalSplitting.normalProjection x
        (ambientLeviCivita.connection eField (immersion.toFun x)
          (mfderiv I I' immersion.toFun x
            (VectorField.mlieBracket I first second x))) =
      immersion.orthogonalSplitting.normalProjection x
        (ambientLeviCivita.connection eField (immersion.toFun x)
          (mfderiv I I' immersion.toFun x
            (induced second x (first x) - induced first x (second x))))
    rw [inducedTorsion]
  rw [connectionCurvatureAction]
  simp only [Pi.sub_apply, map_sub]
  change
    immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection ambientSecond (immersion.toFun x)
            (eFirst (immersion.toFun x))) -
        immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection ambientFirst (immersion.toFun x)
            (eSecond (immersion.toFun x))) -
        immersion.orthogonalSplitting.normalProjection x
          (ambientLeviCivita.connection eField (immersion.toFun x)
            (VectorField.mlieBracket I' eFirst eSecond (immersion.toFun x))) = _
  rw [projectedOuterFirst, projectedOuterSecond, projectedBracket]
  rw [CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong,
    CovariantSubmanifoldFieldExtensionData.covariantDerivativeSecondFundamentalAlong]
  simp only [Pi.sub_apply]
  rw [bracketSecondFundamental]
  change
    secondFundamental first intrinsicSecond x + normalDerivative first normalSecond x -
          (secondFundamental second intrinsicFirst x +
            normalDerivative second normalFirst x) -
        secondFundamental
          (covariantDerivativeAlong I induced first second -
            covariantDerivativeAlong I induced second first) field x =
      (normalDerivative first normalSecond x -
          secondFundamental (covariantDerivativeAlong I induced first second) field x -
          secondFundamental second intrinsicFirst x) -
        (normalDerivative second normalFirst x -
          secondFundamental (covariantDerivativeAlong I induced second first) field x -
          secondFundamental first intrinsicSecond x)
  have secondFundamental_sub :
      secondFundamental
          (covariantDerivativeAlong I induced first second -
            covariantDerivativeAlong I induced second first) field x =
        secondFundamental (covariantDerivativeAlong I induced first second) field x -
          secondFundamental (covariantDerivativeAlong I induced second first) field x := by
    simp [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  rw [secondFundamental_sub]
  abel

/-- Evaluate the constructed covariant derivative of `II` on the canonical linear extensions of
three tangent-fiber vectors and retain its proof of membership in the actual kernel-normal
fiber. -/
def projectedCovariantDerivativeSecondFundamentalValueAt
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (direction first second : TangentSpace I x) :
    SubmanifoldNormalSpaceAt immersion splitting x :=
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  ⟨extensions.covariantDerivativeSecondFundamentalAlong immersion splitting
      ambientConnection leftInverse directionField firstField secondField x,
    extensions.tangentProjection_covariantDerivativeSecondFundamentalAlong_eq_zero
      immersion splitting ambientConnection decomposition leftInverse
      directionField firstField secondField x⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
@[simp]
theorem projectedCovariantDerivativeSecondFundamentalValueAt_coe
    [IsManifold I 2 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (direction first second : TangentSpace I x) :
    ((projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
      ambientConnection extensions decomposition leftInverse x direction first second :
      SubmanifoldNormalSpaceAt immersion splitting x) :
      TangentSpace I' (immersion.toFun x)) =
        extensions.covariantDerivativeSecondFundamentalAlong immersion splitting
          ambientConnection leftInverse
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction)
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first)
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second) x :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Additivity of the pointwise `∇ᴮ II` value in its covariant-derivative direction follows
from connection regularity; no tensoriality equation is supplied as data. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_add_direction
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse) x)
    (direction direction' first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientConnection extensions decomposition leftInverse x (direction + direction')
        first second =
      projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
          ambientConnection extensions decomposition leftInverse x direction first second +
        projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
          ambientConnection extensions decomposition leftInverse x direction' first second := by
  let induced :=
    extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let directionField' :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction'
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientConnection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientConnection
  let normal := secondFundamental firstField secondField
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeFirst' := covariantDerivativeAlong I induced directionField' firstField
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  let derivativeSecond' := covariantDerivativeAlong I induced directionField' secondField
  have directionAdd :
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
          (direction + direction') = directionField + directionField' := by
    exact map_add _ _ _
  have derivativeFirstAdd :
      covariantDerivativeAlong I induced (directionField + directionField') firstField =
        derivativeFirst + derivativeFirst' := by
    funext y
    simp [covariantDerivativeAlong, derivativeFirst, derivativeFirst']
  have derivativeSecondAdd :
      covariantDerivativeAlong I induced (directionField + directionField') secondField =
        derivativeSecond + derivativeSecond' := by
    funext y
    simp [covariantDerivativeAlong, derivativeSecond, derivativeSecond']
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hdirection' : MDiffAt (T% directionField') x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction'
  have hsecond : CMDiffAt 2 (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular directionField secondField hdirection hsecond
  have hderivativeSecond' : MDiffAt (T% derivativeSecond') x :=
    intrinsicRegular directionField' secondField hdirection' hsecond
  have hderivativeSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecond))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecond
  have hderivativeSecondExtension' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecond'))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecond'
  have normalDerivativeAdd :
      normalDerivative (directionField + directionField') normal x =
        normalDerivative directionField normal x +
          normalDerivative directionField' normal x := by
    simp [normalDerivative, SubmanifoldFieldExtensionData.normalDerivative,
      SubmanifoldFieldExtensionData.ambientDerivativeAlong]
  have secondFundamentalAddFirst :
      secondFundamental (derivativeFirst + derivativeFirst') secondField x =
        secondFundamental derivativeFirst secondField x +
          secondFundamental derivativeFirst' secondField x := by
    simp [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  have secondFundamentalAddSecond :
      secondFundamental firstField (derivativeSecond + derivativeSecond') x =
        secondFundamental firstField derivativeSecond x +
          secondFundamental firstField derivativeSecond' x :=
    extensions.secondFundamentalFormAlong_add_second_at immersion splitting
      ambientConnection hderivativeSecondExtension hderivativeSecondExtension'
  apply Subtype.ext
  change
    normalDerivative
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
            (direction + direction')) normal x -
        secondFundamental
          (covariantDerivativeAlong I induced
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (direction + direction')) firstField) secondField x -
        secondFundamental firstField
          (covariantDerivativeAlong I induced
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (direction + direction')) secondField) x =
      (normalDerivative directionField normal x -
          secondFundamental derivativeFirst secondField x -
          secondFundamental firstField derivativeSecond x) +
        (normalDerivative directionField' normal x -
          secondFundamental derivativeFirst' secondField x -
          secondFundamental firstField derivativeSecond' x)
  rw [directionAdd, derivativeFirstAdd, derivativeSecondAdd, normalDerivativeAdd,
    secondFundamentalAddFirst, secondFundamentalAddSecond]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Constant real scalars pull through the covariant-derivative direction of the pointwise
`∇ᴮ II` value. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_smul_direction
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse) x)
    (scalar : ℝ) (direction first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientConnection extensions decomposition leftInverse x (scalar • direction)
        first second =
      scalar • projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientConnection extensions decomposition leftInverse x direction first second := by
  let induced :=
    extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientConnection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientConnection
  let normal := secondFundamental firstField secondField
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  have directionSmul :
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
          (scalar • direction) = scalar • directionField := by
    exact map_smul _ _ _
  have derivativeFirstSmul :
      covariantDerivativeAlong I induced (scalar • directionField) firstField =
        scalar • derivativeFirst := by
    funext y
    simp [covariantDerivativeAlong, derivativeFirst]
  have derivativeSecondSmul :
      covariantDerivativeAlong I induced (scalar • directionField) secondField =
        scalar • derivativeSecond := by
    funext y
    simp [covariantDerivativeAlong, derivativeSecond]
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hsecond : CMDiffAt 2 (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular directionField secondField hdirection hsecond
  have hderivativeSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecond))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecond
  have normalDerivativeSmul :
      normalDerivative (scalar • directionField) normal x =
        scalar • normalDerivative directionField normal x := by
    simp [normalDerivative, SubmanifoldFieldExtensionData.normalDerivative,
      SubmanifoldFieldExtensionData.ambientDerivativeAlong]
  have secondFundamentalSmulFirst :
      secondFundamental (scalar • derivativeFirst) secondField x =
        scalar • secondFundamental derivativeFirst secondField x := by
    simp [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  have secondFundamentalSmulSecond :
      secondFundamental firstField (scalar • derivativeSecond) x =
        scalar • secondFundamental firstField derivativeSecond x :=
    extensions.secondFundamentalFormAlong_smul_second_at immersion splitting
      ambientConnection scalar hderivativeSecondExtension
  apply Subtype.ext
  change
    normalDerivative
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
            (scalar • direction)) normal x -
        secondFundamental
          (covariantDerivativeAlong I induced
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (scalar • direction)) firstField) secondField x -
        secondFundamental firstField
          (covariantDerivativeAlong I induced
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (scalar • direction)) secondField) x =
      scalar • (normalDerivative directionField normal x -
        secondFundamental derivativeFirst secondField x -
        secondFundamental firstField derivativeSecond x)
  rw [directionSmul, derivativeFirstSmul, derivativeSecondSmul, normalDerivativeSmul,
    secondFundamentalSmulFirst, secondFundamentalSmulSecond]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Additivity of the pointwise `∇ᴮ II` value in its first second-fundamental-form slot. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_add_first
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientConnection x)
    (direction first first' second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientConnection extensions decomposition leftInverse x direction (first + first')
        second =
      projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
          ambientConnection extensions decomposition leftInverse x direction first second +
        projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
          ambientConnection extensions decomposition leftInverse x direction first' second := by
  let induced :=
    extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let firstField' :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first'
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientConnection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientConnection
  let normal := secondFundamental firstField secondField
  let normal' := secondFundamental firstField' secondField
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeFirst' := covariantDerivativeAlong I induced directionField firstField'
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  have firstAdd :
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
          (first + first') = firstField + firstField' := by
    exact map_add _ _ _
  have normalAdd :
      secondFundamental (firstField + firstField') secondField = normal + normal' := by
    funext y
    simp [secondFundamental, normal, normal',
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  have hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first second
  have hnormal' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal'))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first' second
  have normalDerivativeAdd :
      normalDerivative directionField (normal + normal') x =
        normalDerivative directionField normal x +
          normalDerivative directionField normal' x :=
    extensions.normalDerivative_add_normal_at immersion splitting ambientConnection
      hnormal hnormal'
  have hfirst : MDiffAt (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first
  have hfirst' : MDiffAt (T% firstField') x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first'
  have inducedAdd := DFunLike.congr_fun
    (induced.isCovariantDerivativeOn.add hfirst hfirst') (directionField x)
  have secondFundamentalDerivativeAdd :
      secondFundamental
          (covariantDerivativeAlong I induced directionField (firstField + firstField'))
          secondField x =
        secondFundamental derivativeFirst secondField x +
          secondFundamental derivativeFirst' secondField x := by
    change splitting.normalProjection x
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField)
          (immersion.toFun x)
          (mfderiv I I' immersion.toFun x
            (induced (firstField + firstField') x (directionField x)))) = _
    rw [inducedAdd]
    simp only [add_apply, map_add]
    rfl
  have secondFundamentalAddFirst :
      secondFundamental (firstField + firstField') derivativeSecond x =
        secondFundamental firstField derivativeSecond x +
          secondFundamental firstField' derivativeSecond x := by
    simp [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  apply Subtype.ext
  change
    normalDerivative directionField
          (secondFundamental
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (first + first')) secondField) x -
        secondFundamental
          (covariantDerivativeAlong I induced directionField
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (first + first'))) secondField x -
        secondFundamental
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
            (first + first')) derivativeSecond x =
      (normalDerivative directionField normal x -
          secondFundamental derivativeFirst secondField x -
          secondFundamental firstField derivativeSecond x) +
        (normalDerivative directionField normal' x -
          secondFundamental derivativeFirst' secondField x -
          secondFundamental firstField' derivativeSecond x)
  rw [firstAdd, normalAdd, normalDerivativeAdd, secondFundamentalDerivativeAdd,
    secondFundamentalAddFirst]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
  [CompleteSpace E'] [FiniteDimensional ℝ E']
  [RiemannianBundle (fun x : N ↦ TangentSpace I' x)] in
/-- Constant real scalars pull through the first second-fundamental-form slot of the pointwise
`∇ᴮ II` value. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_smul_first
    [IsManifold I 3 M] [IsManifold I' 2 N]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientConnection : CovariantDerivative I' E' (TangentSpace I' : N → Type _))
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientConnection x)
    (scalar : ℝ) (direction first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientConnection extensions decomposition leftInverse x direction (scalar • first)
        second =
      scalar • projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientConnection extensions decomposition leftInverse x direction first second := by
  let induced :=
    extensions.inducedCovariantDerivative immersion splitting ambientConnection leftInverse
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientConnection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientConnection
  let normal := secondFundamental firstField secondField
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  have firstSmul :
      SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
          (scalar • first) = scalar • firstField := by
    exact map_smul _ _ _
  have normalSmul :
      secondFundamental (scalar • firstField) secondField = scalar • normal := by
    funext y
    simp [secondFundamental, normal,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  have hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first second
  have normalDerivativeSmul :
      normalDerivative directionField (scalar • normal) x =
        scalar • normalDerivative directionField normal x :=
    extensions.normalDerivative_smul_normal_at immersion splitting ambientConnection
      scalar hnormal
  have hfirst : MDiffAt (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first
  have inducedSmul := DFunLike.congr_fun
    (induced.isCovariantDerivativeOn.smul_const scalar hfirst) (directionField x)
  have secondFundamentalDerivativeSmul :
      secondFundamental
          (covariantDerivativeAlong I induced directionField (scalar • firstField))
          secondField x =
        scalar • secondFundamental derivativeFirst secondField x := by
    change splitting.normalProjection x
        (ambientConnection
          (extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField)
          (immersion.toFun x)
          (mfderiv I I' immersion.toFun x
            (induced (scalar • firstField) x (directionField x)))) = _
    rw [inducedSmul]
    simp only [smul_apply, map_smul]
    rfl
  have secondFundamentalSmulFirst :
      secondFundamental (scalar • firstField) derivativeSecond x =
        scalar • secondFundamental firstField derivativeSecond x := by
    simp [secondFundamental,
      SubmanifoldFieldExtensionData.secondFundamentalFormAlong,
      SubmanifoldFieldExtensionData.ambientDerivativeTangent]
  apply Subtype.ext
  change
    normalDerivative directionField
          (secondFundamental
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (scalar • first)) secondField) x -
        secondFundamental
          (covariantDerivativeAlong I induced directionField
            (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
              (scalar • first))) secondField x -
        secondFundamental
          (SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x
            (scalar • first)) derivativeSecond x =
      scalar • (normalDerivative directionField normal x -
        secondFundamental derivativeFirst secondField x -
        secondFundamental firstField derivativeSecond x)
  rw [firstSmul, normalSmul, normalDerivativeSmul, secondFundamentalDerivativeSmul,
    secondFundamentalSmulFirst]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Additivity of the pointwise `∇ᴮ II` value in its second second-fundamental-form slot.

The canonical source extension is linear, but the chosen ambient extension operators are only
required to agree after restriction to the immersion.  The proof therefore establishes the
needed additive identities on a source neighborhood and transports those germs through the
ambient Levi--Civita connection. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_add_second
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion splitting
        ambientLeviCivita.connection leftInverse) x)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientLeviCivita.connection x)
    (direction first second second' : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientLeviCivita.connection extensions decomposition leftInverse x direction first
        (second + second') =
      projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
          ambientLeviCivita.connection extensions decomposition leftInverse x direction first
          second +
        projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
          ambientLeviCivita.connection extensions decomposition leftInverse x direction first
          second' := by
  let induced :=
    extensions.inducedCovariantDerivative immersion splitting
      ambientLeviCivita.connection leftInverse
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondField' :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second'
  let secondSumField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (second + second')
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientLeviCivita.connection
  let normalSum := secondFundamental firstField secondSumField
  let normal := secondFundamental firstField secondField
  let normal' := secondFundamental firstField secondField'
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeSecondSum :=
    covariantDerivativeAlong I induced directionField secondSumField
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  let derivativeSecond' := covariantDerivativeAlong I induced directionField secondField'
  have secondAdd : secondSumField = secondField + secondField' := by
    exact map_add _ _ _
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hsecond : CMDiffAt 2 (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second
  have hsecond' : CMDiffAt 2 (T% secondField') x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second'
  have hsecondSum : CMDiffAt 2 (T% secondSumField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (second + second')
  have hsecondNear : ∀ᶠ y in nhds x, MDiffAt (T% secondField) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hsecond.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondNear' : ∀ᶠ y in nhds x, MDiffAt (T% secondField') y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hsecond'.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have normalAgreement : normalSum =ᶠ[nhds x] normal + normal' := by
    filter_upwards [hsecondNear, hsecondNear'] with y hy hy'
    change secondFundamental firstField secondSumField y =
      secondFundamental firstField secondField y +
        secondFundamental firstField secondField' y
    rw [secondAdd]
    exact extensions.secondFundamentalFormAlong_add_second_at immersion splitting
      ambientLeviCivita.connection
      (extensions.tangentExtension_mdifferentiableAt hy)
      (extensions.tangentExtension_mdifferentiableAt hy')
  have hnormalSum : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normalSum))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first (second + second')
  have hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first second
  have hnormal' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal'))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first second'
  have normalDerivativeAdd :
      normalDerivative directionField normalSum x =
        normalDerivative directionField normal x +
          normalDerivative directionField normal' x :=
    extensions.normalDerivative_eq_add_of_eventuallyEq immersion splitting
      ambientLeviCivita hnormalSum hnormal hnormal' normalAgreement
  have hsecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt
      (hsecond.mdifferentiableAt (by norm_num))
  have hsecondExtension' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField'))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt
      (hsecond'.mdifferentiableAt (by norm_num))
  have secondFundamentalAddSecond :
      secondFundamental derivativeFirst secondSumField x =
        secondFundamental derivativeFirst secondField x +
          secondFundamental derivativeFirst secondField' x := by
    rw [secondAdd]
    exact extensions.secondFundamentalFormAlong_add_second_at immersion splitting
      ambientLeviCivita.connection hsecondExtension hsecondExtension'
  have hderivativeSecondSum : MDiffAt (T% derivativeSecondSum) x :=
    intrinsicRegular directionField secondSumField hdirection hsecondSum
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular directionField secondField hdirection hsecond
  have hderivativeSecond' : MDiffAt (T% derivativeSecond') x :=
    intrinsicRegular directionField secondField' hdirection hsecond'
  have derivativeAgreement :
      derivativeSecondSum =ᶠ[nhds x] derivativeSecond + derivativeSecond' := by
    filter_upwards [hsecondNear, hsecondNear'] with y hy hy'
    change induced secondSumField y (directionField y) =
      induced secondField y (directionField y) +
        induced secondField' y (directionField y)
    rw [secondAdd]
    exact DFunLike.congr_fun
      (induced.isCovariantDerivativeOn.add
        hy hy')
      (directionField y)
  have hderivativeSecondSumExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecondSum))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecondSum
  have hderivativeSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecond))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecond
  have hderivativeSecondExtension' : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecond'))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecond'
  have secondFundamentalDerivativeAdd :
      secondFundamental firstField derivativeSecondSum x =
        secondFundamental firstField derivativeSecond x +
          secondFundamental firstField derivativeSecond' x :=
    extensions.secondFundamentalFormAlong_eq_add_of_eventuallyEq immersion splitting
      ambientLeviCivita hderivativeSecondSumExtension hderivativeSecondExtension
      hderivativeSecondExtension' derivativeAgreement
  apply Subtype.ext
  change
    normalDerivative directionField normalSum x -
          secondFundamental derivativeFirst secondSumField x -
        secondFundamental firstField derivativeSecondSum x =
      (normalDerivative directionField normal x -
          secondFundamental derivativeFirst secondField x -
        secondFundamental firstField derivativeSecond x) +
      (normalDerivative directionField normal' x -
          secondFundamental derivativeFirst secondField' x -
        secondFundamental firstField derivativeSecond' x)
  rw [normalDerivativeAdd, secondFundamentalAddSecond, secondFundamentalDerivativeAdd]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- Constant real scalars pull through the second second-fundamental-form slot of the pointwise
`∇ᴮ II` value.  As in the additive theorem, restriction locality transports the scalar
identities through extension choices that need only agree along the immersion. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_smul_second
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion splitting
        ambientLeviCivita.connection leftInverse) x)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientLeviCivita.connection x)
    (scalar : ℝ) (direction first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientLeviCivita.connection extensions decomposition leftInverse x direction first
        (scalar • second) =
      scalar • projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientLeviCivita.connection extensions decomposition leftInverse x direction first
        second := by
  let induced :=
    extensions.inducedCovariantDerivative immersion splitting
      ambientLeviCivita.connection leftInverse
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondScaledField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x (scalar • second)
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion splitting ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion splitting ambientLeviCivita.connection
  let normalScaled := secondFundamental firstField secondScaledField
  let normal := secondFundamental firstField secondField
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeSecondScaled :=
    covariantDerivativeAlong I induced directionField secondScaledField
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  have secondSmul : secondScaledField = scalar • secondField := by
    exact map_smul _ _ _
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hsecond : CMDiffAt 2 (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second
  have hsecondScaled : CMDiffAt 2 (T% secondScaledField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x (scalar • second)
  have hsecondNear : ∀ᶠ y in nhds x, MDiffAt (T% secondField) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hsecond.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have normalAgreement : normalScaled =ᶠ[nhds x] scalar • normal := by
    filter_upwards [hsecondNear] with y hy
    change secondFundamental firstField secondScaledField y =
      scalar • secondFundamental firstField secondField y
    rw [secondSmul]
    exact extensions.secondFundamentalFormAlong_smul_second_at immersion splitting
      ambientLeviCivita.connection scalar
      (extensions.tangentExtension_mdifferentiableAt hy)
  have hnormalScaled : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normalScaled))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first (scalar • second)
  have hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first second
  have normalDerivativeSmul :
      normalDerivative directionField normalScaled x =
        scalar • normalDerivative directionField normal x :=
    extensions.normalDerivative_eq_smul_of_eventuallyEq immersion splitting
      ambientLeviCivita scalar hnormalScaled hnormal normalAgreement
  have hsecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt
      (hsecond.mdifferentiableAt (by norm_num))
  have secondFundamentalSmulSecond :
      secondFundamental derivativeFirst secondScaledField x =
        scalar • secondFundamental derivativeFirst secondField x := by
    rw [secondSmul]
    exact extensions.secondFundamentalFormAlong_smul_second_at immersion splitting
      ambientLeviCivita.connection scalar hsecondExtension
  have hderivativeSecondScaled : MDiffAt (T% derivativeSecondScaled) x :=
    intrinsicRegular directionField secondScaledField hdirection hsecondScaled
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular directionField secondField hdirection hsecond
  have derivativeAgreement :
      derivativeSecondScaled =ᶠ[nhds x] scalar • derivativeSecond := by
    filter_upwards [hsecondNear] with y hy
    change induced secondScaledField y (directionField y) =
      scalar • induced secondField y (directionField y)
    rw [secondSmul]
    exact DFunLike.congr_fun
      (induced.isCovariantDerivativeOn.smul_const scalar hy)
      (directionField y)
  have hderivativeSecondScaledExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension
        derivativeSecondScaled))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecondScaled
  have hderivativeSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.tangentExtension derivativeSecond))
      (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hderivativeSecond
  have secondFundamentalDerivativeSmul :
      secondFundamental firstField derivativeSecondScaled x =
        scalar • secondFundamental firstField derivativeSecond x :=
    extensions.secondFundamentalFormAlong_eq_smul_of_eventuallyEq immersion splitting
      ambientLeviCivita scalar hderivativeSecondScaledExtension
      hderivativeSecondExtension derivativeAgreement
  apply Subtype.ext
  change
    normalDerivative directionField normalScaled x -
          secondFundamental derivativeFirst secondScaledField x -
        secondFundamental firstField derivativeSecondScaled x =
      scalar • (normalDerivative directionField normal x -
        secondFundamental derivativeFirst secondField x -
        secondFundamental firstField derivativeSecond x)
  rw [normalDerivativeSmul, secondFundamentalSmulSecond,
    secondFundamentalDerivativeSmul]
  module

set_option synthInstance.maxHeartbeats 100000 in
/-- The geometrically constructed covariant derivative of the second fundamental form as an
actual continuous trilinear tensor on the source tangent fiber, valued in the kernel-normal
fiber.  All six linearity laws are consequences of the two connections and restriction
locality; no tensoriality equation is stored as input data. -/
def projectedCovariantDerivativeSecondFundamentalAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion splitting
        ambientLeviCivita.connection leftInverse) x)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientLeviCivita.connection x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] SubmanifoldNormalSpaceAt immersion splitting x :=
  LinearMap.toContinuousLinearMap {
    toFun := fun direction ↦ LinearMap.toContinuousLinearMap {
      toFun := fun first ↦ LinearMap.toContinuousLinearMap {
        toFun := fun second ↦
          projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
            ambientLeviCivita.connection extensions decomposition leftInverse x direction first
            second
        map_add' := fun second second' ↦
          projectedCovariantDerivativeSecondFundamentalValueAt_add_second immersion splitting
            ambientLeviCivita extensions decomposition leftInverse x intrinsicRegular
            extensionRegular direction first second second'
        map_smul' := fun scalar second ↦
          projectedCovariantDerivativeSecondFundamentalValueAt_smul_second immersion splitting
            ambientLeviCivita extensions decomposition leftInverse x intrinsicRegular
            extensionRegular scalar direction first second }
      map_add' := by
        intro first first'
        apply ContinuousLinearMap.ext
        intro second
        exact projectedCovariantDerivativeSecondFundamentalValueAt_add_first immersion splitting
          ambientLeviCivita.connection extensions decomposition leftInverse x extensionRegular
          direction first first' second
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        exact projectedCovariantDerivativeSecondFundamentalValueAt_smul_first immersion splitting
          ambientLeviCivita.connection extensions decomposition leftInverse x extensionRegular
          scalar direction first second }
    map_add' := by
      intro direction direction'
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact projectedCovariantDerivativeSecondFundamentalValueAt_add_direction immersion splitting
        ambientLeviCivita.connection extensions decomposition leftInverse x intrinsicRegular
        direction direction' first second
    map_smul' := by
      intro scalar direction
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact projectedCovariantDerivativeSecondFundamentalValueAt_smul_direction immersion splitting
        ambientLeviCivita.connection extensions decomposition leftInverse x intrinsicRegular
        scalar direction first second }

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp]
theorem projectedCovariantDerivativeSecondFundamentalAt_apply
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions : CovariantSubmanifoldFieldExtensionData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedCovariantDerivative immersion splitting
        ambientLeviCivita.connection leftInverse) x)
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion splitting ambientLeviCivita.connection x)
    (direction first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalAt immersion splitting ambientLeviCivita
        extensions decomposition leftInverse x intrinsicRegular extensionRegular
        direction first second =
      projectedCovariantDerivativeSecondFundamentalValueAt immersion splitting
        ambientLeviCivita.connection extensions decomposition leftInverse x
        direction first second :=
  rfl

omit [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] in
/-- The geometrically constructed pointwise `∇ᴮ II` is symmetric in its two `II` slots.
This is obtained by differentiating the field-level symmetry of `II`: ambient torsion-freeness
and bracket naturality prove that symmetry on a neighborhood, Levi--Civita restriction locality
transports it through the normal derivative, and the induced connection supplies the two
correction terms. -/
theorem projectedCovariantDerivativeSecondFundamentalValueAt_comm
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
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (direction first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalValueAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection extensions
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x direction first second =
      projectedCovariantDerivativeSecondFundamentalValueAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection extensions
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x direction second first := by
  let induced :=
    extensions.inducedLeviCivitaConnection immersion ambientLeviCivita |>.connection
  let directionField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x direction
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let secondFundamental :=
    extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normalDerivative :=
    extensions.toSubmanifoldFieldExtensionData.normalDerivative
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection
  let normal := secondFundamental firstField secondField
  let normalSwapped := secondFundamental secondField firstField
  let derivativeFirst := covariantDerivativeAlong I induced directionField firstField
  let derivativeSecond := covariantDerivativeAlong I induced directionField secondField
  have bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData :=
    extensions.hasBracketCompatibility immersion.toSmoothImmersionData
  have hdirection : MDiffAt (T% directionField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x direction
  have hfirst : CMDiffAt 2 (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x first
  have hsecond : CMDiffAt 2 (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x second
  have hfirstNear : ∀ᶠ y in nhds x, MDiffAt (T% firstField) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hfirst.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hsecondNear : ∀ᶠ y in nhds x, MDiffAt (T% secondField) y := by
    have hnear := (contMDiffAt_iff_contMDiffAt_nhds
      (n := (1 : ℕ∞ω)) (by norm_num)).mp (hsecond.of_le (by norm_num))
    exact hnear.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have normalAgreement : normal =ᶠ[nhds x] normalSwapped := by
    filter_upwards [hfirstNear, hsecondNear] with y hy hy'
    exact extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree bracketCompatibility hy hy'
  have hnormal : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normal))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first second
  have hnormalSwapped : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension normalSwapped))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt second first
  have normalDerivativeComm :
      normalDerivative directionField normal x =
        normalDerivative directionField normalSwapped x :=
    extensions.normalDerivative_eq_of_eventuallyEq immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita hnormal hnormalSwapped normalAgreement
  have hderivativeFirst : MDiffAt (T% derivativeFirst) x :=
    intrinsicRegular directionField firstField hdirection hfirst
  have hderivativeSecond : MDiffAt (T% derivativeSecond) x :=
    intrinsicRegular directionField secondField hdirection hsecond
  have correctionFirstComm :
      secondFundamental derivativeFirst secondField x =
        secondFundamental secondField derivativeFirst x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree bracketCompatibility hderivativeFirst
      (hsecond.mdifferentiableAt (by norm_num))
  have correctionSecondComm :
      secondFundamental firstField derivativeSecond x =
        secondFundamental derivativeSecond firstField x :=
    extensions.secondFundamentalFormAlong_comm immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
      ambientLeviCivita.torsionFree bracketCompatibility
      (hfirst.mdifferentiableAt (by norm_num)) hderivativeSecond
  apply Subtype.ext
  change
    normalDerivative directionField normal x -
          secondFundamental derivativeFirst secondField x -
        secondFundamental firstField derivativeSecond x =
      normalDerivative directionField normalSwapped x -
          secondFundamental derivativeSecond firstField x -
        secondFundamental secondField derivativeFirst x
  rw [normalDerivativeComm, correctionFirstComm, correctionSecondComm]
  abel

/-- Symmetry of the continuous trilinear `∇ᴮ II` tensor in its two final slots. -/
theorem projectedCovariantDerivativeSecondFundamentalAt_comm
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
    (extensionRegular : extensions.HasDifferentiatedGaussRegularityAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection x)
    (direction first second : TangentSpace I x) :
    projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita extensions
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x intrinsicRegular extensionRegular direction first second =
      projectedCovariantDerivativeSecondFundamentalAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita extensions
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x intrinsicRegular extensionRegular direction second first :=
  projectedCovariantDerivativeSecondFundamentalValueAt_comm immersion ambientLeviCivita
    extensions x intrinsicRegular extensionRegular direction first second

/-- Canonical linear extensions turn the field-level normal Gauss identity into a pointwise
Codazzi equation on actual tangent and kernel-normal fibers.  The normal ambient curvature and
both `∇ᴮ II` terms are therefore tied to the same geometric source. -/
theorem normalAmbientConnectionCurvatureAt_eq_projectedCovariantDerivativeSecondFundamental_sub
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
    (first second field : TangentSpace I x) :
    normalAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection
        immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
        x ambientRegular first second field =
      projectedCovariantDerivativeSecondFundamentalValueAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection extensions
          immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
          x first second field -
        projectedCovariantDerivativeSecondFundamentalValueAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection extensions
          immersion.hasTangentNormalDecomposition immersion.hasTangentProjectionLeftInverse
          x second first field := by
  let induced :=
    extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentProjectionLeftInverse
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let fieldField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field
  let eFirst :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension firstField
  let eSecond :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField
  let eField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldField
  have hfirst : MDiffAt (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first
  have hsecond : MDiffAt (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second
  have hfield : CMDiffAt 2 (T% fieldField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x field
  have hfieldExtension : CMDiffAt 2 (T% eField) (immersion.toFun x) := by
    exact extensionRegular.tangentExtension_contMDiffAt_two field
  have hnormalSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection secondField fieldField)))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt second field
  have hnormalFirstExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection firstField fieldField)))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first field
  have differentiated :=
    ambientCurvatureAction_normalProjection_eq_covariantDerivativeSecondFundamental_sub
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
      hfirst hsecond hfield hfieldExtension
      hnormalSecondExtension hnormalFirstExtension
  have hfirstExtension : MDiffAt (T% eFirst) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hfirst
  have hsecondExtension : MDiffAt (T% eSecond) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hsecond
  have ambientTensor :
      connectionCurvatureTensorAt I' ambientLeviCivita.connection (immersion.toFun x)
          ambientRegular
          (mfderiv I I' immersion.toFun x first)
          (mfderiv I I' immersion.toFun x second)
          (mfderiv I I' immersion.toFun x field) =
        connectionCurvatureAction I' ambientLeviCivita.connection
          eFirst eSecond eField (immersion.toFun x) := by
    simpa only [eFirst, eSecond, eField,
      extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees,
      firstField, secondField, fieldField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self] using
      (connectionCurvatureTensorAt_apply I' ambientLeviCivita.connection
        (immersion.toFun x) ambientRegular hfirstExtension hsecondExtension hfieldExtension)
  apply Subtype.ext
  rw [normalAmbientConnectionCurvatureAt_coe]
  change immersion.orthogonalSplitting.normalProjection x
      (connectionCurvatureTensorAt I' ambientLeviCivita.connection (immersion.toFun x)
        ambientRegular
        (mfderiv I I' immersion.toFun x first)
        (mfderiv I I' immersion.toFun x second)
        (mfderiv I I' immersion.toFun x field)) = _
  rw [ambientTensor]
  exact differentiated

/-! ## A single-source induced Gauss package -/

/-- Actual-fiber Gauss data whose intrinsic curvature and second fundamental form are constructed
from the same isometric immersion, ambient Levi--Civita connection, and covariant extension
operator.  The source connection is the induced Levi--Civita connection proved in
`SubmanifoldInducedConnection`; neither the intrinsic connection nor `II` is independently
supplied. -/
def inducedLeviCivitaSubmanifoldPointwiseGaussDataOfBracketCompatibilityAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnectionOfBracketCompatibility
        immersion ambientLeviCivita
        bracketCompatibility).connection x) :
    SubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
  connectionSubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
    immersion.orthogonalSplitting
    (extensions.inducedLeviCivitaConnectionOfBracketCompatibility
      immersion ambientLeviCivita
      bracketCompatibility).connection x intrinsicRegular
    (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x)

/-- Actual-fiber Gauss data for a boundaryless isometric immersion, constructed without a
caller-supplied bracket hypothesis. -/
def inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
    [IsManifold I 3 M] [IsManifold I' 2 N]
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
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x) :
    SubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
  inducedLeviCivitaSubmanifoldPointwiseGaussDataOfBracketCompatibilityAt
    immersion ambientLeviCivita extensions
    (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
    x intrinsicRegular

/-- The canonical boundaryless pointwise package satisfies the vector Gauss equation relative to
the tangential projection of the ambient connection-curvature tensor.  Every geometric term is
constructed from the same immersion, ambient Levi--Civita connection, and extension operator.
The sole additional input is `HasDifferentiatedGaussRegularityAt`, whose fields assert only the
regularity needed to differentiate those constructed terms. -/
theorem inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasVectorGaussEquationRelativeTo
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
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
      ambientLeviCivita.connection x) :
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
      immersion ambientLeviCivita extensions x intrinsicRegular).HasVectorGaussEquationRelativeTo
        (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection x ambientRegular) := by
  intro first second field
  let induced :=
    extensions.inducedCovariantDerivative immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection
      immersion.hasTangentProjectionLeftInverse
  let firstField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x first
  let secondField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x second
  let fieldField :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt (I := I) x field
  let eFirst :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension firstField
  let eSecond :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension secondField
  let eField :=
    extensions.toSubmanifoldFieldExtensionData.tangentExtension fieldField
  let pointII :=
    CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x
  have hfirst : MDiffAt (T% firstField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x first
  have hsecond : MDiffAt (T% secondField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_mdifferentiableAt
      (I := I) x second
  have hfield : CMDiffAt 2 (T% fieldField) x :=
    SubmanifoldFieldExtensionData.linearFiberExtensionAt_contMDiffAt_two
      (I := I) x field
  have hfieldExtension : CMDiffAt 2 (T% eField) (immersion.toFun x) := by
    exact extensionRegular.tangentExtension_contMDiffAt_two field
  have hnormalSecondExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection secondField fieldField)))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt second field
  have hnormalFirstExtension : MDiffAt
      (T% (extensions.toSubmanifoldFieldExtensionData.alongExtension
        (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection firstField fieldField)))
      (immersion.toFun x) := by
    exact extensionRegular.normalGaussExtension_mdifferentiableAt first field
  have differentiated :=
    inducedCurvatureAction_eq_tangentialAmbient_add_shape
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular
      hfirst hsecond hfield hfieldExtension
      hnormalSecondExtension hnormalFirstExtension
  have intrinsicTensor :
      connectionCurvatureTensorAt I induced x intrinsicRegular first second field =
        connectionCurvatureAction I induced firstField secondField fieldField x := by
    simpa [firstField, secondField, fieldField] using
      (connectionCurvatureTensorAt_apply I induced x intrinsicRegular
        hfirst hsecond hfield)
  have hfirstExtension : MDiffAt (T% eFirst) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hfirst
  have hsecondExtension : MDiffAt (T% eSecond) (immersion.toFun x) :=
    extensions.tangentExtension_mdifferentiableAt hsecond
  have ambientTensor :
      connectionCurvatureTensorAt I' ambientLeviCivita.connection (immersion.toFun x)
          ambientRegular
          (mfderiv I I' immersion.toFun x first)
          (mfderiv I I' immersion.toFun x second)
          (mfderiv I I' immersion.toFun x field) =
        connectionCurvatureAction I' ambientLeviCivita.connection
          eFirst eSecond eField (immersion.toFun x) := by
    simpa only [eFirst, eSecond, eField,
      extensions.toSubmanifoldFieldExtensionData.tangentExtension_agrees,
      firstField, secondField, fieldField,
      SubmanifoldFieldExtensionData.linearFiberExtensionAt_apply_self] using
      (connectionCurvatureTensorAt_apply I' ambientLeviCivita.connection
        (immersion.toFun x) ambientRegular hfirstExtension hsecondExtension hfieldExtension)
  have shapeSecond :
      shapeOperatorOfSecondFundamental pointII (pointII second field) first =
        extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection firstField
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection secondField fieldField) x := by
    exact shapeOperatorOfProjectedSecondFundamentalAt_eq_shapeOperatorAlong
      immersion ambientLeviCivita extensions x first second field hnormalSecondExtension
  have shapeFirst :
      shapeOperatorOfSecondFundamental pointII (pointII first field) second =
        extensions.toSubmanifoldFieldExtensionData.shapeOperatorAlong
          immersion.toSmoothImmersionData immersion.orthogonalSplitting
          ambientLeviCivita.connection secondField
          (extensions.toSubmanifoldFieldExtensionData.secondFundamentalFormAlong
            immersion.toSmoothImmersionData immersion.orthogonalSplitting
            ambientLeviCivita.connection firstField fieldField) x := by
    exact shapeOperatorOfProjectedSecondFundamentalAt_eq_shapeOperatorAlong
      immersion ambientLeviCivita extensions x second first field hnormalFirstExtension
  change connectionCurvatureTensorAt I induced x intrinsicRegular first second field =
    tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
        immersion.orthogonalSplitting ambientLeviCivita.connection x ambientRegular
        first second field +
      shapeOperatorOfSecondFundamental pointII (pointII second field) first -
      shapeOperatorOfSecondFundamental pointII (pointII first field) second
  rw [intrinsicTensor, tangentialAmbientConnectionCurvatureAt_apply, ambientTensor,
    shapeSecond, shapeFirst]
  exact differentiated

/-- The scalar Gauss equation for the same canonical package follows by pairing the proved vector
identity with a fourth tangent vector.  It is therefore no longer an independent hypothesis in
the submanifold-to-Ricci contraction pipeline. -/
theorem inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasGaussEquationRelativeTo
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
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
      ambientLeviCivita.connection x) :
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
      immersion ambientLeviCivita extensions x intrinsicRegular).HasGaussEquationRelativeTo
        (tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
          immersion.orthogonalSplitting ambientLeviCivita.connection x ambientRegular) :=
  PointwiseGaussData.hasGaussEquationRelativeTo_of_vector _ _
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasVectorGaussEquationRelativeTo
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular)

/-- For a flat ambient curvature tensor, the canonical immersion package satisfies the Euclidean
scalar Gauss equation used in CCG25 Theorem 1.9. -/
theorem inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasEuclideanGaussEquation
    [IsManifold I 3 M] [IsManifold I' 3 N]
    [I.Boundaryless] [I'.Boundaryless]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
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
    (ambientFlat : tangentialAmbientConnectionCurvatureAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting ambientLeviCivita.connection x ambientRegular = 0) :
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
      immersion ambientLeviCivita extensions x intrinsicRegular).HasEuclideanGaussEquation :=
  PointwiseGaussData.hasEuclideanGaussEquation_of_relative_eq_zero _ _
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_hasGaussEquationRelativeTo
      immersion ambientLeviCivita extensions x intrinsicRegular ambientRegular extensionRegular)
    ambientFlat

/-- The single-source Gauss package has a symmetric second fundamental form.  Canonical extension
regularity and normal-bracket tangency are both discharged by the covariant extension layer. -/
theorem inducedLeviCivitaSubmanifoldPointwiseGaussDataOfBracketCompatibilityAt_isSymmetric
    [IsManifold I 3 M] [IsManifold I' 2 N]
    [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun y : N ↦ TangentSpace I' y)]
    [∀ y : M, CompleteSpace (TangentSpace I y)]
    [∀ y : N, CompleteSpace (TangentSpace I' y)]
    (immersion : SmoothIsometricImmersionData
      (I := I) (I' := I') (M := M) (N := N))
    (ambientLeviCivita : LeviCivitaConnection (M := N) I')
    (extensions :
      CovariantSubmanifoldFieldExtensionData immersion.toSmoothImmersionData)
    (bracketCompatibility :
      extensions.HasBracketCompatibility immersion.toSmoothImmersionData)
    (x : M)
    (intrinsicRegular : HasConnectionCurvatureRegularityAt I
      (extensions.inducedLeviCivitaConnectionOfBracketCompatibility
        immersion ambientLeviCivita
        bracketCompatibility).connection x) :
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataOfBracketCompatibilityAt
      immersion ambientLeviCivita
      extensions bracketCompatibility x intrinsicRegular).IsSymmetric := by
  intro first second
  exact CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_comm
    immersion.toSmoothImmersionData immersion.orthogonalSplitting
    ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
    immersion.hasTangentProjectionLeftInverse ambientLeviCivita.torsionFree
    bracketCompatibility x first second

/-- The canonical boundaryless Gauss package has symmetric second fundamental form; all bracket
compatibility obligations are discharged internally. -/
theorem inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_isSymmetric
    [IsManifold I 3 M] [IsManifold I' 2 N]
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
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita).connection x) :
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
      immersion ambientLeviCivita extensions x intrinsicRegular).IsSymmetric := by
  exact inducedLeviCivitaSubmanifoldPointwiseGaussDataOfBracketCompatibilityAt_isSymmetric
    immersion ambientLeviCivita extensions
    (extensions.hasBracketCompatibility immersion.toSmoothImmersionData)
    x intrinsicRegular

end ManifoldFibers

end

end RiemannianFluids
