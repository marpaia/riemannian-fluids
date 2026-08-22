import RiemannianFluids.Geometry.Submanifolds
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

end ManifoldFibers

end

end RiemannianFluids
