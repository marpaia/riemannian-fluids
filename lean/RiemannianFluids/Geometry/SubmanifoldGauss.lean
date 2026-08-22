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

/-! ## A single-source induced Gauss package -/

/-- Actual-fiber Gauss data whose intrinsic curvature and second fundamental form are constructed
from the same isometric immersion, ambient Levi--Civita connection, and covariant extension
operator.  The source connection is the induced Levi--Civita connection proved in
`SubmanifoldInducedConnection`; neither the intrinsic connection nor `II` is independently
supplied. -/
def inducedLeviCivitaSubmanifoldPointwiseGaussDataAt
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
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita
        bracketCompatibility).connection x) :
    SubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
      immersion.orthogonalSplitting x :=
  connectionSubmanifoldPointwiseGaussDataAt immersion.toSmoothImmersionData
    immersion.orthogonalSplitting
    (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita
      bracketCompatibility).connection x intrinsicRegular
    (CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt
      immersion.toSmoothImmersionData immersion.orthogonalSplitting
      ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
      immersion.hasTangentProjectionLeftInverse x)

/-- The single-source Gauss package has a symmetric second fundamental form.  Canonical extension
regularity and normal-bracket tangency are both discharged by the covariant extension layer. -/
theorem inducedLeviCivitaSubmanifoldPointwiseGaussDataAt_isSymmetric
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
      (extensions.inducedLeviCivitaConnection immersion ambientLeviCivita
        bracketCompatibility).connection x) :
    (inducedLeviCivitaSubmanifoldPointwiseGaussDataAt immersion ambientLeviCivita
      extensions bracketCompatibility x intrinsicRegular).IsSymmetric := by
  intro first second
  exact CovariantSubmanifoldFieldExtensionData.projectedSecondFundamentalFormAt_comm
    immersion.toSmoothImmersionData immersion.orthogonalSplitting
    ambientLeviCivita.connection extensions immersion.hasTangentNormalDecomposition
    immersion.hasTangentProjectionLeftInverse ambientLeviCivita.torsionFree
    bracketCompatibility x first second

end ManifoldFibers

end

end RiemannianFluids
