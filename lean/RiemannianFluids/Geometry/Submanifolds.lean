import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import RiemannianFluids.Geometry.Manifolds

/-!
# Embedded-submanifold geometry above Mathlib

Mathlib supplies the manifold, tangent-bundle, derivative, continuous-linear-map, and
fiberwise inner-product layers used here.  It does not currently supply a general embedded
Riemannian-submanifold API.  This file therefore records that missing layer without replacing
Mathlib's foundations by unrelated carrier types.

The normal bundle is represented as the kernel of the tangential projection inside the pulled
back ambient tangent bundle.  This keeps arbitrary codimension visible: no preferred unit normal
is introduced until a paper explicitly assumes a hypersurface.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

/-- A smooth immersion, expressed using Mathlib's manifold derivative. -/
structure SmoothImmersionData where
  toFun : M → N
  contMDiff : ContMDiff I I' ∞ toFun
  mfderiv_injective : ∀ x, Function.Injective (mfderiv I I' toFun x)

/-- A smooth embedding is an injective smooth immersion.  Topological properness or closed-image
hypotheses belong to the individual source statement when they are used. -/
structure SmoothEmbeddingData extends SmoothImmersionData (I := I) (I' := I') (M := M) (N := N) where
  injective : Function.Injective toFun

/-- A smooth map whose differential preserves the Riemannian inner product at every point.
Injectivity of the differential is a theorem, so it is not duplicated as structure data. -/
structure SmoothIsometricImmersionData
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [RiemannianBundle (fun x : N => TangentSpace I' x)] where
  toFun : M → N
  contMDiff : ContMDiff I I' ∞ toFun
  mfderiv_inner : ∀ x first second,
    inner ℝ (mfderiv I I' toFun x first) (mfderiv I I' toFun x second) =
      inner ℝ first second

namespace SmoothIsometricImmersionData

variable
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace I' x)]

/-- Forget metric preservation.  The immersion condition follows from preservation of the inner
product, rather than being supplied separately. -/
abbrev toSmoothImmersionData
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    SmoothImmersionData (I := I) (I' := I') (M := M) (N := N) where
  toFun := immersion.toFun
  contMDiff := immersion.contMDiff
  mfderiv_injective := by
    intro x first second equal
    apply ext_inner_right ℝ
    intro test
    rw [← immersion.mfderiv_inner x first test, equal,
      immersion.mfderiv_inner x second test]

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
@[simp]
theorem toSmoothImmersionData_toFun
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    immersion.toSmoothImmersionData.toFun = immersion.toFun :=
  rfl

end SmoothIsometricImmersionData

/-- A section of the ambient tangent bundle pulled back along an immersion. -/
abbrev AmbientVectorFieldAlong
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) :=
  (x : M) → TangentSpace I' (immersion.toFun x)

/-- Tangential and normal projections of the pulled-back ambient tangent bundle. -/
structure SubmanifoldSplittingData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) where
  tangentProjection :
    ∀ x, TangentSpace I' (immersion.toFun x) →L[ℝ] TangentSpace I x
  normalProjection :
    ∀ x, TangentSpace I' (immersion.toFun x) →L[ℝ] TangentSpace I' (immersion.toFun x)

/-- The ambient tangent vector is the sum of its immersed tangential and normal parts. -/
def HasTangentNormalDecomposition
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) : Prop :=
  ∀ x v,
    mfderiv I I' immersion.toFun x (splitting.tangentProjection x v) +
        splitting.normalProjection x v =
      v

/-- Tangential projection is a left inverse to the differential of the immersion. -/
def HasTangentProjectionLeftInverse
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) : Prop :=
  ∀ x v,
    splitting.tangentProjection x (mfderiv I I' immersion.toFun x v) = v

/-- The range of the normal projection is orthogonal to the immersed tangent space. -/
def HasOrthogonalNormalProjection
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) : Prop :=
  ∀ x ambient tangent,
    inner ℝ (splitting.normalProjection x ambient)
        (mfderiv I I' immersion.toFun x tangent) = 0

/-- A Mathlib-backed orthogonal splitting of the pulled-back ambient tangent bundle. -/
def IsOrthogonalSubmanifoldSplitting
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion) : Prop :=
  HasTangentNormalDecomposition immersion splitting ∧
    HasTangentProjectionLeftInverse immersion splitting ∧
      HasOrthogonalNormalProjection immersion splitting

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- Any genuine tangent/normal decomposition sends immersed tangent vectors to zero under the
normal projection. -/
theorem normalProjection_mfderiv_eq_zero
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (tangent : TangentSpace I x) :
    splitting.normalProjection x (mfderiv I I' immersion.toFun x tangent) = 0 := by
  have reconstructed :=
    decomposition x (mfderiv I I' immersion.toFun x tangent)
  rw [leftInverse x tangent] at reconstructed
  exact (add_eq_left.mp reconstructed)

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- In any genuine tangent/normal decomposition, the normal output lies in the kernel of the
tangential projection. -/
theorem tangentProjection_normalProjection_eq_zero
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (decomposition : HasTangentNormalDecomposition immersion splitting)
    (leftInverse : HasTangentProjectionLeftInverse immersion splitting)
    (x : M) (ambient : TangentSpace I' (immersion.toFun x)) :
    splitting.tangentProjection x (splitting.normalProjection x ambient) = 0 := by
  have reconstructed := decomposition x ambient
  have projected := congrArg (splitting.tangentProjection x) reconstructed
  simpa only [map_add, leftInverse x, add_eq_left] using projected

/-- Second fundamental form, shape operators, and mean-curvature vector.  All values live in
actual tangent fibers.  Normal-valuedness, symmetry, and the adjoint relation are separate
inspectable propositions below instead of opaque `Prop` fields. -/
structure SecondFundamentalFormData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) where
  secondFundamentalForm :
    ∀ x, TangentSpace I x → TangentSpace I x → TangentSpace I' (immersion.toFun x)
  shapeOperator :
    ∀ x, TangentSpace I' (immersion.toFun x) → TangentSpace I x → TangentSpace I x
  meanCurvatureVector : ∀ x, TangentSpace I' (immersion.toFun x)

/-- The second fundamental form and mean curvature take values in the normal summand. -/
def IsNormalValuedSecondFundamentalForm
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (geometry : SecondFundamentalFormData immersion) : Prop :=
  (∀ x first second,
      splitting.tangentProjection x (geometry.secondFundamentalForm x first second) = 0) ∧
    ∀ x, splitting.tangentProjection x (geometry.meanCurvatureVector x) = 0

/-- Symmetry of the second fundamental form. -/
def IsSymmetricSecondFundamentalForm
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : SecondFundamentalFormData immersion) : Prop :=
  ∀ x first second,
    geometry.secondFundamentalForm x first second =
      geometry.secondFundamentalForm x second first

/-- The shape operator is fiberwise adjoint to the second fundamental form. -/
def HasShapeSecondFundamentalAdjoint
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : SecondFundamentalFormData immersion) : Prop :=
  ∀ x normal first second,
    inner ℝ (geometry.shapeOperator x normal first) second =
      inner ℝ (geometry.secondFundamentalForm x first second) normal

/-- The intrinsic, normal, and ambient derivatives appearing in Gauss--Weingarten formulas.
Regularity and connection axioms are explicit source hypotheses rather than bundled here. -/
structure SubmanifoldConnectionData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) where
  intrinsicDerivative :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x)
  normalDerivative :
    ((x : M) → TangentSpace I x) → AmbientVectorFieldAlong immersion →
      AmbientVectorFieldAlong immersion
  ambientDerivativeTT :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      AmbientVectorFieldAlong immersion
  ambientDerivativeTN :
    ((x : M) → TangentSpace I x) → AmbientVectorFieldAlong immersion →
      AmbientVectorFieldAlong immersion

/-- Gauss' formula splits the ambient derivative of tangent fields into intrinsic and normal
parts. -/
def HasGaussFormula
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (connection : SubmanifoldConnectionData immersion)
    (geometry : SecondFundamentalFormData immersion) : Prop :=
  ∀ first second x,
    connection.ambientDerivativeTT first second x =
      mfderiv I I' immersion.toFun x (connection.intrinsicDerivative first second x) +
        geometry.secondFundamentalForm x (first x) (second x)

/-- Weingarten's formula splits the derivative of a normal field into the shape term and normal
connection term. -/
def HasWeingartenFormula
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (connection : SubmanifoldConnectionData immersion)
    (geometry : SecondFundamentalFormData immersion) : Prop :=
  ∀ tangent normal x,
    connection.ambientDerivativeTN tangent normal x =
      -(mfderiv I I' immersion.toFun x (geometry.shapeOperator x (normal x) (tangent x))) +
        connection.normalDerivative tangent normal x

/-- The three normal-valued terms in the contracted Codazzi identity. -/
structure RiemannianContractedCodazziData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) where
  traceDerivativeSecondFundamental :
    ((x : M) → TangentSpace I x) → AmbientVectorFieldAlong immersion
  meanCurvatureNormalDerivative :
    ((x : M) → TangentSpace I x) → AmbientVectorFieldAlong immersion
  ambientCurvatureNormalTrace :
    ((x : M) → TangentSpace I x) → AmbientVectorFieldAlong immersion

/-- Contracted Codazzi in the sign convention used by CCG25. -/
def HasContractedCodazziIdentity
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (data : RiemannianContractedCodazziData immersion) : Prop :=
  ∀ tangent x,
    data.traceDerivativeSecondFundamental tangent x =
      data.meanCurvatureNormalDerivative tangent x +
        data.ambientCurvatureNormalTrace tangent x

/-- Carrier-polymorphic contracted-Codazzi terms used by papers that state the identity before
choosing a concrete manifold realization.  The mathematical content is still the displayed
equality; no `hasCodazzi : Prop` placeholder is stored. -/
structure ContractedCodazziData (TangentVector NormalVector : Type*) where
  traceDerivativeSecondFundamental : TangentVector → NormalVector
  meanCurvatureNormalDerivative : TangentVector → NormalVector
  ambientCurvatureNormalTrace : TangentVector → NormalVector

/-- Carrier-polymorphic contracted Codazzi identity. -/
def HasAbstractContractedCodazziIdentity
    {TangentVector NormalVector : Type*} [AddCommGroup NormalVector]
    (data : ContractedCodazziData TangentVector NormalVector) : Prop :=
  ∀ tangent,
    data.traceDerivativeSecondFundamental tangent =
      data.meanCurvatureNormalDerivative tangent +
        data.ambientCurvatureNormalTrace tangent

/-! ## Canonical orthogonal splitting of an isometric immersion -/

section IsometricSplitting

variable
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace I' x)]
  [∀ x : M, CompleteSpace (TangentSpace I x)]
  [∀ x : N, CompleteSpace (TangentSpace I' x)]

/-- The canonical splitting induced by an isometric immersion.  Tangential projection is the
adjoint of `df`; normal projection is `id - df (df)†`. -/
def SmoothIsometricImmersionData.orthogonalSplitting
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    SubmanifoldSplittingData immersion.toSmoothImmersionData where
  tangentProjection := fun x => (mfderiv I I' immersion.toFun x).adjoint
  normalProjection := fun x =>
    ContinuousLinearMap.id ℝ (TangentSpace I' (immersion.toFun x)) -
      (mfderiv I I' immersion.toFun x).comp
        (mfderiv I I' immersion.toFun x).adjoint

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- For an isometric immersion, `(df)† df = id`. -/
theorem SmoothIsometricImmersionData.adjoint_mfderiv_comp_mfderiv
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M) :
    (mfderiv I I' immersion.toFun x).adjoint.comp
        (mfderiv I I' immersion.toFun x) = 1 :=
  (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self
    (mfderiv I I' immersion.toFun x)).mp (immersion.mfderiv_inner x)

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- The canonical projections reconstruct every ambient tangent vector. -/
theorem SmoothIsometricImmersionData.hasTangentNormalDecomposition
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    HasTangentNormalDecomposition immersion.toSmoothImmersionData
      immersion.orthogonalSplitting := by
  intro x ambient
  simp only [SmoothIsometricImmersionData.orthogonalSplitting, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  abel

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- The adjoint tangential projection is a left inverse of `df`. -/
theorem SmoothIsometricImmersionData.hasTangentProjectionLeftInverse
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    HasTangentProjectionLeftInverse immersion.toSmoothImmersionData
      immersion.orthogonalSplitting := by
  intro x tangent
  change (mfderiv I I' immersion.toFun x).adjoint
    (mfderiv I I' immersion.toFun x tangent) = tangent
  have evaluated := congrArg
    (fun map : TangentSpace I x →L[ℝ] TangentSpace I x => map tangent)
    (immersion.adjoint_mfderiv_comp_mfderiv x)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply] using evaluated

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- The range of the canonical normal projection is orthogonal to the immersed tangent space. -/
theorem SmoothIsometricImmersionData.hasOrthogonalNormalProjection
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    HasOrthogonalNormalProjection immersion.toSmoothImmersionData
      immersion.orthogonalSplitting := by
  intro x ambient tangent
  change inner ℝ
      (ambient - mfderiv I I' immersion.toFun x
        ((mfderiv I I' immersion.toFun x).adjoint ambient))
      (mfderiv I I' immersion.toFun x tangent) = 0
  rw [inner_sub_left, immersion.mfderiv_inner,
    ContinuousLinearMap.adjoint_inner_left]
  ring

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- An isometric immersion therefore carries a canonical Mathlib-backed orthogonal
tangent/normal splitting. -/
theorem SmoothIsometricImmersionData.isOrthogonalSubmanifoldSplitting
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N)) :
    IsOrthogonalSubmanifoldSplitting immersion.toSmoothImmersionData
      immersion.orthogonalSplitting :=
  ⟨immersion.hasTangentNormalDecomposition,
    immersion.hasTangentProjectionLeftInverse,
    immersion.hasOrthogonalNormalProjection⟩

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- Membership in the canonical normal fiber is exactly orthogonality to every immersed tangent
vector. -/
theorem SmoothIsometricImmersionData.mem_normalSpace_iff
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M) (ambient : TangentSpace I' (immersion.toFun x)) :
    ambient ∈ LinearMap.ker
        ((immersion.orthogonalSplitting.tangentProjection x).toLinearMap) ↔
      ∀ tangent : TangentSpace I x,
        inner ℝ ambient (mfderiv I I' immersion.toFun x tangent) = 0 := by
  change (mfderiv I I' immersion.toFun x).adjoint ambient = 0 ↔ _
  constructor
  · intro normal tangent
    rw [← ContinuousLinearMap.adjoint_inner_left, normal, inner_zero_left]
  · intro orthogonal
    apply ext_inner_right ℝ
    intro tangent
    rw [ContinuousLinearMap.adjoint_inner_left, orthogonal tangent, inner_zero_left]

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- The canonical normal projection kills every vector in the immersed tangent range. -/
theorem SmoothIsometricImmersionData.normalProjection_mfderiv
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M) (tangent : TangentSpace I x) :
    immersion.orthogonalSplitting.normalProjection x
        (mfderiv I I' immersion.toFun x tangent) = 0 := by
  change mfderiv I I' immersion.toFun x tangent -
      mfderiv I I' immersion.toFun x
        ((mfderiv I I' immersion.toFun x).adjoint
          (mfderiv I I' immersion.toFun x tangent)) = 0
  have leftInverse :
      (mfderiv I I' immersion.toFun x).adjoint
          (mfderiv I I' immersion.toFun x tangent) = tangent := by
    have evaluated := congrArg
      (fun map : TangentSpace I x →L[ℝ] TangentSpace I x => map tangent)
      (immersion.adjoint_mfderiv_comp_mfderiv x)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply] using evaluated
  rw [leftInverse]
  exact sub_self _

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- Tangential projection kills the output of the canonical normal projection. -/
theorem SmoothIsometricImmersionData.tangentProjection_normalProjection
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M) (ambient : TangentSpace I' (immersion.toFun x)) :
    immersion.orthogonalSplitting.tangentProjection x
        (immersion.orthogonalSplitting.normalProjection x ambient) = 0 := by
  change (mfderiv I I' immersion.toFun x).adjoint
      (ambient - mfderiv I I' immersion.toFun x
        ((mfderiv I I' immersion.toFun x).adjoint ambient)) = 0
  have leftInverse :
      (mfderiv I I' immersion.toFun x).adjoint
          (mfderiv I I' immersion.toFun x
            ((mfderiv I I' immersion.toFun x).adjoint ambient)) =
        (mfderiv I I' immersion.toFun x).adjoint ambient := by
    have evaluated := congrArg
      (fun map : TangentSpace I x →L[ℝ] TangentSpace I x =>
        map ((mfderiv I I' immersion.toFun x).adjoint ambient))
      (immersion.adjoint_mfderiv_comp_mfderiv x)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply] using evaluated
  rw [map_sub, leftInverse]
  exact sub_self _

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- The canonical normal projection is idempotent. -/
theorem SmoothIsometricImmersionData.normalProjection_idempotent
    (immersion : SmoothIsometricImmersionData (I := I) (I' := I') (M := M) (N := N))
    (x : M) (ambient : TangentSpace I' (immersion.toFun x)) :
    immersion.orthogonalSplitting.normalProjection x
        (immersion.orthogonalSplitting.normalProjection x ambient) =
      immersion.orthogonalSplitting.normalProjection x ambient := by
  change immersion.orthogonalSplitting.normalProjection x ambient -
      mfderiv I I' immersion.toFun x
        (immersion.orthogonalSplitting.tangentProjection x
          (immersion.orthogonalSplitting.normalProjection x ambient)) =
    immersion.orthogonalSplitting.normalProjection x ambient
  rw [immersion.tangentProjection_normalProjection, map_zero, sub_zero]

end IsometricSplitting

end

end RiemannianFluids
