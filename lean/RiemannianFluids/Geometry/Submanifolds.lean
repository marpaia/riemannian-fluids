import Mathlib.Geometry.Manifold.Riemannian.Basic
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

end

end RiemannianFluids
