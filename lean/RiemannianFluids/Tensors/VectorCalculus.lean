import RiemannianFluids.Geometry.Connections
import RiemannianFluids.Geometry.Musical
import RiemannianFluids.Tensors.Contraction
import RiemannianFluids.Tensors.Symmetry

/-!
# First-order calculus of vector fields

This module constructs intrinsic divergence from a chosen smooth
Levi-Civita connection.  Its regularity contract is explicit:
`C^(k+1)(TM) → C^k(M, ℝ)`.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/--
Intrinsic divergence, defined as the fiberwise trace of the covariant
derivative.
-/
noncomputable def divergence
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothScalarField (M := M) I regularity :=
  (traceVectorOneForm I regularity).comp
    (LeviCivitaConnection.covariantDerivative I connection regularity smooth)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem divergence_apply
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) (x : M) :
    divergence I connection regularity smooth field x =
      tangentTrace I x (connection.connection field x) :=
  rfl

/--
The covariant derivative with its tangent-valued output lowered by the metric.
This is the unsymmetrized covariant two-tensor underlying the deformation
tensor.
-/
noncomputable def covariantDerivativeTensor
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  (lowerVectorOneForm I regularity).comp
    (LeviCivitaConnection.covariantDerivative I connection regularity smooth)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem covariantDerivativeTensor_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (x : M) (direction test : TangentSpace I x) :
    covariantDerivativeTensor I regularity connection smooth field x direction test =
      inner ℝ (connection.connection field x direction) test := by
  rw [show covariantDerivativeTensor I regularity connection smooth field =
    lowerVectorOneForm I regularity
      (LeviCivitaConnection.covariantDerivative I connection regularity smooth field) from rfl]
  rw [lowerVectorOneForm_apply, LeviCivitaConnection.covariantDerivative_apply]

/--
The deformation tensor `Def u`, obtained by symmetrizing the metric-lowered
covariant derivative.  This is a first-order operator
`C^(k+1)(TM) → C^k(T*M ⊗ T*M)`.
-/
noncomputable def deformationTensor
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  (symmetrizeCovariantTwoTensor I regularity).comp
    (covariantDerivativeTensor I regularity connection smooth)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem deformationTensor_apply
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (x : M) (first second : TangentSpace I x) :
    deformationTensor I regularity connection smooth field x first second =
      (2 : ℝ)⁻¹ *
        (inner ℝ (connection.connection field x first) second +
          inner ℝ (connection.connection field x second) first) := by
  rw [show deformationTensor I regularity connection smooth field =
    symmetrizeCovariantTwoTensor I regularity
      (covariantDerivativeTensor I regularity connection smooth field) from rfl]
  rw [symmetrizeCovariantTwoTensor_apply, covariantDerivativeTensor_apply,
    covariantDerivativeTensor_apply]

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
theorem deformationTensor_symmetric
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) :
    transposeCovariantTwoTensor I regularity
        (deformationTensor I regularity connection smooth field) =
      deformationTensor I regularity connection smooth field :=
  symmetrizeCovariantTwoTensor_symmetric I regularity
    (covariantDerivativeTensor I regularity connection smooth field)

/-- A concrete smooth vector field is divergence-free when its intrinsic divergence vanishes. -/
def IsDivergenceFree
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) : Prop :=
  divergence I connection regularity smooth field = 0

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
theorem isDivergenceFree_iff_pointwise
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) :
    IsDivergenceFree I connection regularity smooth field ↔
      ∀ x, tangentTrace I x (connection.connection field x) = 0 := by
  constructor
  · intro h x
    have pointwise := DFunLike.congr_fun h x
    simpa using pointwise
  · intro h
    ext x
    simpa using h x

end RiemannianFluids
