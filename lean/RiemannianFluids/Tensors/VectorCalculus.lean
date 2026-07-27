import RiemannianFluids.Geometry.Connections
import RiemannianFluids.Geometry.Musical
import RiemannianFluids.Tensors.Contraction
import RiemannianFluids.Tensors.Symmetry

/-!
# First-order calculus of vector fields

This is where the separately formalized operations begin to read like vector calculus. Starting from a smooth Levi-Civita connection, one derivative
of a vector field produces

    ∇u : X ↦ ∇_X u.

There are two different ways to consume its two indices, and the distinction drives the rest of the development.

## Contracting gives divergence

If we contract the tangent input of `∇u` against its tangent output, we get

    div u = tr(X ↦ ∇_Xu).

The coordinate formula `∇ᵢuⁱ` is only a representation of this trace. Because `Tensors.Contraction` has already established coordinate invariance and
smoothness, the Lean definition is simply composition:

    divergence = trace ∘ covariantDerivative.

It loses one derivative, so `C^(k+1)` vector fields produce `C^k` scalars.

## Lowering and symmetrizing gives strain

Instead of contracting, lower the output vector with the metric and retain both arguments:

    (∇u)♭(X,Y) = g(∇_Xu,Y).

Its symmetric part is the deformation tensor

    Def u(X,Y)
      = 1/2 [g(∇_Xu,Y) + g(∇_Yu,X)].

This is exactly equation (1.2) of Chan--Czubak--Disconzi, arXiv:1608.05114v2, written without indices. The construction is again a composition of
already justified maps:

    deformationTensor = symmetrize ∘ lower ∘ covariantDerivative.

The pointwise theorem unwraps those three maps to recover the displayed paper formula. The symmetry theorem needs no new calculation: it applies the
fact that symmetrization lands in the fixed points of transpose.

## Divergence-free as an equality of sections

Finally, `IsDivergenceFree` says that the bundled scalar field `div u` is the zero section. The accompanying theorem translates this global equality
into the pointwise trace condition. This matters one layer later: the codifferential identity `d*(u♭) = -div u` turns this constraint into the
vanishing of the extra `d d*` term in CCD17 equation (1.3).

Every definition in the file is therefore a transparent composition. The earlier bundle-coordinate proofs did the work required to make the familiar
informal calculus type-correct and coordinate-independent here.
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
Intrinsic divergence, defined as the fiberwise trace of the covariant derivative:

`div u = tr (X ↦ ∇_X u)`.

The definition is coordinate-free because `traceVectorOneForm` already proved invariance of trace under change-of-frame conjugation.
-/
noncomputable def divergence
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothScalarField (M := M) I regularity :=
  -- Read right to left: differentiate the vector field, then contract its tangent input and output by taking the trace.
  (traceVectorOneForm I regularity).comp
    (LeviCivitaConnection.covariantDerivative I connection regularity smooth)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Pointwise divergence is the trace of the covariant-derivative endomorphism. -/
@[simp]
theorem divergence_apply
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) (x : M) :
    divergence I connection regularity smooth field x =
      tangentTrace I x (connection.connection field x) :=
  rfl

/--
The covariant derivative with its tangent-valued output lowered by the metric. This is the unsymmetrized covariant two-tensor underlying the
deformation tensor.
-/
noncomputable def covariantDerivativeTensor
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  -- Read right to left: form `X ↦ ∇_X u`, then lower the resulting vector against a second tangent argument with the metric.
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
  -- Expose the two composed linear maps at the supplied field.
  rw [show covariantDerivativeTensor I regularity connection smooth field =
    lowerVectorOneForm I regularity
      (LeviCivitaConnection.covariantDerivative I connection regularity smooth field) from rfl]
  -- Evaluate metric lowering and covariant differentiation pointwise.
  rw [lowerVectorOneForm_apply, LeviCivitaConnection.covariantDerivative_apply]

/--
The deformation tensor `Def u`, obtained by symmetrizing the metric-lowered covariant derivative. This is a first-order operator `C^(k+1)(TM) →
C^k(T*M ⊗ T*M)`.

This is CCD17 equation (1.2), with the paper's coordinate indices replaced by two explicit tangent arguments. The factor `1/2` belongs here; the
associated viscosity operator is later named `L_Def = 2 Def* Def`.
-/
noncomputable def deformationTensor
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  -- Read right to left: construct `(X,Y) ↦ g(∇_X u,Y)`, then average it with the tensor obtained by swapping `X` and `Y`.
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
  -- Reveal `Def` as symmetrization of the lowered covariant derivative.
  rw [show deformationTensor I regularity connection smooth field =
    symmetrizeCovariantTwoTensor I regularity
      (covariantDerivativeTensor I regularity connection smooth field) from rfl]
  -- Apply the pointwise symmetrization formula and evaluate each lowered covariant derivative. The result is CCD17 equation (1.2).
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
  -- `Def u` is symmetric because it lies in the image of the symmetrization projection proved in `Tensors.Symmetry`.
  symmetrizeCovariantTwoTensor_symmetric I regularity
    (covariantDerivativeTensor I regularity connection smooth field)

/--
A concrete smooth vector field is divergence-free when its intrinsic divergence vanishes. CCD17 uses the equivalent one-form statement `d* u♭ = 0`
immediately after equation (1.3); `codifferentialOne_flat` proves that equivalence with the repository's sign convention.
-/
def IsDivergenceFree
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) : Prop :=
  divergence I connection regularity smooth field = 0

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Bundled divergence-freeness is equivalent to vanishing trace at every point. -/
theorem isDivergenceFree_iff_pointwise
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) :
    IsDivergenceFree I connection regularity smooth field ↔
      ∀ x, tangentTrace I x (connection.connection field x) = 0 := by
  -- The bundled equality `div field = 0` and its pointwise form are equivalent.
  constructor
  -- Forward direction: evaluate the equality of scalar fields at `x`.
  · intro h x
    have pointwise := DFunLike.congr_fun h x
    -- Unfolding `divergence` turns the evaluated equality into the displayed trace equation.
    simpa using pointwise
  -- Reverse direction: prove equality of scalar fields pointwise.
  · intro h
    ext x
    -- The supplied pointwise trace equation is exactly the desired value.
    simpa using h x

end RiemannianFluids
