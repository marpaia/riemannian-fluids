import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Connections on a Riemannian tangent bundle

A covariant derivative tells us how to differentiate a vector field in a tangent direction:

    (u,X) ↦ ∇_Xu.

Unlike an ordinary derivative, the values `u(x)` and `u(y)` live in different tangent spaces, so subtracting them requires connection data. The
Levi-Civita connection is the unique connection compatible with the metric and free of torsion. Those two conditions mean

    X g(σ,τ) = g(∇_Xσ,τ) + g(σ,∇_Xτ),
    ∇_XY - ∇_YX = [X,Y].

This is the `∇` used in CCD17 equation (1.2) to define `Def u` and in the rough Laplacian `∇*∇` of equation (1.1).

## The formal boundary

Mathlib supplies a bundled `CovariantDerivative`, its differentiability theory, metric differentiation, and torsion. This repository packages a
*chosen* connection with the two Levi-Civita properties. It does not yet derive that connection from the metric or prove existence and uniqueness.
Making the choice explicit lets the downstream analysis proceed while keeping that missing geometric theorem visible in every relevant type.

The metric-compatibility predicate is written out for the tangent bundle. This is a localized Lean adaptation: in the pinned mathlib revision, the
tangent bundle acquires compatible additive/module structures through one instance path and normed inner-product structures through another, which
prevents the fully general predicate from elaborating cleanly. The displayed identity is mathematically the same specialization of mathlib's
`isMetricCompatible_iff`.

## Covariant differentiation as an operator on sections

If the connection coefficients are `C^k` and `u` is `C^(k+1)`, then `∇u` is `C^k`. Lean records that loss in the operator type

    C^(k+1)(TM) → C^k(Hom(TM,TM)).

At a point, the output is the endomorphism `X ↦ ∇_Xu`. The bundled construction below has three obligations: the pointwise formula defines a smooth
section, it respects addition in `u`, and it respects multiplication by constant real scalars. Mathlib's covariant-derivative laws discharge the last
two. The final `_apply` theorem is `rfl` because the representation was chosen so evaluating the bundled operator exposes the original connection
without a translation lemma.
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
The metric-derivative identity for a connection on the tangent bundle:

`X g(σ,τ) = g(∇_X σ,τ) + g(σ,∇_X τ)`.

The three `MDiffAt` hypotheses are the Lean form of the informal phrase "for differentiable vector fields near `x`".
-/
def IsMetricCompatibleTangentConnection
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {x : M} {X σ τ : RiemannianVectorField I},
    MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      d% (fun y => inner ℝ (σ y) (τ y)) x (X x) =
        inner ℝ (connection σ x (X x)) (τ x) +
          inner ℝ (σ x) (connection τ x (X x))

/--
A chosen tangent connection satisfying the defining Levi-Civita properties.

The structure contains no existence or uniqueness claim. Regularity is also kept separate because each differential operator must state the precise
class of connection it consumes.
-/
structure LeviCivitaConnection where
  /-- The underlying covariant derivative supplied by mathlib. -/
  connection : CovariantDerivative I E (TangentSpace I : M → Type _)
  /-- Preservation of the Riemannian metric under parallel differentiation. -/
  metricCompatible : IsMetricCompatibleTangentConnection I connection
  /-- Vanishing torsion, the second defining Levi-Civita property. -/
  torsionFree : connection.torsion = 0

namespace LeviCivitaConnection

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Two Levi--Civita connections have the same value on differentiable direction and field
germs.  This is the uniqueness half of the fundamental theorem of Riemannian geometry at the
level needed by the operator corpus.

The bundled `CovariantDerivative` type accepts arbitrary raw sections, so literal structure
equality would incorrectly assert agreement on its unconstrained junk values for
nondifferentiable fields.  The mathematically meaningful statement is therefore this pointwise
equality on differentiable fields.  The proof uses only the two defining properties: the
difference tensor is symmetric by torsion-freeness and skew-adjoint by metric compatibility,
hence vanishes. -/
theorem eq_on_mdifferentiable
    (first second : LeviCivitaConnection (M := M) I)
    {direction field : (x : M) → TangentSpace I x} {x : M}
    (hdirection : MDiffAt (T% direction) x)
    (hfield : MDiffAt (T% field) x) :
    first.connection field x (direction x) =
      second.connection field x (direction x) := by
  let differenceTensor
      (X Y : (y : M) → TangentSpace I y) : TangentSpace I x :=
    first.connection Y x (X x) - second.connection Y x (X x)
  have symmetric (X Y : (y : M) → TangentSpace I y)
      (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
      differenceTensor X Y = differenceTensor Y X := by
    have torsionFirst :=
      first.connection.torsion_eq_zero_iff.mp first.torsionFree hX hY
    have torsionSecond :=
      second.connection.torsion_eq_zero_iff.mp second.torsionFree hX hY
    dsimp only [differenceTensor]
    calc
      first.connection Y x (X x) - second.connection Y x (X x) =
          (first.connection Y x (X x) - first.connection X x (Y x)) -
            (second.connection Y x (X x) - second.connection X x (Y x)) +
            (first.connection X x (Y x) - second.connection X x (Y x)) := by
        abel
      _ = first.connection X x (Y x) - second.connection X x (Y x) := by
        rw [torsionFirst, torsionSecond, sub_self, zero_add]
  have skewAdjoint (X Y Z : (y : M) → TangentSpace I y)
      (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
      (hZ : MDiffAt (T% Z) x) :
      inner ℝ (differenceTensor X Y) (Z x) =
        -inner ℝ (Y x) (differenceTensor X Z) := by
    have metricFirst := first.metricCompatible hX hY hZ
    have metricSecond := second.metricCompatible hX hY hZ
    dsimp only [differenceTensor]
    rw [metricSecond] at metricFirst
    rw [inner_sub_left, inner_sub_right]
    linarith
  let difference : TangentSpace I x := differenceTensor direction field
  let testField : (y : M) → TangentSpace I y := FiberBundle.extend E difference
  have htest : MDiffAt (T% testField) x := FiberBundle.mdifferentiableAt_extend ..
  have htestValue : testField x = difference := by simp [testField]
  have hqneg : inner ℝ difference difference = -inner ℝ difference difference := by
    calc
      inner ℝ difference difference =
          inner ℝ (differenceTensor direction field) (testField x) := by
        rw [htestValue]
      _ = inner ℝ (differenceTensor field direction) (testField x) := by
        rw [symmetric direction field hdirection hfield]
      _ = -inner ℝ (direction x) (differenceTensor field testField) :=
        skewAdjoint field direction testField hfield hdirection htest
      _ = -inner ℝ (direction x) (differenceTensor testField field) := by
        rw [symmetric field testField hfield htest]
      _ = -inner ℝ (differenceTensor testField field) (direction x) := by
        rw [real_inner_comm]
      _ = inner ℝ (field x) (differenceTensor testField direction) := by
        simpa only [neg_neg] using congrArg Neg.neg
          (skewAdjoint testField field direction htest hfield hdirection)
      _ = inner ℝ (field x) (differenceTensor direction testField) := by
        rw [symmetric testField direction htest hdirection]
      _ = -inner ℝ (differenceTensor direction field) (testField x) := by
        have h := skewAdjoint direction field testField hdirection hfield htest
        linarith
      _ = -inner ℝ difference difference := by
        rw [htestValue]
  have hzero : inner ℝ difference difference = 0 := by linarith
  have : difference = 0 := inner_self_eq_zero.mp hzero
  exact sub_eq_zero.mp this

/-- If two differentiable ambient vector fields agree along a differentiable map, then their
Levi--Civita derivatives agree in every direction tangent to that map.

This is the restriction-locality statement needed by submanifold curvature.  It avoids the
currently missing general Mathlib theorem that a covariant derivative depends only on a
section's one-jet: metric compatibility reduces the claim to differentiating the scalar pairing
with an arbitrary test field along the source map. -/
theorem eq_on_mfderiv_of_comp_eq
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {H₀ : Type*} [TopologicalSpace H₀]
    {I₀ : ModelWithCorners ℝ E₀ H₀}
    {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
    [IsManifold I₀ 1 M₀]
    (connection : LeviCivitaConnection (M := M) I)
    {f : M₀ → M} {x : M₀} (hf : MDiffAt f x)
    {first second : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) (f x))
    (hsecond : MDiffAt (T% second) (f x))
    (agreement : ∀ y, first (f y) = second (f y))
    (direction : TangentSpace I₀ x) :
    connection.connection first (f x) (mfderiv I₀ I f x direction) =
      connection.connection second (f x) (mfderiv I₀ I f x direction) := by
  apply ext_inner_right ℝ
  intro test
  let directionField : (y : M) → TangentSpace I y :=
    FiberBundle.extend E (mfderiv I₀ I f x direction)
  let testField : (y : M) → TangentSpace I y := FiberBundle.extend E test
  have hdirectionField : MDiffAt (T% directionField) (f x) :=
    FiberBundle.mdifferentiableAt_extend ..
  have htestField : MDiffAt (T% testField) (f x) :=
    FiberBundle.mdifferentiableAt_extend ..
  have hdirectionValue :
      directionField (f x) = mfderiv I₀ I f x direction :=
    by simp [directionField]
  have htestValue : testField (f x) = test := by simp [testField]
  let scalarFirst : M → ℝ := fun y ↦ inner ℝ (first y) (testField y)
  let scalarSecond : M → ℝ := fun y ↦ inner ℝ (second y) (testField y)
  have hscalarFirst : MDiffAt scalarFirst (f x) :=
    MDifferentiableAt.inner_bundle
      (E := (TangentSpace I : M → Type _)) hfirst htestField
  have hscalarSecond : MDiffAt scalarSecond (f x) :=
    MDifferentiableAt.inner_bundle
      (E := (TangentSpace I : M → Type _)) hsecond htestField
  have scalarAgreement : scalarFirst ∘ f = scalarSecond ∘ f := by
    funext y
    change inner ℝ (first (f y)) (testField (f y)) =
      inner ℝ (second (f y)) (testField (f y))
    rw [agreement y]
  have chainFirst := mfderiv_comp_apply x hscalarFirst hf direction
  have chainSecond := mfderiv_comp_apply x hscalarSecond hf direction
  have scalarDerivativeAgreement :
      d% scalarFirst (f x) (mfderiv I₀ I f x direction) =
        d% scalarSecond (f x) (mfderiv I₀ I f x direction) := by
    calc
      d% scalarFirst (f x) (mfderiv I₀ I f x direction) =
          d% (scalarFirst ∘ f) x direction := chainFirst.symm
      _ = d% (scalarSecond ∘ f) x direction := by rw [scalarAgreement]
      _ = d% scalarSecond (f x) (mfderiv I₀ I f x direction) := chainSecond
  have metricFirst := connection.metricCompatible
    hdirectionField hfirst htestField
  have metricSecond := connection.metricCompatible
    hdirectionField hsecond htestField
  rw [hdirectionValue, htestValue] at metricFirst metricSecond
  rw [scalarDerivativeAgreement, metricSecond] at metricFirst
  rw [agreement x] at metricFirst
  linarith

/--
The native mathlib regularity predicate for the packaged connection. It is kept separate from `LeviCivitaConnection` because different operators
consume different numbers of derivatives.
-/
def IsContMDiff
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω) : Prop :=
  CovariantDerivative.ContMDiffCovariantDerivative connection.connection regularity

set_option backward.isDefEq.respectTransparency false in
/--
Covariant differentiation as a regularity-losing linear operator `C^(k+1)(TM) -> C^k(Hom(TM, TM))`.
-/
noncomputable def covariantDerivative
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothVectorOneForm (M := M) I regularity where
  toFun field :=
    -- The value is exactly mathlib's covariant derivative `X ↦ ∇_X field`.
    { toFun := connection.connection field
      contMDiff_toFun := by
        -- A section is globally `C^k` iff it is `C^k` on the universal set.
        rw [← contMDiffOn_univ]
        -- Mathlib's regularity theorem composes the `C^k` connection with the `C^(k+1)` input section, accounting for the lost derivative.
        exact smooth.contMDiff.contMDiff field.contMDiff.contMDiffOn }
  map_add' first second := by
    -- Equality of sections is checked pointwise and then on each direction.
    ext x direction
    -- The covariant derivative is additive in the differentiated field.
    exact DFunLike.congr_fun
      (connection.connection.isCovariantDerivativeOn.add
        (first.mdifferentiable' (by simp) x)
        (second.mdifferentiable' (by simp) x)) direction
  map_smul' scalar field := by
    -- Again reduce equality of sections to a point and tangent direction.
    ext x direction
    -- Constants pull through the covariant derivative.
    exact DFunLike.congr_fun
      (connection.connection.isCovariantDerivativeOn.smul_const scalar
        (field.mdifferentiable' (by simp) x)) direction

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem covariantDerivative_apply
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) (x : M) :
    covariantDerivative I connection regularity smooth field x =
      connection.connection field x :=
  rfl

end LeviCivitaConnection

end RiemannianFluids
