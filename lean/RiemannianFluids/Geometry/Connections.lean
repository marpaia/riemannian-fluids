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
