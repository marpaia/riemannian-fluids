import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import RiemannianFluids.Geometry.Manifolds
import RiemannianFluids.Tensors.SmoothSections

/-!
# Connections on a Riemannian tangent bundle

Mathlib supplies bundled covariant derivatives, their differentiability
contract, metric differentiation, and torsion.  This module packages the
properties that characterize a chosen Levi-Civita connection while leaving
existence and uniqueness as explicit future obligations.

The tangent bundle already has additive and module instances before a
`RiemannianBundle` equips its fibers with normed inner-product instances.  In
the pinned mathlib version those two instance paths prevent the general
`CovariantDerivative.IsMetricCompatible` predicate from elaborating directly
for a tangent connection.  `IsMetricCompatibleTangentConnection` is exactly
the tangent specialization of the identity in
`CovariantDerivative.isMetricCompatible_iff`; keeping this bridge localized
avoids propagating the instance mismatch into the geometric API.
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

/-- The metric-derivative identity for a connection on the tangent bundle. -/
def IsMetricCompatibleTangentConnection
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {x : M} {X σ τ : RiemannianVectorField I},
    MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      d% (fun y => inner ℝ (σ y) (τ y)) x (X x) =
        inner ℝ (connection σ x (X x)) (τ x) +
          inner ℝ (σ x) (connection τ x (X x))

/--
A chosen tangent connection satisfying the defining Levi-Civita properties.

The structure contains no existence or uniqueness claim.  Regularity is also
kept separate because each differential operator must state the precise class
of connection it consumes.
-/
structure LeviCivitaConnection where
  connection : CovariantDerivative I E (TangentSpace I : M → Type _)
  metricCompatible : IsMetricCompatibleTangentConnection I connection
  torsionFree : connection.torsion = 0

namespace LeviCivitaConnection

/-- The native mathlib regularity predicate for the packaged connection. -/
def IsContMDiff
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω) : Prop :=
  CovariantDerivative.ContMDiffCovariantDerivative connection.connection regularity

set_option backward.isDefEq.respectTransparency false in
/--
Covariant differentiation as a regularity-losing linear operator
`C^(k+1)(TM) -> C^k(Hom(TM, TM))`.
-/
noncomputable def covariantDerivative
    (connection : LeviCivitaConnection (M := M) I) (regularity : ℕ∞ω)
    (smooth : IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothVectorOneForm (M := M) I regularity where
  toFun field :=
    { toFun := connection.connection field
      contMDiff_toFun := by
        rw [← contMDiffOn_univ]
        exact smooth.contMDiff.contMDiff field.contMDiff.contMDiffOn }
  map_add' first second := by
    ext x direction
    exact DFunLike.congr_fun
      (connection.connection.isCovariantDerivativeOn.add
        (first.mdifferentiable' (by simp) x)
        (second.mdifferentiable' (by simp) x)) direction
  map_smul' scalar field := by
    ext x direction
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
