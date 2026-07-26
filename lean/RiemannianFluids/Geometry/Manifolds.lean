import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# The mathlib boundary for Riemannian surfaces

This module does not redevelop manifolds, tangent bundles, Riemannian metrics,
or covariant derivatives.  It records the two pieces of data not yet supplied
as a complete construction by mathlib for this project:

* the model vector space has intrinsic real dimension two;
* a chosen tangent-bundle connection is metric-compatible and torsion-free.

The second item is an explicit witness, not a claim that this project has
already constructed the Levi-Civita connection.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

/-- The intrinsic, rather than ambient, dimension-two requirement for a surface model. -/
class IsSurfaceModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop where
  finrank_eq_two : Module.finrank ℝ E = 2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- A vector field in mathlib's dependent tangent-bundle representation. -/
abbrev RiemannianVectorField := (x : M) → TangentSpace I x

/-- Metric compatibility specialized to a connection on the tangent bundle. -/
def IsMetricCompatibleTangentConnection
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {x : M} {X σ τ : RiemannianVectorField I},
    MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      d% (fun y => inner ℝ (σ y) (τ y)) x (X x) =
        inner ℝ (connection σ x (X x)) (τ x) +
          inner ℝ (σ x) (connection τ x (X x))

/--
An explicit witness for the defining properties of the Levi-Civita connection.

Existence and uniqueness are future geometric rungs.  Downstream operator
theorems must take this witness as a visible hypothesis until those rungs have
been proved.
-/
structure LeviCivitaWitness where
  connection : CovariantDerivative I E (TangentSpace I : M → Type _)
  metricCompatible : IsMetricCompatibleTangentConnection I connection
  torsionFree : connection.torsion = 0

end RiemannianFluids
