import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The mathlib boundary for Riemannian surfaces

The geometric analysis takes place on a Riemannian manifold, but this repository should not bury its argument under a second implementation of
manifold foundations. Mathlib already supplies charts, tangent bundles, smooth sections, and Riemannian metrics. This file marks the narrow boundary
between that library and the objects named by the fluid proof.

## Intrinsic dimension, not an embedding

A surface is two-dimensional because every tangent space has two independent directions. It need not be presented as a subset of `ℝ³`. Mathlib
describes a manifold using a model vector space `E`; the condition

    finrank_ℝ E = 2

therefore expresses intrinsic dimension two. `IsSurfaceModel` records exactly that fact and nothing about an ambient space.

The only theorem in this file extracts a small consequence Lean later needs: a two-dimensional vector space is nontrivial. The proof replaces the
abstract dimension with `2`, proves `0 < 2`, and asks mathlib to transfer positive dimension into `Nontrivial E`. This is mathematically elementary,
but installing the instance explicitly keeps tensor and operator-norm constructions from failing for typeclass reasons far from their source.

## Why orientation is absent

The registered CCD17 claim is stated for an oriented surface, but none of the current steps--musical duality, trace, covariant differentiation,
symmetrization, or the algebraic operator comparison--uses an orientation. Orientation should first appear when a concrete Hodge-star or integration
construction actually consumes it. Adding it here would make the formal statement stronger without teaching us where the hypothesis matters.

Connections and their regularity begin in `Geometry.Connections`; this module does not assert the existence of a Levi-Civita connection. Its purpose
is only to make dimension and tangent-field notation explicit at the library boundary.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

/-- A first-class witness for the geometric hypotheses in the compact Hodge theorem.

The carrier types and Mathlib instances are fields so that a literature package can retain
the actual manifold setting as data instead of replacing it by a Boolean-style `Prop`
flag.  The analytic realization of differential forms may still be supplied separately. -/
structure CompactBoundarylessRiemannianManifoldData where
  E : Type
  [normedAddCommGroupE : NormedAddCommGroup E]
  [normedSpaceE : NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E]
  H : Type
  [topologicalSpaceH : TopologicalSpace H]
  I : ModelWithCorners ℝ E H
  M : Type
  [metricSpaceM : MetricSpace M]
  [chartedSpaceM : ChartedSpace H M]
  [isManifoldM : IsManifold I 1 M]
  [compactSpaceM : CompactSpace M]
  [boundarylessManifoldM : BoundarylessManifold I M]
  [riemannianBundleM : RiemannianBundle (fun x : M => TangentSpace I x)]

/-- A first-class witness for the geometric hypotheses in the complete-manifold
Hodge--Kodaira theorem. -/
structure CompleteBoundarylessRiemannianManifoldData where
  E : Type
  [normedAddCommGroupE : NormedAddCommGroup E]
  [normedSpaceE : NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E]
  H : Type
  [topologicalSpaceH : TopologicalSpace H]
  I : ModelWithCorners ℝ E H
  M : Type
  [metricSpaceM : MetricSpace M]
  [chartedSpaceM : ChartedSpace H M]
  [isManifoldM : IsManifold I 1 M]
  [completeSpaceM : CompleteSpace M]
  [boundarylessManifoldM : BoundarylessManifold I M]
  [riemannianBundleM : RiemannianBundle (fun x : M => TangentSpace I x)]

/--
The intrinsic, rather than ambient, dimension-two requirement for a surface model. `E` is the model vector space used by `ModelWithCorners`; asserting
`finrank E = 2` says that tangent spaces are two-dimensional regardless of any later embedding into an ambient Euclidean space.
-/
class IsSurfaceModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop where
  finrank_eq_two : Module.finrank ℝ E = 2

/--
A two-dimensional model space is nontrivial.

Lean needs this instance to put the expected norm on spaces of continuous bilinear maps. Mathematically it is the elementary implication `dim E = 2 ⇒
E ≠ {0}`.
-/
instance surfaceModel_nontrivial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [IsSurfaceModel E] : Nontrivial E :=
  Module.nontrivial_of_finrank_pos (by
    -- Replace the abstract dimension by the surface assumption.
    rw [IsSurfaceModel.finrank_eq_two]
    -- The remaining arithmetic fact is `0 < 2`.
    norm_num)

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]

/-- A vector field in mathlib's dependent tangent-bundle representation. -/
abbrev RiemannianVectorField := (x : M) → TangentSpace I x

omit [CompleteSpace E] [IsManifold I 1 M] in
set_option backward.isDefEq.respectTransparency false in
/--
Finite-dimensionality transfers from the manifold model to every tangent fiber. Mathlib's tangent fibers are definitionally modeled on `E`, but the
instance is intentionally made explicit at the project boundary so that fiberwise trace and Riesz constructions do not rely on fragile synthesis.
-/
theorem tangentFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  -- Mathlib's tangent fiber is modeled on `E`. It suffices to exhibit the identity-on-values linear map from the tangent fiber into `E` and prove it
  -- injective; finite-dimensionality then transfers along that injection.
  FiniteDimensional.of_injective
    ({ toFun := fun v => v
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : TangentSpace I x →ₗ[ℝ] E)
    (by
      -- Injectivity is definitional because both sides carry the same value.
      intro first second equality
      exact equality)

end RiemannianFluids
