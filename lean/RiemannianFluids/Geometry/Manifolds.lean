import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The mathlib boundary for Riemannian surfaces

This module does not redevelop manifolds, tangent bundles, or Riemannian
metrics.  It records the intrinsic dimension contract used when a general
Riemannian-manifold theorem is specialized to a surface.

Connections and their regularity live in `RiemannianFluids.Geometry.Connections`.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

/-- The intrinsic, rather than ambient, dimension-two requirement for a surface model. -/
class IsSurfaceModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop where
  finrank_eq_two : Module.finrank ℝ E = 2

/-- A two-dimensional model space is nontrivial. -/
instance surfaceModel_nontrivial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [IsSurfaceModel E] : Nontrivial E :=
  Module.nontrivial_of_finrank_pos (by
    rw [IsSurfaceModel.finrank_eq_two]
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
Finite-dimensionality transfers from the manifold model to every tangent
fiber.  Mathlib's tangent fibers are definitionally modeled on `E`, but the
instance is intentionally made explicit at the project boundary so that
fiberwise trace and Riesz constructions do not rely on fragile synthesis.
-/
theorem tangentFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  FiniteDimensional.of_injective
    ({ toFun := fun v => v
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : TangentSpace I x →ₗ[ℝ] E)
    (by
      intro first second equality
      exact equality)

end RiemannianFluids
