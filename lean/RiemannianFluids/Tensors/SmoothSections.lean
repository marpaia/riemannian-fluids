import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Regularity-indexed tensor fields

The formal geometric layer uses bundled `C^k` sections.  In particular, a
differential operator records its loss of regularity instead of being modeled
as an endomorphism of an undifferentiated ambient vector space.
-/

namespace RiemannianFluids

open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]

/-- `C^k` sections of the tangent bundle. -/
abbrev SmoothVectorField (regularity : ℕ∞ω) :=
  ContMDiffSection I E regularity (TangentSpace I : M → Type _)

/-- `C^k` real-valued scalar fields. -/
abbrev SmoothScalarField (regularity : ℕ∞ω) :=
  ContMDiffMap I 𝓘(ℝ) M ℝ regularity

/-- `C^k` sections of the cotangent bundle. -/
abbrev SmoothOneForm (regularity : ℕ∞ω) :=
  ContMDiffSection I (E →L[ℝ] ℝ) regularity
    (fun x : M => TangentSpace I x →L[ℝ] ℝ)

/-- `C^k` differential forms of a fixed degree. -/
abbrev SmoothDifferentialForm (degree : ℕ) (regularity : ℕ∞ω) :=
  ContMDiffSection I (E [⋀^Fin degree]→L[ℝ] ℝ) regularity
    (fun x : M => TangentSpace I x [⋀^Fin degree]→L[ℝ] ℝ)

/-- `C^k` tangent-valued one-forms, the codomain of a covariant derivative. -/
abbrev SmoothVectorOneForm (regularity : ℕ∞ω) :=
  ContMDiffSection I (E →L[ℝ] E) regularity
    (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)

/-- `C^k` covariant two-tensor fields. -/
abbrev SmoothCovariantTwoTensor (regularity : ℕ∞ω) :=
  ContMDiffSection I (E →L[ℝ] E →L[ℝ] ℝ) regularity
    (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

end RiemannianFluids
