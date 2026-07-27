import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Regularity-indexed tensor fields

Before defining an operator, we must say what kind of field it acts on. A tensor field assigns an object in a fiber over each point and varies
smoothly:

    scalar field:                 x ↦ f(x)        in ℝ,
    vector field:                 x ↦ u(x)        in T_xM,
    one-form:                     x ↦ α(x)        in T_x*M,
    tangent-valued one-form:      x ↦ A(x)        in Hom(T_xM,T_xM),
    covariant two-tensor:         x ↦ T(x)        in Hom(T_xM,T_x*M).

Mathlib's `ContMDiffSection` packages both the dependent function and the proof that it is `C^k`. The abbreviations below give mathematical names to
the particular bundles used by the fluid argument; they introduce no new axioms or data.

## Regularity is part of the analysis

Geometric-analysis prose writes `u`, `∇u`, and `Δu` without decorating every symbol by a differentiability class. The proof still assumes enough
derivatives exist. Here that bookkeeping is visible in the types:

    ∇ : C^(k+1) → C^k,
    Δ : C^(k+2) → C^k.

This prevents a second-order identity from accidentally being stated as an endomorphism of one undifferentiated space. It also explains why the same
mathematical field may appear at several regularities: restriction forgets excess smoothness, never values.

## Why the curried tensor representation

A covariant two-tensor is represented as a continuous linear map whose value is another continuous linear map, `X ↦ (Y ↦ T(X,Y))`. This is mathlib's
native representation of continuous multilinear structure. It makes composition and smooth bundle application available, while later pointwise
theorems recover the familiar notation `T(X,Y)`.

The file is deliberately declarative. It establishes the vocabulary used by the subsequent proof, much as a paper fixes notation before beginning its
argument.
-/

namespace RiemannianFluids

open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]

/--
`C^k` sections of the tangent bundle. This is the formal type of a velocity field before any divergence-free or boundary condition is imposed.
-/
abbrev SmoothVectorField (regularity : ℕ∞ω) :=
  ContMDiffSection I E regularity (TangentSpace I : M → Type _)

/--
`C^k` real-valued scalar fields. Pressure and the output of divergence use this type.
-/
abbrev SmoothScalarField (regularity : ℕ∞ω) :=
  ContMDiffMap I 𝓘(ℝ) M ℝ regularity

/--
`C^k` sections of the cotangent bundle. CCD17 identifies a vector field with its metric-lowered one-form; this development keeps the two types
distinct and uses `flat` and `sharp` for the conversion.
-/
abbrev SmoothOneForm (regularity : ℕ∞ω) :=
  ContMDiffSection I (E →L[ℝ] ℝ) regularity
    (fun x : M => TangentSpace I x →L[ℝ] ℝ)

/--
`C^k` alternating differential forms of a fixed degree. Degree two is needed to type the `d* d` half of the Hodge Laplacian on one-forms.
-/
abbrev SmoothDifferentialForm (degree : ℕ) (regularity : ℕ∞ω) :=
  ContMDiffSection I (E [⋀^Fin degree]→L[ℝ] ℝ) regularity
    (fun x : M => TangentSpace I x [⋀^Fin degree]→L[ℝ] ℝ)

/--
`C^k` tangent-valued one-forms. At a point this is a linear map `X ↦ ∇_X u`, so it is the natural codomain of a covariant derivative.
-/
abbrev SmoothVectorOneForm (regularity : ℕ∞ω) :=
  ContMDiffSection I (E →L[ℝ] E) regularity
    (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)

/--
`C^k` covariant two-tensor fields. Metric-lowering the output of `∇u` gives `(X,Y) ↦ g(∇_X u,Y)` in this type; symmetrizing it gives `Def u`.
-/
abbrev SmoothCovariantTwoTensor (regularity : ℕ∞ω) :=
  ContMDiffSection I (E →L[ℝ] E →L[ℝ] ℝ) regularity
    (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

end RiemannianFluids
