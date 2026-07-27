import RiemannianFluids.Tensors.ScalarCalculus
import RiemannianFluids.Tensors.VectorCalculus

/-!
# Codifferential and Hodge-side operators

The Hodge side of the viscosity comparison is built from the de Rham complex

    Ω⁰(M) --d₀--> Ω¹(M) --d₁--> Ω²(M)

and the formal adjoints pointing in the opposite direction. On one-forms the analysis-positive Hodge Laplacian is

    L_Hodge = d₀ d₁* + d₂* d₁.

The subscripts only record degrees: the first summand goes from one-forms to scalars and back, while the second goes from one-forms to two-forms and
back. Papers usually suppress them and write `d d* + d* d`.

## The codifferential and the sign

For a one-form `α`, metric duality identifies the first codifferential with negative divergence:

    d₁* α = -div(α♯).

This fixes the sign convention for the whole file. Applied to the metric dual of a vector field, the musical inverse law gives

    d₁*(u♭) = -div u.

Consequently, if `u` is divergence-free, then `d₁*(u♭) = 0`, and applying `d₀` gives

    d₀ d₁*(u♭) = 0.

That tiny calculation is the concrete analytical step which removes the extra exact term from the final CCD17 identity. The theorem
`exactCodifferentialCorrection_eq_zero_of_divergenceFree` spells it out as three linear operations: lower `u`, apply `d d*`, and raise the result.

## Positive convention versus the paper

Chan--Czubak--Disconzi, arXiv:1608.05114v2, define after equation (1.3)

    Δ_H = -(d d* + d* d).

This repository instead names the nonnegative operator

    L_Hodge = d d* + d* d = -Δ_H.

The distinction matters: copying the paper's symbol while silently changing its sign would reverse the viscous term in the energy balance. The Lean
names therefore encode the repository convention, while the comments retain the paper notation needed to compare equations.

## What is constructed and what remains an interface

The degree-zero differential is already available from manifold derivatives, and `d₁*` on one-forms is constructed from divergence, so the entire
exact piece `d d*` is concrete. The pinned mathlib API does not yet provide the smooth degree-one exterior derivative `d₁` or the degree-two
codifferential `d₂*` in the form needed here. `OneFormHodgeData` asks a caller to supply those two maps separately. This is intentionally weaker and
more revealing than accepting an opaque Hodge Laplacian: the declaration still exhibits its two de Rham halves and their derivative losses.

The file therefore reaches exactly the formal boundary. It proves the divergence-free cancellation from concrete geometry, but it does not disguise
missing differential-form infrastructure as a theorem.
-/

namespace RiemannianFluids

open Bundle
open scoped ContDiff Manifold

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
The regularity required as input to a second-order operator with `C^k` output. Writing the two increments separately mirrors the composition of two
first-order operators and avoids treating a Laplacian as an untyped endomorphism.
-/
abbrev SecondOrderRegularity (regularity : ℕ∞ω) := (regularity + 1) + 1

/--
Analysis-positive codifferential on one-forms: `d* α = -div (α♯)`.

This identity fixes the sign convention. The definition is a composition of two concrete maps: raise `α` to a vector field and take minus its
intrinsic divergence. It loses one derivative because divergence does.
-/
noncomputable def codifferentialOne
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I (regularity + 1) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothOneForm (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothScalarField (M := M) I regularity :=
  -- Read right to left: `α ↦ α♯ ↦ -div(α♯)`.
  -(divergence I connection regularity smooth).comp (sharp I (regularity + 1))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Unfolding `d*` exposes its definition as negative divergence after raising. -/
@[simp]
theorem codifferentialOne_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I (regularity + 1) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (form : SmoothOneForm (M := M) I (regularity + 1)) :
    codifferentialOne I regularity connection smooth form =
      -divergence I connection regularity smooth (sharp I (regularity + 1) form) :=
  rfl

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- On a metric-lowered vector field, the codifferential is negative divergence. -/
@[simp]
theorem codifferentialOne_flat
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I (regularity + 1) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) :
    codifferentialOne I regularity connection smooth
        (flat I (regularity + 1) field) =
      -divergence I connection regularity smooth field := by
  -- Expand the codifferential, then cancel raising after lowering by the musical inverse law. This proves `d*(u♭) = -div u`.
  rw [codifferentialOne_apply, sharp_flat]

/--
The exact one-form correction `d d*`, with both derivative losses explicit. This is the extra `d d*` term in CCD17 equation (1.3), distinct from the
copy already contained in the Hodge Laplacian.
-/
noncomputable def exactCodifferentialCorrectionOne
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1)) :
    SmoothOneForm (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity :=
  -- Read right to left: apply `d*` to obtain a scalar, then apply the degree-zero exterior derivative `d`.
  (scalarDifferential I regularity).comp
    (codifferentialOne I (regularity + 1) connection smooth)

/--
The vector-field realization `(d d* (u♭))♯` of the exact correction. The paper identifies these types; Lean records the lowering before and raising
after the one-form operator.
-/
noncomputable def exactCodifferentialCorrection
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1)) :
    SmoothVectorField (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity :=
  -- Read right to left: lower `u`, apply `d d*`, and raise the output.
  (sharp I regularity).comp
    ((exactCodifferentialCorrectionOne I regularity connection smooth).comp
      (flat I (SecondOrderRegularity regularity)))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
theorem exactCodifferentialCorrection_eq_zero_of_divergenceFree
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (hdiv : IsDivergenceFree I connection (regularity + 1) smooth field) :
    exactCodifferentialCorrection I regularity connection smooth field = 0 := by
  -- Expose the three compositions so the codifferential theorem can rewrite the middle scalar field.
  rw [show exactCodifferentialCorrection I regularity connection smooth field =
    sharp I regularity
      (scalarDifferential I regularity
        (codifferentialOne I (regularity + 1) connection smooth
          (flat I (SecondOrderRegularity regularity) field))) from rfl]
  -- `d*(u♭) = -div u`; divergence-freeness makes this zero, and both linear maps `d` and `sharp` preserve zero. This formalizes the sentence after
  -- CCD17 equation (1.3).
  rw [codifferentialOne_flat, hdiv, neg_zero, LinearMap.map_zero, LinearMap.map_zero]

/--
The currently missing degree-one part of the de Rham complex. Supplying this data is the exact boundary needed to construct the Hodge Laplacian on
one-forms without postulating the already-combined Laplacian.

The fields are not axioms: a caller must construct them. Packaging `d₁` and `d₂*` separately ensures that the Hodge Laplacian below is visibly
assembled from the same two halves used in the literature.
-/
structure OneFormHodgeData (regularity : ℕ∞ω) where
  /-- Exterior derivative `d₁ : Ω¹ → Ω²`, losing one derivative. -/
  exteriorOne :
    SmoothOneForm (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I 2 (regularity + 1)
  /-- Codifferential `d₂* : Ω² → Ω¹`, losing one derivative. -/
  codifferentialTwo :
    SmoothDifferentialForm (M := M) I 2 (regularity + 1) →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity

/--
Analysis-positive Hodge Laplacian `d d* + d* d` on one-forms.

CCD17 writes `Δ_H = -(d d* + d* d)`. This declaration is therefore the repository's `L_Hodge = -Δ_H`, not the paper's signed `Δ_H`.
-/
noncomputable def OneFormHodgeData.hodgeLaplacian
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (data : OneFormHodgeData (M := M) I regularity) :
    SmoothOneForm (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity :=
  -- First summand: `d₀ d₁*`; second summand: `d₂* d₁`.
  exactCodifferentialCorrectionOne I regularity connection smooth +
    data.codifferentialTwo.comp data.exteriorOne

/--
Vector-field Hodge Laplacian obtained through the musical equivalence. This is the explicit Lean version of the paper's convention of identifying a
vector field with its metric-dual one-form.
-/
noncomputable def OneFormHodgeData.hodgeLaplacianVector
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (data : OneFormHodgeData (M := M) I regularity) :
    SmoothVectorField (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity :=
  -- Read right to left: `u ↦ u♭ ↦ L_Hodge(u♭) ↦ (L_Hodge(u♭))♯`.
  (sharp I regularity).comp
    ((data.hodgeLaplacian I regularity connection smooth).comp
      (flat I (SecondOrderRegularity regularity)))

end RiemannianFluids
