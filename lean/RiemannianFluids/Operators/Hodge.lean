import RiemannianFluids.Tensors.ScalarCalculus
import RiemannianFluids.Tensors.VectorCalculus

/-!
# Codifferential and Hodge-side operators

With the analysis-positive convention, the codifferential on one-forms is
`d* α = -div (α♯)`.  This module constructs that operator and the exact
second-order correction `d d*` concretely.  The degree-one exterior derivative
and degree-two codifferential are exposed as data because the pinned manifold
API does not yet supply those operators on smooth differential forms.
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

/-- The regularity required as input to a second-order operator with `C^k` output. -/
abbrev SecondOrderRegularity (regularity : ℕ∞ω) := (regularity + 1) + 1

/-- Analysis-positive codifferential on one-forms: `d* α = -div (α♯)`. -/
noncomputable def codifferentialOne
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I (regularity + 1) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothOneForm (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothScalarField (M := M) I regularity :=
  -(divergence I connection regularity smooth).comp (sharp I (regularity + 1))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
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
  rw [codifferentialOne_apply, sharp_flat]

/-- The exact one-form correction `d d*`, with both derivative losses explicit. -/
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
  (scalarDifferential I regularity).comp
    (codifferentialOne I (regularity + 1) connection smooth)

/-- The vector-field realization `(d d* (u♭))♯` of the exact correction. -/
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
  rw [show exactCodifferentialCorrection I regularity connection smooth field =
    sharp I regularity
      (scalarDifferential I regularity
        (codifferentialOne I (regularity + 1) connection smooth
          (flat I (SecondOrderRegularity regularity) field))) from rfl]
  rw [codifferentialOne_flat, hdiv, neg_zero, LinearMap.map_zero, LinearMap.map_zero]

/--
The currently missing degree-one part of the de Rham complex.  Supplying this
data is the exact boundary needed to construct the Hodge Laplacian on
one-forms without postulating the already-combined Laplacian.
-/
structure OneFormHodgeData (regularity : ℕ∞ω) where
  exteriorOne :
    SmoothOneForm (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I 2 (regularity + 1)
  codifferentialTwo :
    SmoothDifferentialForm (M := M) I 2 (regularity + 1) →ₗ[ℝ]
      SmoothOneForm (M := M) I regularity

/-- Analysis-positive Hodge Laplacian `d d* + d* d` on one-forms. -/
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
  exactCodifferentialCorrectionOne I regularity connection smooth +
    data.codifferentialTwo.comp data.exteriorOne

/-- Vector-field Hodge Laplacian obtained through the musical equivalence. -/
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
  (sharp I regularity).comp
    ((data.hodgeLaplacian I regularity connection smooth).comp
      (flat I (SecondOrderRegularity regularity)))

end RiemannianFluids
