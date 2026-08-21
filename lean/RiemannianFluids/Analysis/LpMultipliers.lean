import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Bounded pointwise operators on `Lᵖ`

This module packages a strongly measurable, essentially uniformly bounded family of bounded
linear maps into a bounded operator between Bochner `Lᵖ` spaces.  Thin-shell comparison maps
are variable-coefficient fiber maps, so the constant-coefficient `ContinuousLinearMap.compLpL`
construction is not sufficient.
-/

namespace RiemannianFluids

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A strongly measurable family of continuous linear maps with one explicit almost-everywhere
operator-norm bound. -/
structure BoundedPointwiseLinearMap
    (α E F : Type*) [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure α) where
  toFun : α → E →L[ℝ] F
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  stronglyMeasurable : AEStronglyMeasurable toFun μ
  norm_le : ∀ᵐ x ∂μ, ‖toFun x‖ ≤ bound

namespace BoundedPointwiseLinearMap

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The pointwise application of a bounded measurable operator family preserves `Lᵖ`. -/
theorem apply_memLp (operator : BoundedPointwiseLinearMap α E F μ)
    (field : Lp E p μ) :
    MemLp (fun x ↦ operator.toFun x (field x)) p μ := by
  apply (Lp.memLp field).of_le_mul
  · exact (ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂
      (Lp.aestronglyMeasurable field) operator.stronglyMeasurable
  · filter_upwards [operator.norm_le] with x hx
    exact (operator.toFun x).le_opNorm (field x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Pointwise application on the `Lp` quotient. -/
def apply (operator : BoundedPointwiseLinearMap α E F μ)
    (field : Lp E p μ) : Lp F p μ :=
  (operator.apply_memLp field).toLp fun x ↦ operator.toFun x (field x)

omit [Fact (1 ≤ p)] in
/-- A representative of `operator.apply field` is the expected pointwise application. -/
theorem coeFn_apply (operator : BoundedPointwiseLinearMap α E F μ)
    (field : Lp E p μ) :
    operator.apply field =ᵐ[μ] fun x ↦ operator.toFun x (field x) :=
  MemLp.coeFn_toLp (operator.apply_memLp field)

omit [Fact (1 ≤ p)] in
theorem apply_add (operator : BoundedPointwiseLinearMap α E F μ)
    (left right : Lp E p μ) :
    operator.apply (left + right) = operator.apply left + operator.apply right := by
  apply Lp.ext
  filter_upwards [operator.coeFn_apply (left + right), operator.coeFn_apply left,
      operator.coeFn_apply right, Lp.coeFn_add left right,
      Lp.coeFn_add (operator.apply left) (operator.apply right)] with x hall hleft hright hinput houtput
  rw [hall, hinput, houtput]
  simp only [Pi.add_apply, map_add, hleft, hright]

omit [Fact (1 ≤ p)] in
theorem apply_smul (operator : BoundedPointwiseLinearMap α E F μ)
    (scalar : ℝ) (field : Lp E p μ) :
    operator.apply (scalar • field) = scalar • operator.apply field := by
  apply Lp.ext
  filter_upwards [operator.coeFn_apply (scalar • field), operator.coeFn_apply field,
      Lp.coeFn_smul scalar field, Lp.coeFn_smul scalar (operator.apply field)] with
      x hall hfield hinput houtput
  rw [hall, hinput, houtput]
  simp only [Pi.smul_apply, map_smul, hfield]

/-- The induced linear map on `Lp`. -/
def linearMap (operator : BoundedPointwiseLinearMap α E F μ) :
    Lp E p μ →ₗ[ℝ] Lp F p μ where
  toFun := operator.apply
  map_add' := operator.apply_add
  map_smul' := operator.apply_smul

omit [Fact (1 ≤ p)] in
/-- The explicit essential operator bound controls the induced `Lp` norm. -/
theorem norm_apply_le (operator : BoundedPointwiseLinearMap α E F μ)
    (field : Lp E p μ) :
    ‖operator.apply field‖ ≤ operator.bound * ‖field‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operator.coeFn_apply field, operator.norm_le] with x happly hnorm
  rw [happly]
  exact (operator.toFun x).le_opNorm (field x) |>.trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- A bounded measurable pointwise family induces a continuous linear map on Bochner `Lp`. -/
def toContinuousLinearMap (operator : BoundedPointwiseLinearMap α E F μ) :
    Lp E p μ →L[ℝ] Lp F p μ :=
  LinearMap.mkContinuous operator.linearMap operator.bound operator.norm_apply_le

@[simp] theorem toContinuousLinearMap_apply
    (operator : BoundedPointwiseLinearMap α E F μ) (field : Lp E p μ) :
    operator.toContinuousLinearMap field = operator.apply field :=
  rfl

theorem norm_toContinuousLinearMap_le
    (operator : BoundedPointwiseLinearMap α E F μ) :
    ‖(operator.toContinuousLinearMap : Lp E p μ →L[ℝ] Lp F p μ)‖ ≤ operator.bound :=
  (operator.toContinuousLinearMap : Lp E p μ →L[ℝ] Lp F p μ).opNorm_le_bound
    operator.bound_nonneg
    operator.norm_apply_le

end BoundedPointwiseLinearMap

end

end RiemannianFluids
