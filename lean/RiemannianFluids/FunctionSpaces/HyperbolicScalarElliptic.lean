import Mathlib.Analysis.InnerProductSpace.Laplacian
import RiemannianFluids.FunctionSpaces.HyperbolicL2HodgeDecomposition
import RiemannianFluids.FunctionSpaces.HyperbolicLocalization

/-!
# The scalar hyperbolic Hodge operator in Euclidean coordinates

The complete-manifold step in the CCP25 Hodge decomposition reduces to the positive shifted
scalar operator `delta d + 2`.  This module identifies its second-order part exactly in the
upper-half-plane chart.  For a compact smooth scalar `f`, with `Phi` its smooth extension by zero
to the ambient complex plane,

    delta d f = -y² Delta_E Phi.

The proof differentiates the already-established orthonormal-frame formulas twice, including the
vertical derivative of the inverse-height coefficient.  This is the coefficient-level bridge
between the concrete hyperbolic de Rham core and the Euclidean tempered-distribution regularity
engine.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Complex Filter Function MeasureTheory
open scoped ENNReal Laplacian NNReal

/-- Locally in the upper half-plane, the Euclidean horizontal derivative is the zero extension
of `y⁻¹` times the hyperbolic horizontal derivative. -/
theorem ambient_dx_eventuallyEq_inverseIm_horizontal
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    (fun z ↦ fderiv ℝ (ambientExtendZero f.toFun) z 1) =ᶠ[nhds (p : ℂ)]
      ambientExtendZero (inverseImWeightedCore (horizontalDerivativeCore f)).toFun := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos]
    with z hz
  let q : HyperbolicPlane := ⟨z, hz⟩
  change fderiv ℝ (ambientExtendZero f.toFun) (q : ℂ) 1 =
    ambientExtendZero (inverseImWeightedCore (horizontalDerivativeCore f)).toFun (q : ℂ)
  rw [fderiv_ambientExtendZero_coe_apply_one, ambientExtendZero_coe]
  rfl

/-- Locally in the upper half-plane, the Euclidean vertical derivative is the zero extension of
`y⁻¹` times the hyperbolic vertical derivative. -/
theorem ambient_dy_eventuallyEq_inverseIm_vertical
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    (fun z ↦ fderiv ℝ (ambientExtendZero f.toFun) z Complex.I) =ᶠ[nhds (p : ℂ)]
      ambientExtendZero (inverseImWeightedCore (verticalDerivativeCore f)).toFun := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos]
    with z hz
  let q : HyperbolicPlane := ⟨z, hz⟩
  change fderiv ℝ (ambientExtendZero f.toFun) (q : ℂ) Complex.I =
    ambientExtendZero (inverseImWeightedCore (verticalDerivativeCore f)).toFun (q : ℂ)
  rw [fderiv_ambientExtendZero_coe_apply_I, ambientExtendZero_coe]
  rfl

/-- The ambient second horizontal derivative in terms of two hyperbolic frame derivatives. -/
theorem iteratedFDeriv_ambientExtendZero_one_one
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    iteratedFDeriv ℝ 2 (ambientExtendZero f.toFun) (p : ℂ) ![1, 1] =
      (p.im ^ 2)⁻¹ * horizontalDerivative (horizontalDerivativeCore f).toFun p := by
  rw [iteratedFDeriv_two_apply]
  have hcCont : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ (ambientExtendZero f.toFun)) :=
    (contDiff_infty_iff_fderiv.mp (contDiff_ambientExtendZero f)).2
  have hc : DifferentiableAt ℝ
      (fderiv ℝ (ambientExtendZero f.toFun)) (p : ℂ) :=
    (hcCont.differentiable (by simp)).differentiableAt
  have hclm := fderiv_clm_apply (𝕜 := ℝ)
    (c := fderiv ℝ (ambientExtendZero f.toFun))
    (u := fun _ : ℂ ↦ (1 : ℂ)) (x := (p : ℂ)) hc (by fun_prop)
  have hdirection := DFunLike.congr_fun hclm (1 : ℂ)
  rw [show ![(1 : ℂ), 1] 0 = 1 by simp,
    show ![(1 : ℂ), 1] 1 = 1 by simp]
  have hdirection' :
      fderiv ℝ (fun z ↦ fderiv ℝ (ambientExtendZero f.toFun) z 1)
          (p : ℂ) 1 =
        fderiv ℝ (fderiv ℝ (ambientExtendZero f.toFun)) (p : ℂ) 1 1 := by
    simpa using hdirection
  rw [← hdirection']
  rw [(ambient_dx_eventuallyEq_inverseIm_horizontal f p).fderiv_eq]
  exact fderiv_ambientInverseIm_coe_apply_one (horizontalDerivativeCore f) p

/-- The ambient second vertical derivative, including differentiation of `y⁻¹`. -/
theorem iteratedFDeriv_ambientExtendZero_I_I
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    iteratedFDeriv ℝ 2 (ambientExtendZero f.toFun) (p : ℂ) ![Complex.I, Complex.I] =
      (p.im ^ 2)⁻¹ *
        (verticalDerivative (verticalDerivativeCore f).toFun p -
          verticalDerivative f.toFun p) := by
  rw [iteratedFDeriv_two_apply]
  have hcCont : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ (ambientExtendZero f.toFun)) :=
    (contDiff_infty_iff_fderiv.mp (contDiff_ambientExtendZero f)).2
  have hc : DifferentiableAt ℝ
      (fderiv ℝ (ambientExtendZero f.toFun)) (p : ℂ) :=
    (hcCont.differentiable (by simp)).differentiableAt
  have hclm := fderiv_clm_apply (𝕜 := ℝ)
    (c := fderiv ℝ (ambientExtendZero f.toFun))
    (u := fun _ : ℂ ↦ Complex.I) (x := (p : ℂ)) hc (by fun_prop)
  have hdirection := DFunLike.congr_fun hclm Complex.I
  rw [show ![Complex.I, Complex.I] 0 = Complex.I by simp,
    show ![Complex.I, Complex.I] 1 = Complex.I by simp]
  have hdirection' :
      fderiv ℝ (fun z ↦ fderiv ℝ (ambientExtendZero f.toFun) z Complex.I)
          (p : ℂ) Complex.I =
        fderiv ℝ (fderiv ℝ (ambientExtendZero f.toFun)) (p : ℂ)
          Complex.I Complex.I := by
    simpa using hdirection
  rw [← hdirection']
  rw [(ambient_dy_eventuallyEq_inverseIm_vertical f p).fderiv_eq]
  exact fderiv_ambientInverseIm_coe_apply_I (verticalDerivativeCore f) p

/-- Exact coordinate formula for the scalar Hodge Laplacian on the compact core. -/
theorem oneFormCodifferential_scalarExterior_eq_neg_height_sq_laplacian
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    oneFormCodifferentialCore (scalarExteriorDerivativeCore f) p =
      -p.im ^ 2 * Δ (ambientExtendZero f.toFun) (p : ℂ) := by
  rw [oneFormCodifferentialCore_apply]
  have hzero :
      (fun q ↦ scalarExteriorDerivativeCore f q 0) =
        (horizontalDerivativeCore f).toFun := by
    funext q
    exact scalarExteriorDerivativeCore_apply_zero f q
  have hone :
      (fun q ↦ scalarExteriorDerivativeCore f q 1) =
        (verticalDerivativeCore f).toFun := by
    funext q
    exact scalarExteriorDerivativeCore_apply_one f q
  rw [hzero, hone, scalarExteriorDerivativeCore_apply_one]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  change -horizontalDerivative (horizontalDerivativeCore f).toFun p +
      verticalDerivative f.toFun p - verticalDerivative (verticalDerivativeCore f).toFun p =
    -p.im ^ 2 *
      (iteratedFDeriv ℝ 2 (ambientExtendZero f.toFun) (p : ℂ) ![1, 1] +
        iteratedFDeriv ℝ 2 (ambientExtendZero f.toFun) (p : ℂ)
          ![Complex.I, Complex.I])
  rw [iteratedFDeriv_ambientExtendZero_one_one,
    iteratedFDeriv_ambientExtendZero_I_I]
  field_simp [im_ne_zero p]
  ring

/-! ## Shifted scalar core and its weak Euclidean form -/

/-- The compact scalar representative of the CCP25 operator `delta d + 2`. -/
noncomputable def scalarShiftedHodgeCore :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  oneFormCodifferentialCore.comp scalarExteriorDerivativeCore +
    (2 : ℝ) • LinearMap.id

@[simp] theorem scalarShiftedHodgeCore_apply
    (f : HyperbolicSmoothCompactScalar) :
    scalarShiftedHodgeCore f =
      oneFormCodifferentialCore (scalarExteriorDerivativeCore f) + (2 : ℝ) • f := by
  simp [scalarShiftedHodgeCore]

/-- The existing shifted `L²` operator is exactly the inclusion of the compact representative. -/
theorem hyperbolicScalarShiftedHodgeCoreL2_eq_toL2
    (f : HyperbolicSmoothCompactScalar) :
    hyperbolicScalarShiftedHodgeCoreL2 f = (scalarShiftedHodgeCore f).toL2 := by
  rw [hyperbolicScalarShiftedHodgeCoreL2_apply]
  change (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2)
        (oneFormCodifferentialCore (scalarExteriorDerivativeCore f)) +
      (2 : ℝ) •
        (hyperbolicSmoothCompactToL2 :
          HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2) f =
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2)
        (scalarShiftedHodgeCore f)
  rw [scalarShiftedHodgeCore_apply, map_add, map_smul]

/-- Pointwise coordinate expression for the complete shifted core operator. -/
@[simp] theorem scalarShiftedHodgeCore_apply_point
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    scalarShiftedHodgeCore f p =
      -p.im ^ 2 * Δ (ambientExtendZero f.toFun) (p : ℂ) + 2 * f p := by
  rw [scalarShiftedHodgeCore_apply]
  change oneFormCodifferentialCore (scalarExteriorDerivativeCore f) p + 2 * f p = _
  rw [oneFormCodifferential_scalarExterior_eq_neg_height_sq_laplacian]

/-- Pairing the shifted hyperbolic core with an arbitrary hyperbolic `L²` scalar is precisely the
Euclidean weak pairing for `-Δ + 2 y⁻²` on the upper half-plane. -/
theorem inner_hyperbolicScalarShiftedHodgeCoreL2_eq_euclideanIntegral
    (h : HyperbolicScalarL2) (f : HyperbolicSmoothCompactScalar) :
    inner ℝ h (hyperbolicScalarShiftedHodgeCoreL2 f) =
      ∫ z, ambientExtendZero (fun p ↦
        h p * (-Δ (ambientExtendZero f.toFun) (p : ℂ) +
          2 * (p.im ^ 2)⁻¹ * f p)) z ∂MeasureTheory.volume := by
  rw [hyperbolicScalarShiftedHodgeCoreL2_eq_toL2, hyperbolicScalarL2_inner]
  have hcoe := (scalarShiftedHodgeCore f).toL2_coe
  have hintegral :
      (∫ p, h p * (scalarShiftedHodgeCore f).toL2 p ∂hyperbolicVolume) =
        ∫ p, h p * scalarShiftedHodgeCore f p ∂hyperbolicVolume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hcoe] with p hp
    rw [hp]
    rfl
  rw [hintegral]
  let density : HyperbolicPlane → ℝ≥0 := fun p ↦
    (1 / NNReal.mk p.im p.im_pos.le) ^ 2
  have hdensity : Measurable density := by
    rw [← measurable_coe_nnreal_real_iff]
    simpa only [density, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk,
      Pi.div_apply, Pi.one_apply] using
      (((contMDiff_im (n := 0)).continuous.measurable.const_div 1).pow_const 2)
  change (∫ p, h p * scalarShiftedHodgeCore f p
      ∂(MeasureTheory.volume.comap ((↑) : HyperbolicPlane → ℂ)).withDensity
        (fun p ↦ (density p : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul hdensity]
  rw [integral_comap_eq_integral_ambientExtendZero_general]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
  · rcases hz with ⟨p, rfl⟩
    simp only [ambientExtendZero_coe]
    rw [scalarShiftedHodgeCore_apply_point]
    dsimp [density]
    change (1 / p.im) ^ 2 *
        (h p * (-p.im ^ 2 * Δ (ambientExtendZero f.toFun) (p : ℂ) + 2 * f p)) =
      h p * (-Δ (ambientExtendZero f.toFun) (p : ℂ) +
        2 * (p.im ^ 2)⁻¹ * f p)
    field_simp [im_ne_zero p]
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz]

end RiemannianFluids.HyperbolicPlane
