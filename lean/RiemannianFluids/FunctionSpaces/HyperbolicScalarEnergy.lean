import RiemannianFluids.Analysis.EuclideanWeakEnergy
import RiemannianFluids.FunctionSpaces.HyperbolicScalarRegularity

/-!
# Shifted scalar energy on the complete hyperbolic plane

This module closes the scalar analytic input needed for the concrete CCP25 Hodge
decomposition.  Compact hyperbolic tests are transported to ambient Schwartz functions,
localized weak solutions satisfy an exact energy identity, and the canonical outer-cutoff
exhaustion forces every weak solution of `(delta d + 2) h = 0` in `L2` to vanish.  The final
result is dense range of the compact shifted Hodge core in the complete measured hyperbolic
scalar `L2` carrier.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Complex Function MeasureTheory Set TemperedDistribution
open scoped ENNReal Laplacian LineDeriv NNReal RealInnerProductSpace SchwartzMap

/-- A compact hyperbolic scalar, extended by zero, as an ambient Schwartz function. -/
noncomputable def ambientComplexCoreSchwartz
    (chi : HyperbolicSmoothCompactScalar) : SchwartzMap ℂ ℂ :=
  (ambientComplexCore_hasCompactSupport chi).toSchwartzMap
    (ambientComplexCore_contDiff chi)

@[simp] theorem ambientComplexCoreSchwartz_apply
    (chi : HyperbolicSmoothCompactScalar) (z : ℂ) :
    ambientComplexCoreSchwartz chi z = ambientComplexCore chi z :=
  rfl

theorem ambientComplexCoreSchwartz_isReal
    (chi : HyperbolicSmoothCompactScalar) :
    RiemannianFluids.EuclideanSobolev.IsRealSchwartz
      (ambientComplexCoreSchwartz chi) := by
  intro z
  simp [ambientComplexCoreSchwartz_apply, ambientComplexCore]

theorem ambientComplexCoreSchwartz_scalarProduct
    (chi rho : HyperbolicSmoothCompactScalar) :
    ambientComplexCoreSchwartz (scalarProductCore chi rho) =
      RiemannianFluids.EuclideanSobolev.schwartzProduct
        (ambientComplexCoreSchwartz chi) (ambientComplexCoreSchwartz rho) := by
  ext z
  simp only [ambientComplexCoreSchwartz_apply,
    RiemannianFluids.EuclideanSobolev.schwartzProduct_apply]
  by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
  · rcases hz with ⟨p, rfl⟩
    simp only [ambientComplexCore, ambientExtendZero_coe]
    norm_cast
  · simp [ambientComplexCore, ambientExtendZero, Function.extend_apply' _ _ _ hz]

theorem inner_ambientLocalizedScalarL2
    (chi rho : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    inner ℝ (ambientLocalizedScalarL2 chi h) (ambientLocalizedScalarL2 rho h) =
      ∫ p, (chi p * h p) * (rho p * h p)
        ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) := by
  rw [L2.inner_def]
  calc
    (∫ z, inner ℝ (ambientLocalizedScalarL2 chi h z)
        (ambientLocalizedScalarL2 rho h z) ∂volume) =
        ∫ z, ambientExtendZero
          (fun p ↦ (chi p * h p) * (rho p * h p)) z ∂volume := by
      apply integral_congr_ae
      filter_upwards [ambientLocalizedScalarL2_ae chi h,
        ambientLocalizedScalarL2_ae rho h] with z hchi hrho
      rw [hchi, hrho]
      by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
      · rcases hz with ⟨p, rfl⟩
        rw [Complex.inner]
        simp only [ambientExtendZero_coe, map_mul, Complex.conj_ofReal,
          Complex.ofReal_mul]
        norm_cast
        ring
      · simp [ambientExtendZero, Function.extend_apply' _ _ _ hz]
    _ = ∫ p, (chi p * h p) * (rho p * h p)
        ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) :=
      (integral_comap_eq_integral_ambientExtendZero_general _).symm

private noncomputable def chartDensity : HyperbolicPlane → ℝ≥0 :=
  fun p ↦ (1 / NNReal.mk p.im p.im_pos.le) ^ 2

private theorem measurable_chartDensity : Measurable chartDensity := by
  rw [← measurable_coe_nnreal_real_iff]
  simpa only [chartDensity, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_mk, Pi.div_apply, Pi.one_apply] using
    (((contMDiff_im (n := 0)).continuous.measurable.const_div 1).pow_const 2)

private theorem integral_hyperbolic_eq_chart (f : HyperbolicPlane → ℝ) :
    (∫ p, f p ∂hyperbolicVolume) =
      ∫ p, (chartDensity p : ℝ) * f p
        ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) := by
  rw [hyperbolicVolume_def]
  change (∫ p, f p ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)).withDensity
      (fun p ↦ (chartDensity p : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul measurable_chartDensity]
  simp only [NNReal.smul_def, smul_eq_mul]

/-- The potential term in the localized weak identity is exactly the intrinsic weighted
`L²` mass inside the cutoff. -/
theorem inner_ambientLocalized_shifted_square
    (kappa rho : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2)
    (hone : ∀ p ∈ tsupport (scalarProductCore kappa kappa).toFun, rho p = 1) :
    inner ℝ (ambientLocalizedScalarL2 rho h)
        (ambientLocalizedScalarL2
          (shiftedPotentialCore (scalarProductCore kappa kappa)) h) =
      ∫ p, 2 * (kappa p * h p) ^ 2 ∂hyperbolicVolume := by
  rw [inner_ambientLocalizedScalarL2]
  rw [integral_hyperbolic_eq_chart]
  apply integral_congr_ae
  filter_upwards with p
  simp only [shiftedPotentialCore_apply, scalarProductCore_apply]
  dsimp [chartDensity]
  by_cases hkappa : kappa p = 0
  · rw [show kappa.toFun p = 0 from hkappa]
    ring
  · have hpSupport : p ∈ support (scalarProductCore kappa kappa).toFun := by
      change kappa.toFun p * kappa.toFun p ≠ 0
      exact mul_ne_zero hkappa hkappa
    have hpTSupport : p ∈ tsupport (scalarProductCore kappa kappa).toFun :=
      subset_closure hpSupport
    have hrho := hone p hpTSupport
    change rho.toFun p = 1 at hrho
    rw [hrho]
    field_simp [im_ne_zero p]

/-- Euclidean multiplication by a coefficient of the form `y⁻¹ a` has exactly the
intrinsic hyperbolic `L²` norm of multiplication by `a`. -/
theorem norm_sq_schwartzLpMultiplier_frameCoefficient
    (g : SchwartzMap ℂ ℂ) (a : HyperbolicPlane → ℝ)
    (hg : ∀ p : HyperbolicPlane,
      g (p : ℂ) = Complex.ofReal ((p.im)⁻¹ * a p))
    (rho : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
        (E := ℂ) g (ambientLocalizedScalarL2 rho h)‖ ^ 2 =
      ∫ p, (a p * (rho p * h p)) ^ 2 ∂hyperbolicVolume := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [integral_hyperbolic_eq_chart]
  calc
    (∫ z, inner ℝ
        (RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
          (E := ℂ) g (ambientLocalizedScalarL2 rho h) z)
        (RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
          (E := ℂ) g (ambientLocalizedScalarL2 rho h) z) ∂volume) =
        ∫ z, ambientExtendZero (fun p ↦
          ((p.im)⁻¹ * a p * (rho p * h p)) ^ 2) z ∂volume := by
      apply integral_congr_ae
      filter_upwards
        [RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier_coeFn
          (E := ℂ) g (ambientLocalizedScalarL2 rho h),
         ambientLocalizedScalarL2_ae rho h] with z hmult hlocalized
      rw [hmult, hlocalized]
      by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
      · rcases hz with ⟨p, rfl⟩
        rw [ambientExtendZero_coe, ambientExtendZero_coe, hg]
        rw [Complex.inner]
        simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
        norm_cast
        ring
      · simp [ambientExtendZero, Function.extend_apply' _ _ _ hz]
    _ = ∫ p, ((p.im)⁻¹ * a p * (rho p * h p)) ^ 2
        ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) :=
      (integral_comap_eq_integral_ambientExtendZero_general _).symm
    _ = ∫ p, (chartDensity p : ℝ) *
          (a p * (rho p * h p)) ^ 2
        ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp [chartDensity]
      change (p.im⁻¹ * a p * (rho p * h p)) ^ 2 =
        (1 / p.im) ^ 2 * (a p * (rho p * h p)) ^ 2
      ring

theorem lineDeriv_ambientComplexCoreSchwartz_one
    (kappa : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    (∂_{(1 : ℂ)} (ambientComplexCoreSchwartz kappa)) (p : ℂ) =
      Complex.ofReal ((p.im)⁻¹ * horizontalDerivative kappa.toFun p) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (ambientComplexCore kappa) (p : ℂ) 1 = _
  have hsource : DifferentiableAt ℝ (ambientExtendZero kappa.toFun) (p : ℂ) :=
    (contDiff_ambientExtendZero kappa).differentiable (by simp) |>.differentiableAt
  have hcomp := Complex.ofRealCLM.hasFDerivAt.comp (p : ℂ) hsource.hasFDerivAt
  have hf := hcomp.fderiv
  change fderiv ℝ (ambientComplexCore kappa) (p : ℂ) =
    Complex.ofRealCLM.comp
      (fderiv ℝ (ambientExtendZero kappa.toFun) (p : ℂ)) at hf
  rw [hf, ContinuousLinearMap.comp_apply,
    fderiv_ambientExtendZero_coe_apply_one]
  rfl

theorem lineDeriv_ambientComplexCoreSchwartz_I
    (kappa : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    (∂_{Complex.I} (ambientComplexCoreSchwartz kappa)) (p : ℂ) =
      Complex.ofReal ((p.im)⁻¹ * verticalDerivative kappa.toFun p) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (ambientComplexCore kappa) (p : ℂ) Complex.I = _
  have hsource : DifferentiableAt ℝ (ambientExtendZero kappa.toFun) (p : ℂ) :=
    (contDiff_ambientExtendZero kappa).differentiable (by simp) |>.differentiableAt
  have hcomp := Complex.ofRealCLM.hasFDerivAt.comp (p : ℂ) hsource.hasFDerivAt
  have hf := hcomp.fderiv
  change fderiv ℝ (ambientComplexCore kappa) (p : ℂ) =
    Complex.ofRealCLM.comp
      (fderiv ℝ (ambientExtendZero kappa.toFun) (p : ℂ)) at hf
  rw [hf, ContinuousLinearMap.comp_apply,
    fderiv_ambientExtendZero_coe_apply_I]
  rfl

/-- A bounded compact coefficient, multiplied by an outer cutoff valued in `[0,1]`, has the
expected intrinsic `L²` estimate. -/
theorem integral_sq_core_mul_localized_le
    (a rho : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ p, |a p| ≤ C)
    (hrho : ∀ p, 0 ≤ rho p ∧ rho p ≤ 1) :
    (∫ p, (a p * (rho p * h p)) ^ 2 ∂hyperbolicVolume) ≤
      C ^ 2 * ‖h‖ ^ 2 := by
  let coefficient : HyperbolicPlane → ℝ := fun p ↦ a p * rho p
  have hcoefficientContinuous : Continuous coefficient :=
    a.contMDiff_toFun.continuous.mul rho.contMDiff_toFun.continuous
  have hcoefficientCompact : HasCompactSupport coefficient :=
    a.hasCompactSupport_toFun.mul_right
  have hcoefficientLp : MemLp coefficient ∞ hyperbolicVolume :=
    hcoefficientContinuous.memLp_top_of_hasCompactSupport
      hcoefficientCompact hyperbolicVolume
  have hproductLp : MemLp (fun p ↦ coefficient p * h p) 2 hyperbolicVolume :=
    (Lp.memLp h).mul' hcoefficientLp
  have hleftIntegrable :
      Integrable (fun p ↦ (a p * (rho p * h p)) ^ 2) hyperbolicVolume := by
    convert hproductLp.integrable_sq using 1
    funext p
    dsimp [coefficient]
    ring
  have hrightIntegrable :
      Integrable (fun p ↦ C ^ 2 * (h p) ^ 2) hyperbolicVolume :=
    (Lp.memLp h).integrable_sq.const_mul (C ^ 2)
  have hpointwise : ∀ p,
      (a p * (rho p * h p)) ^ 2 ≤ C ^ 2 * (h p) ^ 2 := by
    intro p
    have hrhoAbs : |rho p| ≤ 1 := by
      rw [abs_of_nonneg (hrho p).1]
      exact (hrho p).2
    have hcoefficientAbs : |a p * rho p| ≤ C := by
      rw [abs_mul]
      calc
        |a p| * |rho p| ≤ C * 1 :=
          mul_le_mul (ha p) hrhoAbs (abs_nonneg _) hC
        _ = C := mul_one C
    have hsquare : (a p * rho p) ^ 2 ≤ C ^ 2 := by
      nlinarith only [sq_abs (a p * rho p), sq_abs C,
        abs_nonneg (a p * rho p), abs_of_nonneg hC, hcoefficientAbs]
    calc
      (a p * (rho p * h p)) ^ 2 =
          (a p * rho p) ^ 2 * (h p) ^ 2 := by ring
      _ ≤ C ^ 2 * (h p) ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg (h p))
  calc
    (∫ p, (a p * (rho p * h p)) ^ 2 ∂hyperbolicVolume) ≤
        ∫ p, C ^ 2 * (h p) ^ 2 ∂hyperbolicVolume :=
      integral_mono_ae hleftIntegrable hrightIntegrable
        (Filter.Eventually.of_forall hpointwise)
    _ = C ^ 2 * (∫ p, h p * h p ∂hyperbolicVolume) := by
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = C ^ 2 * ‖h‖ ^ 2 := by
      rw [← hyperbolicScalarL2_inner, real_inner_self_eq_norm_sq]

/-- Both Euclidean derivative multipliers generated by the radius-`R` cutoff are controlled by
the intrinsic hyperbolic norm with the uniform `O(R⁻¹)` cutoff-gradient bound. -/
theorem hyperbolicCutoff_multiplier_energy_bound
    (R : ℝ) (hR : 0 < R) (rho : HyperbolicSmoothCompactScalar)
    (hrho : ∀ p, 0 ≤ rho p ∧ rho p ≤ 1) (h : HyperbolicScalarL2) :
    ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
        (E := ℂ)
        (∂_{(1 : ℂ)} (ambientComplexCoreSchwartz
          (hyperbolicCutoffCore R hR)))
        (ambientLocalizedScalarL2 rho h)‖ ^ 2 +
      ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
        (E := ℂ)
        (∂_{Complex.I} (ambientComplexCoreSchwartz
          (hyperbolicCutoffCore R hR)))
        (ambientLocalizedScalarL2 rho h)‖ ^ 2 ≤
      2 * (hyperbolicRadialBumpDerivativeBound / R) ^ 2 * ‖h‖ ^ 2 := by
  let kappa := hyperbolicCutoffCore R hR
  let C := hyperbolicRadialBumpDerivativeBound / R
  have hC : 0 ≤ C :=
    div_nonneg hyperbolicRadialBumpDerivativeBound_nonneg hR.le
  have hxEq :
      ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
          (E := ℂ) (∂_{(1 : ℂ)} (ambientComplexCoreSchwartz kappa))
          (ambientLocalizedScalarL2 rho h)‖ ^ 2 =
        ∫ p, (horizontalDerivative kappa.toFun p * (rho p * h p)) ^ 2
          ∂hyperbolicVolume :=
    norm_sq_schwartzLpMultiplier_frameCoefficient
      (∂_{(1 : ℂ)} (ambientComplexCoreSchwartz kappa))
      (horizontalDerivative kappa.toFun)
      (lineDeriv_ambientComplexCoreSchwartz_one kappa) rho h
  have hyEq :
      ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
          (E := ℂ) (∂_{Complex.I} (ambientComplexCoreSchwartz kappa))
          (ambientLocalizedScalarL2 rho h)‖ ^ 2 =
        ∫ p, (verticalDerivative kappa.toFun p * (rho p * h p)) ^ 2
          ∂hyperbolicVolume :=
    norm_sq_schwartzLpMultiplier_frameCoefficient
      (∂_{Complex.I} (ambientComplexCoreSchwartz kappa))
      (verticalDerivative kappa.toFun)
      (lineDeriv_ambientComplexCoreSchwartz_I kappa) rho h
  have hxBound :
      (∫ p, (horizontalDerivative kappa.toFun p * (rho p * h p)) ^ 2
          ∂hyperbolicVolume) ≤ C ^ 2 * ‖h‖ ^ 2 := by
    have hb := integral_sq_core_mul_localized_le
      (horizontalDerivativeCore kappa) rho h C hC
      (fun p ↦ abs_horizontalDerivative_hyperbolicCutoff_le R hR p) hrho
    change (∫ p, (horizontalDerivative kappa.toFun p * (rho p * h p)) ^ 2
      ∂hyperbolicVolume) ≤ C ^ 2 * ‖h‖ ^ 2 at hb
    exact hb
  have hyBound :
      (∫ p, (verticalDerivative kappa.toFun p * (rho p * h p)) ^ 2
          ∂hyperbolicVolume) ≤ C ^ 2 * ‖h‖ ^ 2 := by
    have hb := integral_sq_core_mul_localized_le
      (verticalDerivativeCore kappa) rho h C hC
      (fun p ↦ abs_verticalDerivative_hyperbolicCutoff_le R hR p) hrho
    change (∫ p, (verticalDerivative kappa.toFun p * (rho p * h p)) ^ 2
      ∂hyperbolicVolume) ≤ C ^ 2 * ‖h‖ ^ 2 at hb
    exact hb
  rw [hxEq, hyEq]
  calc
    (∫ p, (horizontalDerivative kappa.toFun p * (rho p * h p)) ^ 2
        ∂hyperbolicVolume) +
        ∫ p, (verticalDerivative kappa.toFun p * (rho p * h p)) ^ 2
          ∂hyperbolicVolume ≤
      C ^ 2 * ‖h‖ ^ 2 + C ^ 2 * ‖h‖ ^ 2 := add_le_add hxBound hyBound
    _ = 2 * (hyperbolicRadialBumpDerivativeBound / R) ^ 2 * ‖h‖ ^ 2 := by
      dsimp [C]
      ring

/-- The local distributional shifted equation tested by its actual Euclidean `H¹`
representative. -/
theorem exists_hyperbolic_localized_weak_energy_identity
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi rho : HyperbolicSmoothCompactScalar)
    (hone : ∀ p ∈ tsupport chi.toFun, rho p = 1) :
    ∃ u : Lp ℂ 2 (volume : Measure ℂ),
      RiemannianFluids.EuclideanSobolev.sobolevOneBase (E := ℂ) u =
          ambientLocalizedScalarL2 rho h ∧
        let x := RiemannianFluids.EuclideanSobolev.sobolevOneTripleRecovery
          (E := ℂ) 1 Complex.I u
        let gx := RiemannianFluids.EuclideanSobolev.sobolevOneTripleMultiplier
          (E := ℂ) 1 Complex.I (ambientComplexCoreSchwartz chi) x
        inner ℝ gx.2.1 x.2.1 + inner ℝ gx.2.2 x.2.2 +
          inner ℝ x.1 (ambientLocalizedScalarL2 (shiftedPotentialCore chi) h) = 0 := by
  have hregular :=
    ambientLocalizedScalarL2_memSobolev_one_of_weakShiftedHarmonic h hh rho
  obtain ⟨u, hbase, _⟩ :=
    RiemannianFluids.EuclideanSobolev.exists_sobolevOneCoordinate
      (ambientLocalizedScalarL2 rho h) hregular
  refine ⟨u, hbase, ?_⟩
  have henergy := RiemannianFluids.EuclideanSobolev.localized_weak_energy_identity
    (E := ℂ) Complex.orthonormalBasisOneI (ambientComplexCoreSchwartz chi)
      (ambientComplexCoreSchwartz_isReal chi) u (ambientLocalizedScalarL2 rho h)
      (ambientLocalizedScalarL2 (shiftedPotentialCore chi) h) hbase ?_
  · simpa [Complex.coe_orthonormalBasisOneI] using henergy
  · simpa [ambientComplexCoreSchwartz_apply] using
      localized_laplacian_eq_potential h hh chi rho hone

/-- Hyperbolic Caccioppoli estimate for the square of any compact smooth real cutoff. -/
theorem hyperbolic_localized_square_energy_bound
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (kappa rho : HyperbolicSmoothCompactScalar)
    (hone : ∀ p ∈ tsupport (scalarProductCore kappa kappa).toFun, rho p = 1) :
    inner ℝ (ambientLocalizedScalarL2 rho h)
        (ambientLocalizedScalarL2
          (shiftedPotentialCore (scalarProductCore kappa kappa)) h) ≤
      ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
          (E := ℂ) (∂_{(1 : ℂ)} (ambientComplexCoreSchwartz kappa))
          (ambientLocalizedScalarL2 rho h)‖ ^ 2 +
        ‖RiemannianFluids.EuclideanSobolev.schwartzLpMultiplier
          (E := ℂ) (∂_{Complex.I} (ambientComplexCoreSchwartz kappa))
          (ambientLocalizedScalarL2 rho h)‖ ^ 2 := by
  have hregular :=
    ambientLocalizedScalarL2_memSobolev_one_of_weakShiftedHarmonic h hh rho
  obtain ⟨u, hbase, _⟩ :=
    RiemannianFluids.EuclideanSobolev.exists_sobolevOneCoordinate
      (ambientLocalizedScalarL2 rho h) hregular
  let q := ambientComplexCoreSchwartz kappa
  have hbound := RiemannianFluids.EuclideanSobolev.localized_square_energy_bound
    (E := ℂ) Complex.orthonormalBasisOneI q
      (ambientComplexCoreSchwartz_isReal kappa) u
      (ambientLocalizedScalarL2 rho h)
      (ambientLocalizedScalarL2
        (shiftedPotentialCore (scalarProductCore kappa kappa)) h)
      hbase ?_
  · simpa [q, Complex.coe_orthonormalBasisOneI] using hbound
  · rw [← ambientComplexCoreSchwartz_scalarProduct]
    simpa [ambientComplexCoreSchwartz_apply] using
      localized_laplacian_eq_potential h hh
        (scalarProductCore kappa kappa) rho hone

/-- Quantitative cutoff estimate for a weak shifted-harmonic scalar on the complete
hyperbolic plane. -/
theorem hyperbolicCutoff_mass_bound
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (R : ℝ) (hR : 0 < R) :
    (∫ p, 2 * (hyperbolicCutoffCore R hR p * h p) ^ 2
        ∂hyperbolicVolume) ≤
      2 * (hyperbolicRadialBumpDerivativeBound / R) ^ 2 * ‖h‖ ^ 2 := by
  let kappa := hyperbolicCutoffCore R hR
  obtain ⟨rho, hone, hrho⟩ :=
    exists_bounded_outerCutoff_eq_one (scalarProductCore kappa kappa)
  have henergy := hyperbolic_localized_square_energy_bound h hh kappa rho hone
  rw [inner_ambientLocalized_shifted_square kappa rho h hone] at henergy
  have hgradient := hyperbolicCutoff_multiplier_energy_bound R hR rho hrho h
  change (∫ p, 2 * (kappa p * h p) ^ 2 ∂hyperbolicVolume) ≤ _
  exact henergy.trans hgradient

/-- The cutoff-localized masses converge to the full intrinsic mass. -/
theorem tendsto_hyperbolicCutoff_mass
    (h : HyperbolicScalarL2) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ p,
        2 * (hyperbolicCutoffCoreSequence n p * h p) ^ 2
          ∂hyperbolicVolume)
      Filter.atTop
      (nhds (∫ p, 2 * (h p) ^ 2 ∂hyperbolicVolume)) := by
  apply tendsto_integral_of_dominated_convergence
      (fun p ↦ 2 * (h p) ^ 2)
  · intro n
    have hcutoff : StronglyMeasurable
        (fun p ↦ hyperbolicCutoffCoreSequence n p) :=
      (hyperbolicCutoffCoreSequence n).contMDiff_toFun.continuous.stronglyMeasurable
    have hproduct : AEStronglyMeasurable
        (fun p ↦ hyperbolicCutoffCoreSequence n p * h p)
        hyperbolicVolume :=
      hcutoff.aestronglyMeasurable.mul (Lp.memLp h).1
    exact ((hproduct.aemeasurable.pow_const 2).const_mul 2).aestronglyMeasurable
  · exact (Lp.memLp h).integrable_sq.const_mul 2
  · intro n
    filter_upwards with p
    have hkNonneg : 0 ≤ hyperbolicCutoffCoreSequence n p := by
      rw [hyperbolicCutoffCoreSequence_apply]
      exact hyperbolicCutoff_nonneg ((n : ℝ) + 1) p
    have hkLe : hyperbolicCutoffCoreSequence n p ≤ 1 := by
      rw [hyperbolicCutoffCoreSequence_apply]
      exact hyperbolicCutoff_le_one ((n : ℝ) + 1) p
    have hkSq : (hyperbolicCutoffCoreSequence n p) ^ 2 ≤ 1 := by
      nlinarith only [hkNonneg, hkLe]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 2 * (hyperbolicCutoffCoreSequence n p * h p) ^ 2)]
    calc
      2 * (hyperbolicCutoffCoreSequence n p * h p) ^ 2 =
          2 * (hyperbolicCutoffCoreSequence n p) ^ 2 * (h p) ^ 2 := by ring
      _ ≤ 2 * 1 * (h p) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkSq (by positivity)) (sq_nonneg (h p))
      _ = 2 * (h p) ^ 2 := by ring
  · filter_upwards with p
    apply Filter.EventuallyEq.tendsto
    filter_upwards [eventually_hyperbolicCutoffCoreSequence_eq_one p] with n hn
    rw [hn]
    ring

/-- The weak `L²` kernel of the positive shifted scalar Hodge core is trivial.  This is the
complete-manifold cutoff argument behind the scalar density input to CCP25 Proposition 4.3. -/
theorem weakScalarShiftedHarmonic_eq_zero
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h) : h = 0 := by
  let mass : ℕ → ℝ := fun n ↦ ∫ p,
    2 * (hyperbolicCutoffCoreSequence n p * h p) ^ 2 ∂hyperbolicVolume
  let error : ℕ → ℝ := fun n ↦
    2 * (hyperbolicRadialBumpDerivativeBound / ((n : ℝ) + 1)) ^ 2 * ‖h‖ ^ 2
  have hmass : Filter.Tendsto mass Filter.atTop
      (nhds (∫ p, 2 * (h p) ^ 2 ∂hyperbolicVolume)) := by
    exact tendsto_hyperbolicCutoff_mass h
  have herror : Filter.Tendsto error Filter.atTop (nhds 0) := by
    have hsquare := tendsto_hyperbolicCutoffDerivativeBound.pow 2
    have hscaled := (hsquare.const_mul 2).mul
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ ‖h‖ ^ 2) Filter.atTop (nhds (‖h‖ ^ 2)))
    simpa only [error, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using hscaled
  have hbound : ∀ n, mass n ≤ error n := by
    intro n
    exact hyperbolicCutoff_mass_bound h hh ((n : ℝ) + 1) (by positivity)
  have hmassLe : (∫ p, 2 * (h p) ^ 2 ∂hyperbolicVolume) ≤ 0 :=
    le_of_tendsto_of_tendsto hmass herror
      (Filter.Eventually.of_forall hbound)
  have hmassNonneg : 0 ≤ ∫ p, 2 * (h p) ^ 2 ∂hyperbolicVolume :=
    integral_nonneg fun p ↦ by positivity
  have hmassNorm : (∫ p, 2 * (h p) ^ 2 ∂hyperbolicVolume) =
      2 * ‖h‖ ^ 2 := by
    rw [integral_const_mul]
    congr 1
    calc
      (∫ p, (h p) ^ 2 ∂hyperbolicVolume) =
          ∫ p, h p * h p ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = inner ℝ h h := (hyperbolicScalarL2_inner h h).symm
      _ = ‖h‖ ^ 2 := real_inner_self_eq_norm_sq h
  have hnormSq : ‖h‖ ^ 2 = 0 := by
    rw [hmassNorm] at hmassLe hmassNonneg
    nlinarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- The complete shifted scalar core has dense range in the concrete hyperbolic scalar
`L²` space. -/
theorem hyperbolicScalarShiftedHodgeCoreL2_denseRange :
    DenseRange hyperbolicScalarShiftedHodgeCoreL2 := by
  let K : Submodule ℝ HyperbolicScalarL2 :=
    LinearMap.range hyperbolicScalarShiftedHodgeCoreL2
  have horthogonal : K.orthogonal = ⊥ := by
    apply (Submodule.eq_bot_iff K.orthogonal).2
    intro h hh
    apply weakScalarShiftedHarmonic_eq_zero h
    intro f
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal K h).1 hh
      (hyperbolicScalarShiftedHodgeCoreL2 f) ⟨f, rfl⟩
  have hclosure : K.topologicalClosure = ⊤ := by
    have hdouble := K.orthogonal_orthogonal_eq_closure
    rw [horthogonal, Submodule.bot_orthogonal_eq_top] at hdouble
    exact hdouble.symm
  have hdenseK : Dense (K : Set HyperbolicScalarL2) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 hclosure
  change Dense (Set.range hyperbolicScalarShiftedHodgeCoreL2)
  convert hdenseK using 1
  ext h
  simp [K, LinearMap.mem_range]


end RiemannianFluids.HyperbolicPlane
