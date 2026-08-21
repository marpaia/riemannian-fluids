import RiemannianFluids.Analysis.EuclideanEllipticRegularity
import RiemannianFluids.FunctionSpaces.HyperbolicCutoffs
import RiemannianFluids.FunctionSpaces.HyperbolicScalarElliptic

/-!
# Local regularity for weak shifted-harmonic scalars on the hyperbolic plane

This module closes the local analytic part of the complete-manifold density argument.  A scalar
in the weak kernel of `δd + 2` is localized in the upper-half-plane chart, interpreted as an
actual Euclidean `L²` function, and shown to belong to Euclidean `H¹`.  The proof identifies its
localized distributional Laplacian with an actual compactly supported `L²` potential and then
applies the Euclidean elliptic-regularity engine.

An outer compact cutoff is chosen from the concrete proper hyperbolic exhaustion, so the final
statement applies to every compact smooth localization without exposing an auxiliary hypothesis.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Complex Filter Function MeasureTheory Set TemperedDistribution
open scoped ContDiff ENat ENNReal Laplacian NNReal SchwartzMap

noncomputable def schwartzRealPart (phi : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (phi.postcompCLM (𝕜 := ℝ) Complex.reCLM).postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

noncomputable def schwartzImagPart (phi : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (phi.postcompCLM (𝕜 := ℝ) Complex.imCLM).postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

@[simp] theorem schwartzRealPart_apply (phi : SchwartzMap ℂ ℂ) (z : ℂ) :
    schwartzRealPart phi z = Complex.ofReal (phi z).re := rfl

@[simp] theorem schwartzImagPart_apply (phi : SchwartzMap ℂ ℂ) (z : ℂ) :
    schwartzImagPart phi z = Complex.ofReal (phi z).im := rfl

theorem schwartz_re_add_I_im (phi : SchwartzMap ℂ ℂ) :
    schwartzRealPart phi + Complex.I • schwartzImagPart phi = phi := by
  ext z
  apply Complex.ext <;> simp [schwartzRealPart, schwartzImagPart]

/-- Complex-valued ambient realization of a real compact hyperbolic core scalar. -/
noncomputable def ambientComplexCore
    (chi : HyperbolicSmoothCompactScalar) : ℂ → ℂ :=
  fun z ↦ Complex.ofReal (ambientExtendZero chi.toFun z)

theorem ambientComplexCore_contDiff
    (chi : HyperbolicSmoothCompactScalar) :
    ContDiff ℝ ∞ (ambientComplexCore chi) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_ambientExtendZero chi)

theorem ambientComplexCore_hasCompactSupport
    (chi : HyperbolicSmoothCompactScalar) :
    HasCompactSupport (ambientComplexCore chi) := by
  exact (hasCompactSupport_ambientExtendZero chi).comp_left rfl

noncomputable def schwartzProductCoreRe
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ) :
    HyperbolicSmoothCompactScalar :=
  ⟨fun p ↦ chi p * (phi (p : ℂ)).re,
    chi.contMDiff_toFun.mul
      ((Complex.reCLM.contDiff.comp (phi.smooth ⊤)).comp_contMDiff contMDiff_coe),
    chi.hasCompactSupport_toFun.mul_right⟩

noncomputable def schwartzProductCoreIm
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ) :
    HyperbolicSmoothCompactScalar :=
  ⟨fun p ↦ chi p * (phi (p : ℂ)).im,
    chi.contMDiff_toFun.mul
      ((Complex.imCLM.contDiff.comp (phi.smooth ⊤)).comp_contMDiff contMDiff_coe),
    chi.hasCompactSupport_toFun.mul_right⟩

@[simp] theorem schwartzProductCoreRe_apply
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ)
    (p : HyperbolicPlane) :
    schwartzProductCoreRe chi phi p = chi p * (phi (p : ℂ)).re := rfl

@[simp] theorem schwartzProductCoreIm_apply
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ)
    (p : HyperbolicPlane) :
    schwartzProductCoreIm chi phi p = chi p * (phi (p : ℂ)).im := rfl

theorem ambient_schwartzProductCore_re
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ) :
    ambientExtendZero (schwartzProductCoreRe chi phi).toFun =
      fun z ↦ (ambientComplexCore chi z * phi z).re := by
  funext z
  by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
  · rcases hz with ⟨p, rfl⟩
    rw [ambientExtendZero_coe]
    change chi p * (phi (p : ℂ)).re = _
    simp [ambientComplexCore]
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz,
      ambientComplexCore, Pi.zero_apply, Complex.ofReal_zero, zero_mul, zero_re]

theorem ambient_schwartzProductCore_im
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ) :
    ambientExtendZero (schwartzProductCoreIm chi phi).toFun =
      fun z ↦ (ambientComplexCore chi z * phi z).im := by
  funext z
  by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
  · rcases hz with ⟨p, rfl⟩
    rw [ambientExtendZero_coe]
    change chi p * (phi (p : ℂ)).im = _
    simp [ambientComplexCore]
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz,
      ambientComplexCore, Pi.zero_apply, Complex.ofReal_zero, zero_mul, zero_im]

theorem laplacian_ambient_schwartzProductCore_re
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ) (z : ℂ) :
    Δ (ambientExtendZero (schwartzProductCoreRe chi phi).toFun) z =
      (Δ (fun w ↦ ambientComplexCore chi w * phi w) z).re := by
  rw [ambient_schwartzProductCore_re]
  have hsmooth : ContDiff ℝ ∞
      (fun w ↦ ambientComplexCore chi w * phi w) :=
    (ambientComplexCore_contDiff chi).mul (phi.smooth ⊤)
  have htwo_le : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  have hsmoothAt : ContDiffAt ℝ 2
      (fun w ↦ ambientComplexCore chi w * phi w) z :=
    (hsmooth.of_le htwo_le).contDiffAt
  have h := hsmoothAt.laplacian_CLM_comp_left (l := Complex.reCLM)
  simpa [Function.comp_def] using h

theorem laplacian_ambient_schwartzProductCore_im
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ) (z : ℂ) :
    Δ (ambientExtendZero (schwartzProductCoreIm chi phi).toFun) z =
      (Δ (fun w ↦ ambientComplexCore chi w * phi w) z).im := by
  rw [ambient_schwartzProductCore_im]
  have hsmooth : ContDiff ℝ ∞
      (fun w ↦ ambientComplexCore chi w * phi w) :=
    (ambientComplexCore_contDiff chi).mul (phi.smooth ⊤)
  have htwo_le : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  have hsmoothAt : ContDiffAt ℝ 2
      (fun w ↦ ambientComplexCore chi w * phi w) z :=
    (hsmooth.of_le htwo_le).contDiffAt
  have h := hsmoothAt.laplacian_CLM_comp_left (l := Complex.imCLM)
  simpa [Function.comp_def] using h

/-- Weak kernel of the positive shifted scalar Hodge core. -/
def IsWeakScalarShiftedHarmonic (h : HyperbolicScalarL2) : Prop :=
  ∀ f : HyperbolicSmoothCompactScalar,
    inner ℝ h (hyperbolicScalarShiftedHodgeCoreL2 f) = 0

noncomputable def weakShiftedSchwartzIntegrand
    (h : HyperbolicScalarL2) (chi : HyperbolicSmoothCompactScalar)
    (phi : SchwartzMap ℂ ℂ) : ℂ → ℂ :=
  ambientExtendZero (fun p ↦
    Complex.ofReal (h p) *
      (-Δ (fun w ↦ ambientComplexCore chi w * phi w) (p : ℂ) +
        Complex.ofReal (2 * (p.im ^ 2)⁻¹) *
          (Complex.ofReal (chi p) * phi (p : ℂ))))

theorem integral_weakShiftedSchwartzIntegrand_eq_zero
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ)
    (hint : Integrable (weakShiftedSchwartzIntegrand h chi phi) volume) :
    (∫ z, weakShiftedSchwartzIntegrand h chi phi z ∂volume) = 0 := by
  apply Complex.ext
  · rw [zero_re]
    change RCLike.re (∫ z, weakShiftedSchwartzIntegrand h chi phi z ∂volume) = 0
    rw [← integral_re hint]
    calc
      (∫ z, (weakShiftedSchwartzIntegrand h chi phi z).re ∂volume) =
          ∫ z, ambientExtendZero (fun p ↦
            h p * (-Δ (ambientExtendZero
                (schwartzProductCoreRe chi phi).toFun) (p : ℂ) +
              2 * (p.im ^ 2)⁻¹ * schwartzProductCoreRe chi phi p)) z
            ∂volume := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
        · rcases hz with ⟨p, rfl⟩
          simp only [weakShiftedSchwartzIntegrand, ambientExtendZero_coe,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            neg_re, add_re, mul_re]
          rw [laplacian_ambient_schwartzProductCore_re]
          simp only [ambientComplexCore, schwartzProductCoreRe_apply]
        · simp only [weakShiftedSchwartzIntegrand, ambientExtendZero,
            Function.extend_apply' _ _ _ hz, Pi.zero_apply, Complex.zero_re]
      _ = inner ℝ h
          (hyperbolicScalarShiftedHodgeCoreL2
            (schwartzProductCoreRe chi phi)) :=
        (inner_hyperbolicScalarShiftedHodgeCoreL2_eq_euclideanIntegral h
          (schwartzProductCoreRe chi phi)).symm
      _ = 0 := hh _
  · rw [zero_im]
    change RCLike.im (∫ z, weakShiftedSchwartzIntegrand h chi phi z ∂volume) = 0
    rw [← integral_im hint]
    calc
      (∫ z, (weakShiftedSchwartzIntegrand h chi phi z).im ∂volume) =
          ∫ z, ambientExtendZero (fun p ↦
            h p * (-Δ (ambientExtendZero
                (schwartzProductCoreIm chi phi).toFun) (p : ℂ) +
              2 * (p.im ^ 2)⁻¹ * schwartzProductCoreIm chi phi p)) z
            ∂volume := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
        · rcases hz with ⟨p, rfl⟩
          simp only [weakShiftedSchwartzIntegrand, ambientExtendZero_coe,
            Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            neg_im, add_im, mul_im]
          rw [laplacian_ambient_schwartzProductCore_im]
          simp only [ambientComplexCore, schwartzProductCoreIm_apply]
        · simp only [weakShiftedSchwartzIntegrand, ambientExtendZero,
            Function.extend_apply' _ _ _ hz, Pi.zero_apply, Complex.zero_im]
      _ = inner ℝ h
          (hyperbolicScalarShiftedHodgeCoreL2
            (schwartzProductCoreIm chi phi)) :=
        (inner_hyperbolicScalarShiftedHodgeCoreL2_eq_euclideanIntegral h
          (schwartzProductCoreIm chi phi)).symm
      _ = 0 := hh _

noncomputable def shiftedPotentialCore
    (chi : HyperbolicSmoothCompactScalar) : HyperbolicSmoothCompactScalar :=
  (2 : ℝ) • densityWeightedCore chi

@[simp] theorem shiftedPotentialCore_apply
    (chi : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    shiftedPotentialCore chi p = 2 * (p.im ^ 2)⁻¹ * chi p := by
  change 2 * ((p.im ^ 2)⁻¹ * chi p) = _
  ring

theorem ambientComplexCore_eventuallyEq_zero_of_not_mem_tsupport
    (chi : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane)
    (hp : p ∉ tsupport chi.toFun) :
    ambientComplexCore chi =ᶠ[nhds (p : ℂ)] 0 := by
  have hambientNot : (p : ℂ) ∉ tsupport (ambientExtendZero chi.toFun) := by
    intro hambient
    have himage :=
      chi.hasCompactSupport_toFun.tsupport_extend_zero_subset
        UpperHalfPlane.continuous_coe hambient
    rcases himage with ⟨q, hq, hqp⟩
    have : q = p := UpperHalfPlane.coe_injective hqp
    exact hp (this ▸ hq)
  have hzero := notMem_tsupport_iff_eventuallyEq.mp hambientNot
  filter_upwards [hzero] with z hz
  simp [ambientComplexCore, hz]

theorem laplacian_ambientComplexCore_mul_schwartz_eq_zero_of_not_mem_tsupport
    (chi : HyperbolicSmoothCompactScalar) (phi : SchwartzMap ℂ ℂ)
    (p : HyperbolicPlane) (hp : p ∉ tsupport chi.toFun) :
    Δ (fun z ↦ ambientComplexCore chi z * phi z) (p : ℂ) = 0 := by
  have hgzero :=
    ambientComplexCore_eventuallyEq_zero_of_not_mem_tsupport chi p hp
  have hproduct :
      (fun z ↦ ambientComplexCore chi z * phi z) =ᶠ[nhds (p : ℂ)]
        (0 : ℂ → ℂ) := by
    filter_upwards [hgzero] with z hz
    simp [hz]
  have hlaplacian := InnerProductSpace.laplacian_congr_nhds hproduct
  have hat := hlaplacian.self_of_nhds
  rw [hat]
  change Δ (fun _ : ℂ ↦ (0 : ℂ)) (p : ℂ) = 0
  rw [InnerProductSpace.laplacian_const]
  rfl

theorem localized_laplacian_eq_potential
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi rho : HyperbolicSmoothCompactScalar)
    (hone : ∀ p ∈ tsupport chi.toFun, rho p = 1) :
    TemperedDistribution.smulLeftCLM ℂ (ambientComplexCore chi)
        (Δ (ambientLocalizedScalarL2 rho h : TemperedDistribution ℂ ℂ)) =
      (ambientLocalizedScalarL2 (shiftedPotentialCore chi) h :
        TemperedDistribution ℂ ℂ) := by
  let g : ℂ → ℂ := ambientComplexCore chi
  let U : Lp ℂ 2 (volume : Measure ℂ) := ambientLocalizedScalarL2 rho h
  let V : Lp ℂ 2 (volume : Measure ℂ) :=
    ambientLocalizedScalarL2 (shiftedPotentialCore chi) h
  have hgCompact : HasCompactSupport g := ambientComplexCore_hasCompactSupport chi
  have hgSmooth : ContDiff ℝ ∞ g := ambientComplexCore_contDiff chi
  have hg : g.HasTemperateGrowth := hgCompact.hasTemperateGrowth hgSmooth
  ext phi
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.laplacian_apply_apply]
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply]
  let psi : SchwartzMap ℂ ℂ := SchwartzMap.smulLeftCLM ℂ g phi
  change (∫ z, (Δ psi) z • U z ∂volume) = ∫ z, phi z • V z ∂volume
  have hleft : Integrable (fun z ↦ (Δ psi) z * U z) volume :=
    ((Δ psi).memLp 2 volume).integrable_mul (Lp.memLp U)
  have hright : Integrable (fun z ↦ phi z * V z) volume :=
    (phi.memLp 2 volume).integrable_mul (Lp.memLp V)
  simp only [smul_eq_mul]
  rw [← sub_eq_zero]
  rw [← integral_sub hleft hright]
  have hUae : (U : ℂ → ℂ) =ᵐ[volume]
      ambientExtendZero (fun p ↦ Complex.ofReal (rho p * h p)) :=
    ambientLocalizedScalarL2_ae rho h
  have hVae : (V : ℂ → ℂ) =ᵐ[volume]
      ambientExtendZero (fun p ↦
        Complex.ofReal (shiftedPotentialCore chi p * h p)) :=
    ambientLocalizedScalarL2_ae (shiftedPotentialCore chi) h
  have hpointwise :
      (fun z ↦ (Δ psi) z * U z - phi z * V z) =ᵐ[volume]
        fun z ↦ -weakShiftedSchwartzIntegrand h chi phi z := by
    filter_upwards [hUae, hVae] with z hUz hVz
    rw [hUz, hVz]
    by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
    · rcases hz with ⟨p, rfl⟩
      simp only [ambientExtendZero_coe]
      have hpsiClassical :
          (Δ psi) (p : ℂ) =
            Δ (fun w ↦ ambientComplexCore chi w * phi w) (p : ℂ) := by
        have hpsi : (⇑psi : ℂ → ℂ) =
            fun w ↦ ambientComplexCore chi w * phi w := by
          funext w
          simp [psi, g, hg]
        rw [SchwartzMap.laplacian_apply, hpsi]
      rw [hpsiClassical]
      by_cases hp : p ∈ tsupport chi.toFun
      · rw [hone p hp]
        simp only [shiftedPotentialCore_apply,
          weakShiftedSchwartzIntegrand, ambientExtendZero_coe]
        simp [ambientComplexCore]
        ring
      · have hlap :=
          laplacian_ambientComplexCore_mul_schwartz_eq_zero_of_not_mem_tsupport
            chi phi p hp
        have hchi : chi p = 0 := by
          apply notMem_support.mp
          intro hs
          exact hp (subset_closure hs)
        change chi.toFun p = 0 at hchi
        have hpotential : shiftedPotentialCore chi p = 0 := by
          rw [shiftedPotentialCore_apply]
          simp [hchi]
        rw [hlap, hpotential]
        simp [weakShiftedSchwartzIntegrand, hlap, hchi]
    · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz, Pi.zero_apply,
        weakShiftedSchwartzIntegrand, mul_zero, sub_zero, neg_zero]
  rw [integral_congr_ae hpointwise]
  rw [integral_neg]
  have hweakInt : Integrable (weakShiftedSchwartzIntegrand h chi phi) volume := by
    have hsub : Integrable (fun z ↦ (Δ psi) z * U z - phi z * V z) volume :=
      hleft.sub hright
    have hnegWeak : Integrable
        (fun z ↦ -weakShiftedSchwartzIntegrand h chi phi z) volume :=
      hsub.congr hpointwise
    apply hnegWeak.neg.congr
    filter_upwards with z
    simp
  rw [integral_weakShiftedSchwartzIntegrand_eq_zero h hh chi phi hweakInt]
  simp

/-- If an outer cutoff is one on the support of an inner cutoff, multiplying the outer ambient
`L²` representative by the inner cutoff recovers exactly the inner ambient representative. -/
theorem smulLeft_ambientLocalizedScalarL2_eq_of_outerCutoff
    (chi rho : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2)
    (hone : ∀ p ∈ tsupport chi.toFun, rho p = 1) :
    TemperedDistribution.smulLeftCLM ℂ (ambientComplexCore chi)
        (ambientLocalizedScalarL2 rho h : TemperedDistribution ℂ ℂ) =
      (ambientLocalizedScalarL2 chi h : TemperedDistribution ℂ ℂ) := by
  let g : ℂ → ℂ := ambientComplexCore chi
  have hgCompact : HasCompactSupport g := ambientComplexCore_hasCompactSupport chi
  have hgSmooth : ContDiff ℝ ∞ g := ambientComplexCore_contDiff chi
  have hg : g.HasTemperateGrowth := hgCompact.hasTemperateGrowth hgSmooth
  have hgLp : MemLp g ∞ (volume : Measure ℂ) :=
    hgSmooth.continuous.memLp_top_of_hasCompactSupport hgCompact volume
  rw [← Lp.toTemperedDistribution_smul_eq (p := ∞) (q := 2) (r := 2)
    hg hgLp (ambientLocalizedScalarL2 rho h)]
  have hlp : (hgLp.toLp g) • ambientLocalizedScalarL2 rho h =
      ambientLocalizedScalarL2 chi h := by
    rw [Lp.ext_iff]
    filter_upwards [
        Lp.coeFn_lpSMul (r := 2) (hgLp.toLp g) (ambientLocalizedScalarL2 rho h),
        hgLp.coeFn_toLp,
        ambientLocalizedScalarL2_ae rho h,
        ambientLocalizedScalarL2_ae chi h] with z hproduct hgValue hrho hchi
    rw [hproduct]
    change (hgLp.toLp g z) * (ambientLocalizedScalarL2 rho h z) =
      ambientLocalizedScalarL2 chi h z
    rw [hgValue, hrho, hchi]
    by_cases hz : ∃ p : HyperbolicPlane, (p : ℂ) = z
    · rcases hz with ⟨p, rfl⟩
      simp only [g, ambientComplexCore, ambientExtendZero_coe]
      change Complex.ofReal (chi.toFun p) *
          Complex.ofReal (rho.toFun p * h p) =
        Complex.ofReal (chi.toFun p * h p)
      by_cases hp : p ∈ tsupport chi.toFun
      · have hrhop : rho.toFun p = 1 := hone p hp
        rw [hrhop]
        simp [Complex.ofReal_mul]
      · have hchip : chi.toFun p = 0 := by
          apply notMem_support.mp
          intro hs
          exact hp (subset_closure hs)
        rw [hchip]
        simp
    · simp only [g, ambientComplexCore, ambientExtendZero,
        Function.extend_apply' _ _ _ hz, Pi.zero_apply, Complex.ofReal_zero, mul_zero]
  exact congrArg (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2) hlp

/-- A weak shifted-harmonic scalar is Euclidean `H¹` after multiplication by any compact
hyperbolic core cutoff.  The auxiliary cutoff only chooses an actual ambient `L²`
representative on a neighborhood of the requested localization. -/
theorem localized_memSobolev_one
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi rho : HyperbolicSmoothCompactScalar)
    (hone : ∀ p ∈ tsupport chi.toFun, rho p = 1) :
    (TemperedDistribution.smulLeftCLM ℂ (ambientComplexCore chi)
      (ambientLocalizedScalarL2 rho h : TemperedDistribution ℂ ℂ)).MemSobolev 1 2 := by
  apply RiemannianFluids.EuclideanEllipticRegularity.localized_memSobolev_one_of_laplacian
    (ambientComplexCore_hasCompactSupport chi)
    (ambientComplexCore_contDiff chi)
  rw [localized_laplacian_eq_potential h hh chi rho hone]
  exact (RiemannianFluids.EuclideanEllipticRegularity.lp_toTemperedDistribution_memSobolev_zero
    (ambientLocalizedScalarL2 (shiftedPotentialCore chi) h)).mono (by norm_num)

/-- Every compactly localized ambient representative of a weak shifted-harmonic scalar belongs
to Euclidean `H¹`. -/
theorem ambientLocalizedScalarL2_memSobolev_one
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi rho : HyperbolicSmoothCompactScalar)
    (hone : ∀ p ∈ tsupport chi.toFun, rho p = 1) :
    (ambientLocalizedScalarL2 chi h : TemperedDistribution ℂ ℂ).MemSobolev 1 2 := by
  rw [← smulLeft_ambientLocalizedScalarL2_eq_of_outerCutoff chi rho h hone]
  exact localized_memSobolev_one h hh chi rho hone

/-- Every compact hyperbolic core has a larger compact cutoff that is identically one on its
topological support. -/
theorem exists_outerCutoff_eq_one
    (chi : HyperbolicSmoothCompactScalar) :
    ∃ rho : HyperbolicSmoothCompactScalar,
      ∀ p ∈ tsupport chi.toFun, rho p = 1 := by
  have hcontinuous : Continuous hyperbolicExhaustion :=
    contMDiff_hyperbolicExhaustion.continuous
  obtain ⟨R₀, hR₀⟩ := bddAbove_def.mp
    (chi.hasCompactSupport_toFun.bddAbove_image hcontinuous.continuousOn)
  let R : ℝ := max 1 R₀
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left 1 R₀)
  refine ⟨hyperbolicCutoffCore R hR, ?_⟩
  intro p hp
  rw [hyperbolicCutoffCore_apply]
  apply hyperbolicCutoff_eq_one_of_exhaustion_le R hR p
  exact (hR₀ (hyperbolicExhaustion p) ⟨p, hp, rfl⟩).trans (le_max_right 1 R₀)

/-- The automatically chosen outer cutoff may also be required to take values in `[0,1]`. -/
theorem exists_bounded_outerCutoff_eq_one
    (chi : HyperbolicSmoothCompactScalar) :
    ∃ rho : HyperbolicSmoothCompactScalar,
      (∀ p ∈ tsupport chi.toFun, rho p = 1) ∧
      (∀ p, 0 ≤ rho p ∧ rho p ≤ 1) := by
  have hcontinuous : Continuous hyperbolicExhaustion :=
    contMDiff_hyperbolicExhaustion.continuous
  obtain ⟨R₀, hR₀⟩ := bddAbove_def.mp
    (chi.hasCompactSupport_toFun.bddAbove_image hcontinuous.continuousOn)
  let R : ℝ := max 1 R₀
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left 1 R₀)
  refine ⟨hyperbolicCutoffCore R hR, ?_, ?_⟩
  · intro p hp
    rw [hyperbolicCutoffCore_apply]
    apply hyperbolicCutoff_eq_one_of_exhaustion_le R hR p
    exact (hR₀ (hyperbolicExhaustion p) ⟨p, hp, rfl⟩).trans (le_max_right 1 R₀)
  · intro p
    rw [hyperbolicCutoffCore_apply]
    exact ⟨hyperbolicCutoff_nonneg R p, hyperbolicCutoff_le_one R p⟩

/-- Final intrinsic local regularity theorem: every compact localization of a weak
shifted-harmonic hyperbolic `L²` scalar is an actual Euclidean `H¹` distribution. -/
theorem ambientLocalizedScalarL2_memSobolev_one_of_weakShiftedHarmonic
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi : HyperbolicSmoothCompactScalar) :
    (ambientLocalizedScalarL2 chi h : TemperedDistribution ℂ ℂ).MemSobolev 1 2 := by
  obtain ⟨rho, hrho⟩ := exists_outerCutoff_eq_one chi
  exact ambientLocalizedScalarL2_memSobolev_one h hh chi rho hrho

/-- Intrinsic local `H¹` regularity statement with the harmless outer representative cutoff
chosen automatically. -/
theorem exists_localized_memSobolev_one
    (h : HyperbolicScalarL2) (hh : IsWeakScalarShiftedHarmonic h)
    (chi : HyperbolicSmoothCompactScalar) :
    ∃ rho : HyperbolicSmoothCompactScalar,
      (TemperedDistribution.smulLeftCLM ℂ (ambientComplexCore chi)
        (ambientLocalizedScalarL2 rho h : TemperedDistribution ℂ ℂ)).MemSobolev 1 2 := by
  obtain ⟨rho, hrho⟩ := exists_outerCutoff_eq_one chi
  exact ⟨rho, localized_memSobolev_one h hh chi rho hrho⟩

end RiemannianFluids.HyperbolicPlane
