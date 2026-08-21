import RiemannianFluids.FunctionSpaces.HyperbolicIntegrationByParts

/-!
# Euclidean localization of hyperbolic `L²` functions

The complete-hyperbolic elliptic argument is local in the upper-half-plane chart, while the
ambient Sobolev machinery is formulated on the Euclidean plane.  This module supplies the exact
measure bridge between those two settings.

The hyperbolic density is `y⁻² dx dy`.  Thus, after multiplication by a compact smooth cutoff
`chi`, a hyperbolic `L²` scalar becomes Euclidean `L²`: write `chi h = y⁻¹ (y chi) h`, use
boundedness of the compactly supported coefficient `y chi` in hyperbolic measure, and cancel the
density.  Extension by zero then gives an actual ambient `Lp` carrier suitable for tempered
distribution and local elliptic-regularity arguments.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Complex Function MeasureTheory Set
open scoped ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrating a zero extension over the ambient plane is exactly integration against the
pulled-back Euclidean measure on the upper half-plane.  No regularity assumption on the
integrand is needed. -/
theorem integral_comap_eq_integral_ambientExtendZero_general
    (f : HyperbolicPlane → F) :
    (∫ p, f p ∂(volume.comap ((↑) : HyperbolicPlane → ℂ))) =
      ∫ z, ambientExtendZero f z ∂volume := by
  have hpres : MeasurePreserving ((↑) : HyperbolicPlane → ℂ)
      (volume.comap ((↑) : HyperbolicPlane → ℂ))
      (volume.restrict (Set.range ((↑) : HyperbolicPlane → ℂ))) :=
    ⟨UpperHalfPlane.measurable_coe, by
      rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
  calc
    (∫ p, f p ∂(volume.comap ((↑) : HyperbolicPlane → ℂ))) =
        ∫ p, ambientExtendZero f (p : ℂ)
          ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) := by simp
    _ = ∫ z, ambientExtendZero f z
          ∂(volume.restrict (Set.range ((↑) : HyperbolicPlane → ℂ))) :=
      hpres.integral_comp UpperHalfPlane.measurableEmbedding_coe _
    _ = ∫ z, ambientExtendZero f z ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
        exact Function.extend_apply' _ _ _ hz

/-- An `Lp` function on the upper half-plane with pulled-back Euclidean measure remains `Lp`
after extension by zero to the ambient plane. -/
theorem memLp_ambientExtendZero_of_comap
    {p : ℝ≥0∞} {f : HyperbolicPlane → F}
    (hf : MemLp f p (volume.comap ((↑) : HyperbolicPlane → ℂ))) :
    MemLp (ambientExtendZero f) p volume := by
  let s : Set ℂ := Set.range ((↑) : HyperbolicPlane → ℂ)
  have hs : MeasurableSet s := by
    rw [show s = UpperHalfPlane.upperHalfPlaneSet from UpperHalfPlane.range_coe]
    exact UpperHalfPlane.isOpen_upperHalfPlaneSet.measurableSet
  have hpres : MeasurePreserving ((↑) : HyperbolicPlane → ℂ)
      (volume.comap ((↑) : HyperbolicPlane → ℂ))
      (volume.restrict s) :=
    ⟨UpperHalfPlane.measurable_coe, by
      dsimp [s]
      rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
  have hrestrict : MemLp (ambientExtendZero f) p (volume.restrict s) := by
    rw [← hpres.map_eq]
    rw [UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff]
    have hcomp : ambientExtendZero f ∘ ((↑) : HyperbolicPlane → ℂ) = f := by
      funext x
      exact ambientExtendZero_coe f x
    rw [hcomp]
    exact hf
  have hindicator := (memLp_indicator_iff_restrict hs).2 hrestrict
  have heq : s.indicator (ambientExtendZero f) = ambientExtendZero f := by
    funext z
    by_cases hz : z ∈ s
    · simp [hz]
    · rw [Set.indicator_of_notMem hz]
      change 0 = Function.extend ((↑) : HyperbolicPlane → ℂ) f 0 z
      have hz' : ¬ ∃ q : HyperbolicPlane, (q : ℂ) = z := by
        intro hex
        exact hz hex
      exact (Function.extend_apply' f (0 : ℂ → F) z hz').symm
  rwa [heq] at hindicator

/-- Multiplication by a compact smooth scalar converts a hyperbolic `L²` scalar into an `L²`
function for the pulled-back Euclidean measure. -/
theorem memLp_compact_mul_scalar_comap
    (chi : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    MemLp (fun p ↦ chi p * h p) 2
      (volume.comap ((↑) : HyperbolicPlane → ℂ)) := by
  let hfun : HyperbolicPlane → ℝ := fun p ↦ h p
  have hhLp : MemLp hfun 2 hyperbolicVolume := by
    simpa only [hfun] using Lp.memLp h
  let mu0 : Measure HyperbolicPlane :=
    volume.comap ((↑) : HyperbolicPlane → ℂ)
  let density : HyperbolicPlane → ℝ≥0 := fun p ↦
    (1 / NNReal.mk p.im p.im_pos.le) ^ 2
  have hdensity : Measurable density := by
    rw [← measurable_coe_nnreal_real_iff]
    simpa only [density, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk,
      Pi.div_apply, Pi.one_apply] using
      (((contMDiff_im (n := 0)).continuous.measurable.const_div 1).pow_const 2)
  let coefficient : HyperbolicPlane → ℝ := fun p ↦ p.im * chi p
  have hcoefficientContinuous : Continuous coefficient :=
    (contMDiff_im (n := 0)).continuous.mul chi.contMDiff_toFun.continuous
  have hcoefficientCompact : HasCompactSupport coefficient :=
    chi.hasCompactSupport_toFun.mul_left
  have hcoefficientLp : MemLp coefficient ∞ hyperbolicVolume :=
    hcoefficientContinuous.memLp_top_of_hasCompactSupport hcoefficientCompact hyperbolicVolume
  have hqLp : MemLp (fun p ↦ coefficient p * hfun p) 2 hyperbolicVolume := by
    exact hhLp.mul' hcoefficientLp
  have hqIntegrable :
      Integrable (fun p ↦ (coefficient p * hfun p) ^ 2) hyperbolicVolume :=
    hqLp.integrable_sq
  have hqIntegrableMu0 :
      Integrable (fun p ↦ (density p : ℝ) • (coefficient p * hfun p) ^ 2) mu0 := by
    rw [hyperbolicVolume_def] at hqIntegrable
    exact (integrable_withDensity_iff_integrable_smul hdensity).1 hqIntegrable
  have hintegrable : Integrable (fun p ↦ (chi p * hfun p) ^ 2) mu0 := by
    convert hqIntegrableMu0 using 1
    funext p
    dsimp [density, coefficient]
    change (chi p * hfun p) ^ 2 =
      (1 / p.im) ^ 2 * (p.im * chi p * hfun p) ^ 2
    field_simp [im_ne_zero p]
  have hhMeasHyp : AEStronglyMeasurable hfun hyperbolicVolume := hhLp.1
  have hhMeasWeighted :
      AEStronglyMeasurable (fun p ↦ (density p : ℝ) • hfun p) mu0 := by
    rw [hyperbolicVolume_def] at hhMeasHyp
    exact (aestronglyMeasurable_withDensity_iff hdensity).1 hhMeasHyp
  have hySqMeas : StronglyMeasurable (fun p : HyperbolicPlane ↦ p.im ^ 2) :=
    ((contMDiff_im (n := 0)).continuous.pow 2).stronglyMeasurable
  have hhMeasRaw : AEStronglyMeasurable hfun mu0 := by
    have hscaled := hySqMeas.aestronglyMeasurable.smul hhMeasWeighted
    convert hscaled using 1
    funext p
    dsimp [density]
    field_simp [im_ne_zero p]
  have hlocalizedMeas : AEStronglyMeasurable (fun p ↦ chi p * hfun p) mu0 :=
    chi.contMDiff_toFun.continuous.aestronglyMeasurable.mul hhMeasRaw
  simpa only [hfun, mu0] using
    (memLp_two_iff_integrable_sq hlocalizedMeas).2 hintegrable

/-- A compact localization of a hyperbolic `L²` scalar, extended by zero, is Euclidean `L²`. -/
theorem memLp_ambient_compact_mul_scalar
    (chi : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    MemLp (ambientExtendZero (fun p ↦ chi p * h p)) 2 volume :=
  memLp_ambientExtendZero_of_comap (memLp_compact_mul_scalar_comap chi h)

/-- Complex-valued version used by Fourier-defined tempered distributions. -/
theorem memLp_ambient_compact_mul_scalar_complex
    (chi : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    MemLp (ambientExtendZero (fun p ↦ Complex.ofReal (chi p * h p))) 2 volume := by
  apply memLp_ambientExtendZero_of_comap
  exact (memLp_compact_mul_scalar_comap chi h).ofReal

/-- The actual ambient Euclidean `L²` carrier of a compactly localized hyperbolic scalar. -/
noncomputable def ambientLocalizedScalarL2
    (chi : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_ambient_compact_mul_scalar_complex chi h).toLp
    (ambientExtendZero (fun p ↦ Complex.ofReal (chi p * h p)))

/-- The localized carrier has the expected pointwise representative almost everywhere. -/
theorem ambientLocalizedScalarL2_ae
    (chi : HyperbolicSmoothCompactScalar) (h : HyperbolicScalarL2) :
    (ambientLocalizedScalarL2 chi h : ℂ → ℂ) =ᵐ[volume]
      ambientExtendZero (fun p ↦ Complex.ofReal (chi p * h p)) :=
  (memLp_ambient_compact_mul_scalar_complex chi h).coeFn_toLp

end RiemannianFluids.HyperbolicPlane
