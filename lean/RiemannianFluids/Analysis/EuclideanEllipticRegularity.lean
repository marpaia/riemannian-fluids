import Mathlib.Analysis.Distribution.Sobolev
import RiemannianFluids.Analysis.DistributionalLeibniz

/-!
# Euclidean elliptic regularity for tempered distributions

The complete-manifold Hodge argument ultimately localizes weak elliptic equations to Euclidean
coordinate patches.  This file records the constant-coefficient part of that bridge using
Mathlib's Fourier-defined Bessel potentials and Sobolev spaces.

With Mathlib's Fourier normalization, the order-two Bessel potential is

    J^2 u = u - (2 * pi)^(-2) Delta u.

Consequently, if both `u` and its distributional Laplacian have local `H^s` regularity, then `u`
has `H^(s+2)` regularity.  Variable-coefficient localization and multiplier commutators are kept
separate: this theorem is the reusable Euclidean engine they consume.
-/

noncomputable section

namespace RiemannianFluids.EuclideanEllipticRegularity

open FourierTransform TemperedDistribution ENNReal MeasureTheory LineDeriv
open scoped ContDiff ENat SchwartzMap Laplacian LineDeriv

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Under Mathlib's Fourier normalization, the order-two Bessel potential is the identity minus
`(2 * pi)^(-2)` times the distributional Laplacian. -/
theorem besselPotential_two_eq_sub_laplacian
    (u : TemperedDistribution E F) :
    besselPotential E F 2 u =
      u - (((2 * Real.pi) ^ 2 : ℝ)⁻¹ : ℂ) • Δ u := by
  rw [laplacian_eq_fourierMultiplierCLM]
  rw [← Complex.coe_smul (-(2 * Real.pi) ^ 2), smul_smul]
  have hcoefficient :
      (((((2 * Real.pi) ^ 2 : ℝ) : ℂ))⁻¹ *
        ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ)) = -1 := by
    push_cast
    field_simp
  have hleft : Function.LeftInverse
      (FourierTransform.fourierInv :
        TemperedDistribution E F → TemperedDistribution E F)
      (FourierTransform.fourier :
        TemperedDistribution E F → TemperedDistribution E F) :=
    fun x ↦ FourierTransform.fourierInv_fourier_eq x
  rw [hcoefficient, neg_one_smul, sub_neg_eq_add]
  rw [besselPotential]
  apply hleft.injective
  simp only [fourierMultiplierCLM_apply,
    FourierTransform.fourier_add,
    FourierTransform.fourier_fourierInv_eq]
  have hsymbol :
      (fun x : E ↦ Complex.ofReal
        ((1 + ‖x‖ ^ 2) ^ (2 / 2 : ℝ))) =
        (fun _ : E ↦ (1 : ℂ)) +
          (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)) := by
    funext x
    norm_num
  rw [hsymbol, smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp only [add_apply, smulLeftCLM_const, one_smul]

variable [CompleteSpace F]

/-- Constant-coefficient elliptic gain for tempered distributions: Sobolev control of a
distribution and its Laplacian at order `s` gives two additional derivatives. -/
theorem memSobolev_add_two_of_laplacian
    {s : ℝ} {u : TemperedDistribution E F}
    (hu : u.MemSobolev s 2) (hlaplacian : (Δ u).MemSobolev s 2) :
    u.MemSobolev (s + 2) 2 := by
  have hbessel : (besselPotential E F 2 u).MemSobolev s 2 := by
    rw [besselPotential_two_eq_sub_laplacian]
    exact hu.sub (hlaplacian.smul
      ((((2 * Real.pi) ^ 2 : ℝ)⁻¹ : ℂ)))
  have hgain :=
    (memSobolev_besselPotential_iff (s := s) (r := (2 : ℝ)) (f := u)).1 hbessel
  simpa [add_comm] using hgain

/-- An actual Euclidean `L²` function, viewed as a tempered distribution, has Sobolev order
zero. -/
theorem lp_toTemperedDistribution_memSobolev_zero
    (u : Lp F 2 (volume : Measure E)) :
    (u : TemperedDistribution E F).MemSobolev 0 2 := by
  rw [memSobolev_zero_iff]
  exact ⟨u, rfl⟩

/-- Multiplying an `L²` function by an `L∞` temperate-growth coefficient remains Sobolev order
zero, stated directly for the corresponding product of tempered distributions. -/
theorem smulLeftCLM_lp_memSobolev_zero
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hgLp : MemLp g ∞ (volume : Measure E))
    (u : Lp F 2 (volume : Measure E)) :
    (TemperedDistribution.smulLeftCLM F g
      (u : TemperedDistribution E F)).MemSobolev 0 2 := by
  rw [memSobolev_zero_iff]
  refine ⟨(hgLp.toLp _) • u, ?_⟩
  exact (Lp.toTemperedDistribution_smul_eq hg hgLp u).symm

/-- Compact smooth localization preserves Euclidean `L²`, expressed as Sobolev order zero for
the localized tempered distribution. -/
theorem smulLeftCLM_lp_memSobolev_zero_of_compactSupport
    {g : E → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (u : Lp F 2 (volume : Measure E)) :
    (TemperedDistribution.smulLeftCLM F g
      (u : TemperedDistribution E F)).MemSobolev 0 2 := by
  apply smulLeftCLM_lp_memSobolev_zero (hgc.hasTemperateGrowth hg)
  exact hg.continuous.memLp_top_of_hasCompactSupport hgc volume

variable {F₂ : Type*}
  [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]

/-- The first local elliptic gain in the scale consumed by the complete-manifold argument: an
`L²` distribution whose Laplacian is `H⁻¹` belongs to `H¹`. -/
theorem memSobolev_one_of_laplacian_memSobolev_neg_one
    {u : TemperedDistribution E F₂}
    (hu : u.MemSobolev 0 2) (hlaplacian : (Δ u).MemSobolev (-1) 2) :
    u.MemSobolev 1 2 := by
  have huNeg : u.MemSobolev (-1) 2 :=
    TemperedDistribution.MemSobolev.mono (E := E) (F := F₂)
      (by norm_num : (-1 : ℝ) ≤ 0) hu
  have hgain := memSobolev_add_two_of_laplacian
    (s := (-1 : ℝ)) huNeg hlaplacian
  norm_num at hgain ⊢
  exact hgain

/-- Sobolev membership is stable under a finite sum of tempered distributions. -/
theorem memSobolev_finset_sum
    {sOrder : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {I : Type*} (S : Finset I) (u : I → TemperedDistribution E F₂)
    (hu : ∀ i ∈ S, (u i).MemSobolev sOrder p) :
    (∑ i ∈ S, u i).MemSobolev sOrder p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact (hu a (by simp)).add (ih (fun i hi ↦ hu i (by simp [hi])))

/-- Local `L² → H¹` regularity in the exact divergence-form interface used after multiplying a
weak equation by a compact cutoff.  It is enough to know that the cutoff multiple of the original
distributional Laplacian is `H⁻¹`; the proved commutator formula supplies all remaining terms. -/
theorem localized_memSobolev_one_of_laplacian
    {g : E → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (u : Lp F₂ 2 (volume : Measure E))
    (hlocalizedLaplacian :
      (TemperedDistribution.smulLeftCLM F₂ g
        (Δ (u : TemperedDistribution E F₂))).MemSobolev (-1) 2) :
    (TemperedDistribution.smulLeftCLM F₂ g
      (u : TemperedDistribution E F₂)).MemSobolev 1 2 := by
  let basis := stdOrthonormalBasis ℝ E
  let U : TemperedDistribution E F₂ := u
  let correction : Fin (Module.finrank ℝ E) → TemperedDistribution E F₂ :=
    fun i ↦
      (2 : ℂ) • ∂_{basis i}
          (TemperedDistribution.smulLeftCLM F₂
            (fun x ↦ fderiv ℝ g x (basis i)) U) -
        TemperedDistribution.smulLeftCLM F₂
          (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ g y (basis i)) x (basis i)) U
  have hcorrection : ∀ i, (correction i).MemSobolev (-1) 2 := by
    intro i
    have hfirstCompact : HasCompactSupport (fun x ↦ fderiv ℝ g x (basis i)) :=
      hgc.fderiv_apply ℝ (basis i)
    have hfirstSmooth : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ g x (basis i)) := by
      fun_prop
    have hsecondCompact :
        HasCompactSupport
          (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ g y (basis i)) x (basis i)) :=
      hfirstCompact.fderiv_apply ℝ (basis i)
    have hsecondSmooth :
        ContDiff ℝ ∞
          (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ g y (basis i)) x (basis i)) := by
      fun_prop
    have hfirstZero := smulLeftCLM_lp_memSobolev_zero_of_compactSupport
      hfirstCompact hfirstSmooth u
    have hfirstDerivative :
        (∂_{basis i} (TemperedDistribution.smulLeftCLM F₂
          (fun x ↦ fderiv ℝ g x (basis i)) U)).MemSobolev (-1) 2 := by
      simpa using hfirstZero.lineDerivOp
    have hsecondZero := smulLeftCLM_lp_memSobolev_zero_of_compactSupport
      hsecondCompact hsecondSmooth u
    have hsecondNeg :
        (TemperedDistribution.smulLeftCLM F₂
          (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ g y (basis i)) x (basis i)) U).MemSobolev
            (-1) 2 :=
      hsecondZero.mono (by norm_num)
    exact (hfirstDerivative.smul (2 : ℂ)).sub hsecondNeg
  have hsum : (∑ i, correction i).MemSobolev (-1) 2 :=
    memSobolev_finset_sum Finset.univ correction (fun i _ ↦ hcorrection i)
  have hlaplacian :
      (Δ (TemperedDistribution.smulLeftCLM F₂ g U)).MemSobolev (-1) 2 := by
    rw [DistributionalLeibniz.tempered_laplacian_smulLeft_of_compactSupport hgc hg]
    exact hlocalizedLaplacian.add hsum
  apply memSobolev_one_of_laplacian_memSobolev_neg_one
  · exact smulLeftCLM_lp_memSobolev_zero_of_compactSupport hgc hg u
  · exact hlaplacian

end RiemannianFluids.EuclideanEllipticRegularity
