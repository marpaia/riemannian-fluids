import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Distributional Leibniz rules

Complete-manifold cutoff arguments multiply weak solutions by smooth compactly supported
functions.  Mathlib supplies multiplication and directional differentiation on Schwartz functions
and tempered distributions, but does not currently package their compatibility.  This file proves
that compatibility directly from the test-function definition of a distributional derivative.

The compact-support corollary is the interface needed for localization: a smooth compact
multiplier and each of its directional derivatives have temperate growth automatically.
-/

noncomputable section

namespace RiemannianFluids.DistributionalLeibniz

open Function TemperedDistribution
open LineDeriv Laplacian
open scoped ContDiff ENat SchwartzMap Laplacian

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every directional derivative of a smooth compactly supported complex-valued function has
temperate growth. -/
theorem compact_fderiv_apply_hasTemperateGrowth
    {g : E → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g) (m : E) :
    (fun x ↦ fderiv ℝ g x m).HasTemperateGrowth :=
  (hgc.fderiv_apply ℝ m).hasTemperateGrowth (by fun_prop)

/-- Pointwise Leibniz rule, bundled as an equality in Schwartz space. -/
theorem schwartz_lineDeriv_smulLeft
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {m : E}
    (hdg : (fun x ↦ fderiv ℝ g x m).HasTemperateGrowth)
    (f : SchwartzMap E ℂ) :
    ∂_{m} (SchwartzMap.smulLeftCLM ℂ g f) =
      SchwartzMap.smulLeftCLM ℂ g (∂_{m} f) +
        SchwartzMap.smulLeftCLM ℂ (fun x ↦ fderiv ℝ g x m) f := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [show (⇑(SchwartzMap.smulLeftCLM ℂ g f) : E → ℂ) =
    (fun y ↦ g y • f y) from SchwartzMap.smulLeftCLM_apply hg f]
  simp only [add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.smulLeftCLM_apply_apply hdg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [fderiv_fun_smul (hg.1.differentiable (by simp)).differentiableAt f.differentiableAt]
  rfl

/-- Distributional Leibniz rule for multiplication by a smooth temperate-growth function. -/
theorem tempered_lineDeriv_smulLeft
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {m : E}
    (hdg : (fun x ↦ fderiv ℝ g x m).HasTemperateGrowth)
    (u : TemperedDistribution E F) :
    ∂_{m} (TemperedDistribution.smulLeftCLM F g u) =
      TemperedDistribution.smulLeftCLM F g (∂_{m} u) +
        TemperedDistribution.smulLeftCLM F (fun x ↦ fderiv ℝ g x m) u := by
  ext f
  change u (SchwartzMap.smulLeftCLM ℂ g (-∂_{m} f)) =
    u (-∂_{m} (SchwartzMap.smulLeftCLM ℂ g f)) +
      u (SchwartzMap.smulLeftCLM ℂ (fun x ↦ fderiv ℝ g x m) f)
  rw [map_neg, schwartz_lineDeriv_smulLeft hg hdg]
  simp

/-- Distributional Leibniz rule specialized to a smooth compact multiplier. -/
theorem tempered_lineDeriv_smulLeft_of_compactSupport
    {g : E → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (m : E) (u : TemperedDistribution E F) :
    ∂_{m} (TemperedDistribution.smulLeftCLM F g u) =
      TemperedDistribution.smulLeftCLM F g (∂_{m} u) +
        TemperedDistribution.smulLeftCLM F (fun x ↦ fderiv ℝ g x m) u :=
  tempered_lineDeriv_smulLeft (hgc.hasTemperateGrowth hg)
    (compact_fderiv_apply_hasTemperateGrowth hgc hg m) u

/-- A second directional derivative of a localized distribution, arranged so that every
commutator term is either a derivative of a localized `L²` quantity or a zeroth-order localized
quantity.  This form is tailored to the first local Sobolev-gain estimate. -/
theorem tempered_secondLineDeriv_smulLeft_of_compactSupport
    {g : E → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (m : E) (u : TemperedDistribution E F) :
    ∂_{m} (∂_{m} (TemperedDistribution.smulLeftCLM F g u)) =
      TemperedDistribution.smulLeftCLM F g (∂_{m} (∂_{m} u)) +
        (2 : ℂ) • ∂_{m} (TemperedDistribution.smulLeftCLM F
          (fun x ↦ fderiv ℝ g x m) u) -
        TemperedDistribution.smulLeftCLM F
          (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ g y m) x m) u := by
  have hdgc : HasCompactSupport (fun x ↦ fderiv ℝ g x m) :=
    hgc.fderiv_apply ℝ m
  have hdg : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ g x m) := by fun_prop
  rw [tempered_lineDeriv_smulLeft_of_compactSupport hgc hg]
  rw [lineDerivOp_add]
  rw [tempered_lineDeriv_smulLeft_of_compactSupport hgc hg]
  rw [tempered_lineDeriv_smulLeft_of_compactSupport hdgc hdg]
  module

variable {E₂ : Type*}
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-- Laplacian localization formula for a smooth compact multiplier.  The commutator is written in
divergence form, so an `L²` weak solution immediately gives an `H⁻¹` localized Laplacian. -/
theorem tempered_laplacian_smulLeft_of_compactSupport
    {g : E₂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (u : TemperedDistribution E₂ F) :
    Δ (TemperedDistribution.smulLeftCLM F g u) =
      TemperedDistribution.smulLeftCLM F g (Δ u) +
        ∑ i : Fin (Module.finrank ℝ E₂),
          ((2 : ℂ) • ∂_{stdOrthonormalBasis ℝ E₂ i}
              (TemperedDistribution.smulLeftCLM F
                (fun x ↦ fderiv ℝ g x (stdOrthonormalBasis ℝ E₂ i)) u) -
            TemperedDistribution.smulLeftCLM F
              (fun x ↦ fderiv ℝ
                (fun y ↦ fderiv ℝ g y (stdOrthonormalBasis ℝ E₂ i)) x
                  (stdOrthonormalBasis ℝ E₂ i)) u) := by
  rw [TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E₂)]
  rw [TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E₂)]
  simp_rw [tempered_secondLineDeriv_smulLeft_of_compactSupport hgc hg]
  simp [Finset.sum_add_distrib]
  abel

end RiemannianFluids.DistributionalLeibniz
