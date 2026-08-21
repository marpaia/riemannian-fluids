import RiemannianFluids.Analysis.EuclideanEllipticRegularity

/-!
# Concrete Euclidean order-one Sobolev carriers

This module realizes the Bessel-potential definition of `H¹` as an actual `L²`
coordinate space. It continuously recovers the base function and every weak
directional derivative, with equality in tempered distributions.
-/

noncomputable section

namespace RiemannianFluids.EuclideanSobolev

open Complex FourierTransform Function MeasureTheory TemperedDistribution
open scoped ENNReal LineDeriv Real SchwartzMap

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def besselSymbol (s : ℝ) (x : E) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (s / 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem besselSymbol_hasTemperateGrowth (s : ℝ) :
    (besselSymbol (E := E) s).HasTemperateGrowth := by
  exact Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)

noncomputable def schwartzBesselPotential (s : ℝ) :
    SchwartzMap E ℂ →L[ℝ] SchwartzMap E ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (besselSymbol (E := E) s)

theorem schwartzBesselPotential_add (s t : ℝ) (f : SchwartzMap E ℂ) :
    schwartzBesselPotential (E := E) s
        (schwartzBesselPotential (E := E) t f) =
      schwartzBesselPotential (E := E) (s + t) f := by
  change SchwartzMap.fourierMultiplierCLM ℂ (besselSymbol (E := E) s)
      (SchwartzMap.fourierMultiplierCLM ℂ (besselSymbol (E := E) t) f) =
    SchwartzMap.fourierMultiplierCLM ℂ (besselSymbol (E := E) (s + t)) f
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (besselSymbol_hasTemperateGrowth s) (besselSymbol_hasTemperateGrowth t)]
  have hsymbol : besselSymbol (E := E) s * besselSymbol (E := E) t =
      besselSymbol (E := E) (s + t) := by
    funext x
    simp only [besselSymbol, Pi.mul_apply]
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [hsymbol]

theorem besselPotential_schwartz (s : ℝ) (f : SchwartzMap E ℂ) :
    TemperedDistribution.besselPotential E ℂ s
        (f : TemperedDistribution E ℂ) =
      (schwartzBesselPotential (E := E) s f : TemperedDistribution E ℂ) := by
  rw [TemperedDistribution.besselPotential]
  rw [TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (by fun_prop)]
  congr 1
  exact SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2)) f

theorem schwartzBesselPotential_neg_self (s : ℝ) (f : SchwartzMap E ℂ) :
    schwartzBesselPotential (E := E) (-s)
        (schwartzBesselPotential (E := E) s f) = f := by
  rw [schwartzBesselPotential_add]
  have hzero : -s + s = 0 := by ring
  rw [hzero]
  rw [schwartzBesselPotential]
  have hsymbol : besselSymbol (E := E) 0 = fun _ : E ↦ (1 : ℝ) := by
    funext x
    simp [besselSymbol]
  rw [hsymbol]
  simp

noncomputable def schwartzSobolevCore (s : ℝ) :
    SchwartzMap E ℂ →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 volume).comp (schwartzBesselPotential (E := E) s)

theorem schwartzSobolevCore_denseRange (s : ℝ) :
    DenseRange (schwartzSobolevCore (E := E) s) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2
      (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top
  apply Dense.mono _ hdense
  intro u hu
  rcases hu with ⟨f, rfl⟩
  refine ⟨schwartzBesselPotential (E := E) (-s) f, ?_⟩
  simp only [schwartzSobolevCore, ContinuousLinearMap.comp_apply]
  rw [schwartzBesselPotential_add]
  have hzero : s + -s = 0 := by ring
  rw [hzero]
  rw [schwartzBesselPotential]
  have hsymbol : besselSymbol (E := E) 0 = fun _ : E ↦ (1 : ℝ) := by
    funext x
    simp [besselSymbol]
  rw [hsymbol]
  simp

theorem norm_toLp_le_schwartzSobolevCore_one (f : SchwartzMap E ℂ) :
    ‖f.toLp 2 (volume : Measure E)‖ ≤
      ‖schwartzSobolevCore (E := E) 1 f‖ := by
  rw [← Lp.norm_fourier_eq (f.toLp 2 (volume : Measure E)),
    ← Lp.norm_fourier_eq (schwartzSobolevCore (E := E) 1 f)]
  rw [SchwartzMap.toLp_fourier_eq]
  simp only [schwartzSobolevCore, ContinuousLinearMap.comp_apply,
    SchwartzMap.toLpCLM_apply, schwartzBesselPotential,
    SchwartzMap.fourierMultiplierCLM_apply]
  rw [SchwartzMap.toLp_fourier_eq]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(FourierTransform.fourier f).coeFn_toLp 2 volume,
      (FourierTransform.fourier
        (FourierTransform.fourierInv
          (SchwartzMap.smulLeftCLM ℂ (besselSymbol (E := E) 1)
            (FourierTransform.fourier f)))).coeFn_toLp 2 volume] with x hleft hright
  rw [hleft, hright, FourierTransform.fourier_fourierInv_eq]
  simp only [SchwartzMap.smulLeftCLM_apply_apply
    (besselSymbol_hasTemperateGrowth (E := E) 1), norm_smul]
  have hone : 1 ≤ besselSymbol (E := E) 1 x := by
    apply Real.one_le_rpow
    · simp
    · norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact le_mul_of_one_le_left (norm_nonneg _) hone

/-- Continuous recovery of the underlying `L²` function from its order-one Bessel coordinate. -/
noncomputable def sobolevOneBase :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 volume).toLinearMap.extendOfNorm
    (schwartzSobolevCore (E := E) 1).toLinearMap

@[simp] theorem sobolevOneBase_schwartzSobolevCore (f : SchwartzMap E ℂ) :
    sobolevOneBase (E := E) (schwartzSobolevCore (E := E) 1 f) =
      f.toLp 2 (volume : Measure E) := by
  exact LinearMap.extendOfNorm_eq (schwartzSobolevCore_denseRange (E := E) 1)
    ⟨1, fun u ↦ by simpa using norm_toLp_le_schwartzSobolevCore_one (E := E) u⟩ f

theorem sobolevOneBase_toTemperedDistribution
    (u : Lp ℂ 2 (volume : Measure E)) :
    (sobolevOneBase (E := E) u : TemperedDistribution E ℂ) =
      TemperedDistribution.besselPotential E ℂ (-1)
        (u : TemperedDistribution E ℂ) := by
  let lhs : Lp ℂ 2 (volume : Measure E) → TemperedDistribution E ℂ :=
    fun v ↦ (sobolevOneBase (E := E) v : TemperedDistribution E ℂ)
  let rhs : Lp ℂ 2 (volume : Measure E) → TemperedDistribution E ℂ :=
    fun v ↦ TemperedDistribution.besselPotential E ℂ (-1)
      (v : TemperedDistribution E ℂ)
  have hlhs : Continuous lhs :=
    (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous.comp
      (sobolevOneBase (E := E)).continuous
  have hrhs : Continuous rhs :=
    (TemperedDistribution.besselPotential E ℂ (-1)).continuous.comp
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous
  have heq : lhs = rhs :=
    (schwartzSobolevCore_denseRange (E := E) 1).equalizer hlhs hrhs (by
      funext f
      change (sobolevOneBase (E := E) (schwartzSobolevCore (E := E) 1 f) :
          TemperedDistribution E ℂ) =
        TemperedDistribution.besselPotential E ℂ (-1)
          (schwartzSobolevCore (E := E) 1 f : TemperedDistribution E ℂ)
      rw [sobolevOneBase_schwartzSobolevCore]
      rw [Lp.toTemperedDistribution_toLp_eq]
      simp only [schwartzSobolevCore, ContinuousLinearMap.comp_apply,
        SchwartzMap.toLpCLM_apply]
      rw [Lp.toTemperedDistribution_toLp_eq]
      rw [← besselPotential_schwartz (E := E) 1]
      rw [TemperedDistribution.besselPotential_besselPotential_apply]
      norm_num)
  exact congrFun heq u

/-- Every actual `L²` distribution of Sobolev order one has a Bessel coordinate whose
continuous base recovery is the original `L²` function. -/
theorem exists_sobolevOneCoordinate
    (U : Lp ℂ 2 (volume : Measure E))
    (hU : (U : TemperedDistribution E ℂ).MemSobolev 1 2) :
    ∃ u : Lp ℂ 2 (volume : Measure E),
      sobolevOneBase (E := E) u = U ∧
        TemperedDistribution.besselPotential E ℂ 1
          (U : TemperedDistribution E ℂ) =
            (u : TemperedDistribution E ℂ) := by
  obtain ⟨u, hu⟩ := hU
  refine ⟨u, ?_, hu⟩
  have htd : (sobolevOneBase (E := E) u : TemperedDistribution E ℂ) =
      (U : TemperedDistribution E ℂ) := by
    rw [sobolevOneBase_toTemperedDistribution]
    rw [← hu]
    rw [TemperedDistribution.besselPotential_besselPotential_apply]
    norm_num
  have hinjective : Function.Injective
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).toLinearMap :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  apply hinjective
  exact htd

theorem norm_lineDeriv_toLp_le_schwartzSobolevCore_one
    (m : E) (f : SchwartzMap E ℂ) :
    ‖(∂_{m} f).toLp 2 (volume : Measure E)‖ ≤
      (2 * Real.pi * ‖m‖) * ‖schwartzSobolevCore (E := E) 1 f‖ := by
  have hleftNorm := Lp.norm_fourier_eq (E := E) (F := ℂ)
    ((∂_{m} f).toLp 2 (volume : Measure E))
  have hrightNorm := Lp.norm_fourier_eq (E := E) (F := ℂ)
    (schwartzSobolevCore (E := E) 1 f)
  rw [← hleftNorm, ← hrightNorm]
  rw [SchwartzMap.toLp_fourier_eq]
  rw [SchwartzMap.lineDeriv_eq_fourierMultiplierCLM]
  simp only [SchwartzMap.fourierMultiplierCLM_apply]
  rw [FourierTransform.fourier_smul, FourierTransform.fourier_fourierInv_eq]
  simp only [schwartzSobolevCore, ContinuousLinearMap.comp_apply,
    SchwartzMap.toLpCLM_apply, schwartzBesselPotential,
    SchwartzMap.fourierMultiplierCLM_apply]
  rw [SchwartzMap.toLp_fourier_eq]
  rw [FourierTransform.fourier_fourierInv_eq]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
      (FourierTransform.fourier f).coeFn_toLp 2 volume,
      ((2 * (Real.pi : ℂ) * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · m)
          (FourierTransform.fourier f)).coeFn_toLp 2 volume,
      (SchwartzMap.smulLeftCLM ℂ (besselSymbol (E := E) 1)
        (FourierTransform.fourier f)).coeFn_toLp 2 volume] with x hf hleft hright
  rw [hleft, hright]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (besselSymbol_hasTemperateGrowth (E := E) 1)]
  simp [SchwartzMap.smulLeftCLM_apply_apply
    (Function.hasTemperateGrowth_inner_left m)]
  have hx : ‖x‖ ≤ besselSymbol (E := E) 1 x := by
    calc
      ‖x‖ ≤ √(1 + ‖x‖ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
      _ = besselSymbol (E := E) 1 x := by
        rw [Real.sqrt_eq_rpow]
        simp [besselSymbol]
  have hinner := abs_real_inner_le_norm x m
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm : 0 ≤ ‖m‖ := norm_nonneg m
  have hb : 0 ≤ besselSymbol (E := E) 1 x := (norm_nonneg x).trans hx
  rw [abs_of_nonneg hpi, abs_of_nonneg hb]
  have hinner' : |inner ℝ x m| ≤ ‖m‖ * besselSymbol (E := E) 1 x := by
    calc
      |inner ℝ x m| ≤ ‖x‖ * ‖m‖ := hinner
      _ ≤ besselSymbol (E := E) 1 x * ‖m‖ :=
        mul_le_mul_of_nonneg_right hx hm
      _ = ‖m‖ * besselSymbol (E := E) 1 x := mul_comm _ _
  calc
    2 * Real.pi * (|inner ℝ x m| * ‖FourierTransform.fourier f x‖) ≤
        2 * Real.pi * ((‖m‖ * besselSymbol (E := E) 1 x) *
          ‖FourierTransform.fourier f x‖) := by gcongr
    _ = 2 * Real.pi * ‖m‖ *
        (besselSymbol (E := E) 1 x * ‖FourierTransform.fourier f x‖) := by ring

/-- The directional derivative of a Schwartz function, viewed in `L²`. -/
noncomputable def schwartzLineDerivToLp (m : E) :
    SchwartzMap E ℂ →ₗ[ℝ] Lp ℂ 2 (volume : Measure E) :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 volume).toLinearMap.comp
    (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap E ℂ) m).toLinearMap

/-- Continuous recovery of every weak directional derivative from an order-one
Bessel coordinate. -/
noncomputable def sobolevOneLineDeriv (m : E) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  (schwartzLineDerivToLp (E := E) m).extendOfNorm
    (schwartzSobolevCore (E := E) 1).toLinearMap

@[simp] theorem sobolevOneLineDeriv_schwartzSobolevCore
    (m : E) (f : SchwartzMap E ℂ) :
    sobolevOneLineDeriv (E := E) m (schwartzSobolevCore (E := E) 1 f) =
      (∂_{m} f).toLp 2 (volume : Measure E) := by
  exact LinearMap.extendOfNorm_eq (schwartzSobolevCore_denseRange (E := E) 1)
    ⟨2 * Real.pi * ‖m‖,
      fun u ↦ by
        simpa [schwartzLineDerivToLp] using
          norm_lineDeriv_toLp_le_schwartzSobolevCore_one (E := E) m u⟩ f

theorem sobolevOneLineDeriv_toTemperedDistribution
    (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    (sobolevOneLineDeriv (E := E) m u : TemperedDistribution E ℂ) =
      ∂_{m} (sobolevOneBase (E := E) u : TemperedDistribution E ℂ) := by
  let lhs : Lp ℂ 2 (volume : Measure E) → TemperedDistribution E ℂ :=
    fun v ↦ (sobolevOneLineDeriv (E := E) m v : TemperedDistribution E ℂ)
  let rhs : Lp ℂ 2 (volume : Measure E) → TemperedDistribution E ℂ :=
    fun v ↦ ∂_{m} (sobolevOneBase (E := E) v : TemperedDistribution E ℂ)
  have hlhs : Continuous lhs :=
    (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous.comp
      (sobolevOneLineDeriv (E := E) m).continuous
  have hrhs : Continuous rhs :=
    (LineDeriv.lineDerivOpCLM ℂ (TemperedDistribution E ℂ) m).continuous.comp
      ((Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous.comp
        (sobolevOneBase (E := E)).continuous)
  have heq : lhs = rhs :=
    (schwartzSobolevCore_denseRange (E := E) 1).equalizer hlhs hrhs (by
      funext f
      change (sobolevOneLineDeriv (E := E) m
          (schwartzSobolevCore (E := E) 1 f) : TemperedDistribution E ℂ) =
        ∂_{m} (sobolevOneBase (E := E)
          (schwartzSobolevCore (E := E) 1 f) : TemperedDistribution E ℂ)
      rw [sobolevOneLineDeriv_schwartzSobolevCore,
        sobolevOneBase_schwartzSobolevCore]
      rw [Lp.toTemperedDistribution_toLp_eq,
        Lp.toTemperedDistribution_toLp_eq]
      exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq f m).symm)
  exact congrFun heq u

end RiemannianFluids.EuclideanSobolev
