import RiemannianFluids.Analysis.EuclideanSobolevCarrier

/-!
# Weak testing for Euclidean order-one Sobolev carriers

This module converts a distributional equation `g ΔU = V` into its exact weak energy
identity when `U` is only locally `H¹`.  It builds an actual graph carrier for the base
function and two directional derivatives, proves smooth graph density, extends compact
multiplier product rules, and justifies testing the equation by the recovered Sobolev
function itself.
-/

noncomputable section

namespace RiemannianFluids.EuclideanSobolev

open Complex FourierTransform Function MeasureTheory Set TemperedDistribution
open scoped ENNReal Laplacian LineDeriv RealInnerProductSpace SchwartzMap

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

abbrev SobolevOneTriple (E : Type*) [MeasurableSpace E] (μ : Measure E) :=
  Lp ℂ 2 μ × (Lp ℂ 2 μ × Lp ℂ 2 μ)

/-- Multiplication by one fixed Schwartz coefficient as a bounded real-linear operator on `L²`. -/
noncomputable def schwartzLpMultiplier (g : SchwartzMap E ℂ) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) := by
  let G : Lp ℂ ∞ (volume : Measure E) := g.toLp ∞ volume
  let L : Lp ℂ 2 (volume : Measure E) →ₗ[ℝ] Lp ℂ 2 (volume : Measure E) :=
    { toFun := fun u ↦ G • u
      map_add' := fun u v ↦ Lp.add_smul G u v
      map_smul' := fun r u ↦ by
        rw [← Lp.smul_comm r G u]
        rfl }
  exact L.mkContinuous ‖G‖ (fun u ↦ Lp.norm_smul_le G u)

theorem schwartzLpMultiplier_apply (g : SchwartzMap E ℂ)
    (u : Lp ℂ 2 (volume : Measure E)) :
    schwartzLpMultiplier (E := E) g u = g.toLp ∞ volume • u :=
  rfl

theorem schwartzLpMultiplier_coeFn (g : SchwartzMap E ℂ)
    (u : Lp ℂ 2 (volume : Measure E)) :
    (schwartzLpMultiplier (E := E) g u : E → ℂ) =ᵐ[volume]
      fun x ↦ g x * u x := by
  rw [schwartzLpMultiplier_apply]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (g.toLp ∞ volume) u,
      g.coeFn_toLp ∞ volume] with x hmul hg
  rw [hmul]
  change (g.toLp ∞ volume x) * u x = g x * u x
  rw [hg]

noncomputable def schwartzProduct (g f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x ↦ g x) f

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem schwartzProduct_apply (g f : SchwartzMap E ℂ) (x : E) :
    schwartzProduct g f x = g x * f x := by
  simp [schwartzProduct, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]

theorem schwartzLpMultiplier_toLp (g f : SchwartzMap E ℂ) :
    schwartzLpMultiplier (E := E) g (f.toLp 2 volume) =
      (schwartzProduct g f).toLp 2 volume := by
  rw [Lp.ext_iff]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (g.toLp ∞ volume) (f.toLp 2 volume),
      g.coeFn_toLp ∞ volume, f.coeFn_toLp 2 volume,
      (schwartzProduct g f).coeFn_toLp 2 volume] with x hmul hg hf hgf
  rw [schwartzLpMultiplier_apply, hmul]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [hg, hf, hgf, schwartzProduct_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lineDerivOp_mul (m : E) (g f : SchwartzMap E ℂ) :
    ∂_{m} (schwartzProduct g f) =
      schwartzProduct g (∂_{m} f) + schwartzProduct (∂_{m} g) f := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply,
    schwartzProduct_apply]
  have hfun : (schwartzProduct g f : E → ℂ) = fun y ↦ g y * f y := by
    funext y
    rw [schwartzProduct_apply]
  rw [hfun]
  change (fderiv ℝ (⇑g * ⇑f) x) m = _
  rw [fderiv_mul g.differentiableAt f.differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

noncomputable def schwartzConj (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f.postcompCLM (𝕜 := ℝ) Complex.conjCLE

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem schwartzConj_apply (f : SchwartzMap E ℂ) (x : E) :
    schwartzConj f x = Complex.conjCLE (f x) := by
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem lineDerivOp_schwartzConj (m : E) (f : SchwartzMap E ℂ) :
    ∂_{m} (schwartzConj f) = schwartzConj (∂_{m} f) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y ↦ Complex.conjCLE (f y)) x m =
    Complex.conjCLE (fderiv ℝ f x m)
  have hcomp := Complex.conjCLE.hasFDerivAt.comp x (f.hasFDerivAt x)
  have hderiv := hcomp.fderiv
  change fderiv ℝ (fun y ↦ Complex.conjCLE (f y)) x =
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x) at hderiv
  rw [hderiv]
  rfl

theorem inner_toLp_left_eq_toTemperedDistribution_schwartzConj
    (f : SchwartzMap E ℂ) (u : Lp ℂ 2 (volume : Measure E)) :
    inner ℂ (f.toLp 2 volume) u =
      (u : TemperedDistribution E ℂ) (schwartzConj f) := by
  rw [L2.inner_def, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with x hfx
  rw [hfx]
  rw [schwartzConj_apply]
  simp [RCLike.inner_apply, mul_comm]

theorem l2_real_inner_eq_re_complex_inner
    (u v : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ u v = (inner ℂ u v).re := by
  rw [L2.inner_def, L2.inner_def]
  change (∫ x, inner ℝ (u x) (v x) ∂volume) =
    RCLike.re (∫ x, inner ℂ (u x) (v x) ∂volume)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u v)]
  apply integral_congr_ae
  filter_upwards with x
  exact real_inner_eq_re_inner ℂ (u x) (v x)

def IsRealSchwartz (g : SchwartzMap E ℂ) : Prop :=
  ∀ x, Complex.conjCLE (g x) = g x

theorem schwartzLpMultiplier_inner_comm
    (g : SchwartzMap E ℂ) (hg : IsRealSchwartz g)
    (u v : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ (schwartzLpMultiplier (E := E) g u) v =
      inner ℝ u (schwartzLpMultiplier (E := E) g v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [schwartzLpMultiplier_coeFn (E := E) g u,
      schwartzLpMultiplier_coeFn (E := E) g v] with x hu hv
  rw [hu, hv]
  rw [Complex.inner, Complex.inner]
  change (v x * Complex.conjCAE (g x * u x)).re =
    (g x * v x * Complex.conjCAE (u x)).re
  rw [map_mul, show Complex.conjCAE (g x) = g x from hg x]
  ring

theorem schwartzLpMultiplier_comp
    (g f : SchwartzMap E ℂ) (u : Lp ℂ 2 (volume : Measure E)) :
    schwartzLpMultiplier (E := E) g
        (schwartzLpMultiplier (E := E) f u) =
      schwartzLpMultiplier (E := E) (schwartzProduct g f) u := by
  rw [Lp.ext_iff]
  filter_upwards [schwartzLpMultiplier_coeFn (E := E) g
      (schwartzLpMultiplier (E := E) f u),
    schwartzLpMultiplier_coeFn (E := E) f u,
    schwartzLpMultiplier_coeFn (E := E) (schwartzProduct g f) u]
      with x hgf hf hprod
  rw [hgf, hf, hprod, schwartzProduct_apply]
  ring

theorem schwartzLpMultiplier_add
    (g f : SchwartzMap E ℂ) (u : Lp ℂ 2 (volume : Measure E)) :
    schwartzLpMultiplier (E := E) (g + f) u =
      schwartzLpMultiplier (E := E) g u +
        schwartzLpMultiplier (E := E) f u := by
  rw [Lp.ext_iff]
  filter_upwards [schwartzLpMultiplier_coeFn (E := E) (g + f) u,
    schwartzLpMultiplier_coeFn (E := E) g u,
    schwartzLpMultiplier_coeFn (E := E) f u,
    Lp.coeFn_add (schwartzLpMultiplier (E := E) g u)
      (schwartzLpMultiplier (E := E) f u)] with x hsum hg hf hadd
  rw [hsum, hadd]
  simp only [Pi.add_apply]
  rw [hg, hf]
  simp only [add_apply]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartzProduct_comm (g f : SchwartzMap E ℂ) :
    schwartzProduct g f = schwartzProduct f g := by
  ext x
  simp [mul_comm]

theorem schwartzLpMultiplier_lineDeriv_square
    (m : E) (q : SchwartzMap E ℂ) (u : Lp ℂ 2 (volume : Measure E)) :
    schwartzLpMultiplier (E := E) (∂_{m} (schwartzProduct q q)) u =
      (2 : ℝ) • schwartzLpMultiplier (E := E) q
        (schwartzLpMultiplier (E := E) (∂_{m} q) u) := by
  rw [lineDerivOp_mul, schwartzLpMultiplier_add]
  rw [← schwartzLpMultiplier_comp]
  rw [schwartzProduct_comm (∂_{m} q) q]
  rw [← schwartzLpMultiplier_comp]
  simp [two_smul ℝ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartzProduct_conj_of_real
    (g f : SchwartzMap E ℂ) (hg : IsRealSchwartz g) :
    schwartzProduct g (schwartzConj f) =
      schwartzConj (schwartzProduct g f) := by
  ext x
  simp only [schwartzProduct_apply, schwartzConj_apply]
  change g x * Complex.conjCAE (f x) = Complex.conjCAE (g x * f x)
  rw [map_mul, show Complex.conjCAE (g x) = g x from hg x]

theorem toTemperedDistribution_iteratedLineDeriv_schwartzConj
    (m : E) (u U : Lp ℂ 2 (volume : Measure E))
    (hbase : sobolevOneBase (E := E) u = U)
    (f : SchwartzMap E ℂ) :
    (U : TemperedDistribution E ℂ) (∂_{m} (∂_{m} (schwartzConj f))) =
      -inner ℂ ((∂_{m} f).toLp 2 volume)
        (sobolevOneLineDeriv (E := E) m u) := by
  have hderiv := sobolevOneLineDeriv_toTemperedDistribution (E := E) m u
  rw [hbase] at hderiv
  have heval := DFunLike.congr_fun hderiv (∂_{m} (schwartzConj f))
  rw [lineDerivOp_schwartzConj] at heval
  rw [← inner_toLp_left_eq_toTemperedDistribution_schwartzConj] at heval
  rw [TemperedDistribution.lineDerivOp_apply_apply] at heval
  rw [map_neg] at heval
  rw [lineDerivOp_schwartzConj]
  rw [heval]
  simp

theorem toTemperedDistribution_laplacian_schwartzConj
    (b : OrthonormalBasis (Fin 2) ℝ E)
    (u U : Lp ℂ 2 (volume : Measure E))
    (hbase : sobolevOneBase (E := E) u = U)
    (f : SchwartzMap E ℂ) :
    (U : TemperedDistribution E ℂ) (Δ (schwartzConj f)) =
      -(inner ℂ ((∂_{b 0} f).toLp 2 volume)
          (sobolevOneLineDeriv (E := E) (b 0) u) +
        inner ℂ ((∂_{b 1} f).toLp 2 volume)
          (sobolevOneLineDeriv (E := E) (b 1) u)) := by
  rw [SchwartzMap.laplacian_eq_sum b, Fin.sum_univ_two, map_add]
  rw [toTemperedDistribution_iteratedLineDeriv_schwartzConj
      (E := E) (b 0) u U hbase f,
    toTemperedDistribution_iteratedLineDeriv_schwartzConj
      (E := E) (b 1) u U hbase f]
  ring

/-- The base value and two weak directional derivatives of a Schwartz function. -/
noncomputable def sobolevOneTripleCore (m n : E) :
    SchwartzMap E ℂ →L[ℝ] SobolevOneTriple E volume :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 volume).prod
    (((SchwartzMap.toLpCLM ℝ ℂ 2 volume).comp
      (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap E ℂ) m)).prod
      ((SchwartzMap.toLpCLM ℝ ℂ 2 volume).comp
        (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap E ℂ) n)))

@[simp] theorem sobolevOneTripleCore_apply (m n : E) (f : SchwartzMap E ℂ) :
    sobolevOneTripleCore (E := E) m n f =
      (f.toLp 2 volume, ((∂_{m} f).toLp 2 volume, (∂_{n} f).toLp 2 volume)) :=
  rfl

/-- Continuous triple recovery from a Bessel-potential `H¹` coordinate. -/
noncomputable def sobolevOneTripleRecovery (m n : E) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] SobolevOneTriple E volume :=
  (sobolevOneBase (E := E)).prod
    ((sobolevOneLineDeriv (E := E) m).prod
      (sobolevOneLineDeriv (E := E) n))

@[simp] theorem sobolevOneTripleRecovery_core (m n : E) (f : SchwartzMap E ℂ) :
    sobolevOneTripleRecovery (E := E) m n
        (schwartzSobolevCore (E := E) 1 f) =
      sobolevOneTripleCore (E := E) m n f := by
  simp [sobolevOneTripleRecovery, sobolevOneTripleCore]

/-- Every recovered `H¹` triple is in the closure of the smooth graph. -/
theorem sobolevOneTripleRecovery_mem_closure_range
    (m n : E) (u : Lp ℂ 2 (volume : Measure E)) :
    sobolevOneTripleRecovery (E := E) m n u ∈
      closure (range (sobolevOneTripleCore (E := E) m n)) := by
  have hdense : Dense (range (schwartzSobolevCore (E := E) 1)) :=
    schwartzSobolevCore_denseRange (E := E) 1
  have hmem := (sobolevOneTripleRecovery (E := E) m n).continuous
    |>.range_subset_closure_image_dense hdense
      ⟨u, rfl⟩
  apply closure_mono _ hmem
  rintro y ⟨v, ⟨f, rfl⟩, rfl⟩
  exact ⟨f, (sobolevOneTripleRecovery_core (E := E) m n f).symm⟩

/-- Product rule on base value and two weak derivatives. -/
noncomputable def sobolevOneTripleMultiplier (m n : E) (g : SchwartzMap E ℂ) :
    SobolevOneTriple E volume →L[ℝ] SobolevOneTriple E volume := by
  let L2 := Lp ℂ 2 (volume : Measure E)
  let base : SobolevOneTriple E volume →L[ℝ] L2 :=
    ContinuousLinearMap.fst ℝ L2 (L2 × L2)
  let derivs : SobolevOneTriple E volume →L[ℝ] L2 × L2 :=
    ContinuousLinearMap.snd ℝ L2 (L2 × L2)
  let dx : SobolevOneTriple E volume →L[ℝ] L2 :=
    (ContinuousLinearMap.fst ℝ L2 L2).comp derivs
  let dy : SobolevOneTriple E volume →L[ℝ] L2 :=
    (ContinuousLinearMap.snd ℝ L2 L2).comp derivs
  let Mg := schwartzLpMultiplier (E := E) g
  let Mdx := schwartzLpMultiplier (E := E) (∂_{m} g)
  let Mdy := schwartzLpMultiplier (E := E) (∂_{n} g)
  exact (Mg.comp base).prod
    (((Mg.comp dx) + (Mdx.comp base)).prod
      ((Mg.comp dy) + (Mdy.comp base)))

theorem sobolevOneTripleMultiplier_core (m n : E)
    (g f : SchwartzMap E ℂ) :
    sobolevOneTripleMultiplier (E := E) m n g
        (sobolevOneTripleCore (E := E) m n f) =
      sobolevOneTripleCore (E := E) m n (schwartzProduct g f) := by
  simp only [sobolevOneTripleMultiplier, sobolevOneTripleCore_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', add_apply]
  rw [schwartzLpMultiplier_toLp]
  rw [lineDerivOp_mul m g f, lineDerivOp_mul n g f]
  rw [schwartzLpMultiplier_toLp, schwartzLpMultiplier_toLp,
    schwartzLpMultiplier_toLp, schwartzLpMultiplier_toLp]
  congr 1

/-- A distributional equation `g ΔU = V` may be tested against the actual local `H¹`
representative of `U`.  This is the weak Green identity needed by cutoff-energy arguments. -/
theorem localized_weak_energy_identity
    (b : OrthonormalBasis (Fin 2) ℝ E)
    (g : SchwartzMap E ℂ) (hg : IsRealSchwartz g)
    (u U V : Lp ℂ 2 (volume : Measure E))
    (hbase : sobolevOneBase (E := E) u = U)
    (hequation :
      TemperedDistribution.smulLeftCLM ℂ (fun x ↦ g x)
          (Δ (U : TemperedDistribution E ℂ)) =
        (V : TemperedDistribution E ℂ)) :
    let x := sobolevOneTripleRecovery (E := E) (b 0) (b 1) u
    let gx := sobolevOneTripleMultiplier (E := E) (b 0) (b 1) g x
    inner ℝ gx.2.1 x.2.1 + inner ℝ gx.2.2 x.2.2 + inner ℝ x.1 V = 0 := by
  let x := sobolevOneTripleRecovery (E := E) (b 0) (b 1) u
  let M := sobolevOneTripleMultiplier (E := E) (b 0) (b 1) g
  let energy : SobolevOneTriple E volume → ℝ := fun y ↦
    inner ℝ (M y).2.1 x.2.1 + inner ℝ (M y).2.2 x.2.2 + inner ℝ y.1 V
  have hMdx : Continuous (fun y : SobolevOneTriple E volume ↦ (M y).2.1) :=
    continuous_fst.comp (continuous_snd.comp M.continuous)
  have hMdy : Continuous (fun y : SobolevOneTriple E volume ↦ (M y).2.2) :=
    continuous_snd.comp (continuous_snd.comp M.continuous)
  have hbaseContinuous : Continuous (fun y : SobolevOneTriple E volume ↦ y.1) :=
    continuous_fst
  have henergy : Continuous energy :=
    ((hMdx.inner continuous_const).add (hMdy.inner continuous_const)).add
      (hbaseContinuous.inner continuous_const)
  have hxClosure : x ∈ closure
      (range (sobolevOneTripleCore (E := E) (b 0) (b 1))) :=
    sobolevOneTripleRecovery_mem_closure_range (E := E) (b 0) (b 1) u
  have hcore : ∀ y ∈ range (sobolevOneTripleCore (E := E) (b 0) (b 1)),
      energy y = 0 := by
    rintro y ⟨f, rfl⟩
    let psi := schwartzProduct g f
    have hdist := DFunLike.congr_fun hequation (schwartzConj f)
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
      TemperedDistribution.laplacian_apply_apply] at hdist
    change (U : TemperedDistribution E ℂ)
        (Δ (schwartzProduct g (schwartzConj f))) =
      (V : TemperedDistribution E ℂ) (schwartzConj f) at hdist
    rw [schwartzProduct_conj_of_real g f hg] at hdist
    rw [toTemperedDistribution_laplacian_schwartzConj
      (E := E) b u U hbase psi] at hdist
    rw [← inner_toLp_left_eq_toTemperedDistribution_schwartzConj] at hdist
    have hre := congrArg Complex.re hdist
    dsimp only [energy, M, x]
    rw [sobolevOneTripleMultiplier_core]
    simp only [sobolevOneTripleCore_apply]
    simp only [sobolevOneTripleRecovery, ContinuousLinearMap.prod_apply]
    change inner ℝ ((∂_{b 0} psi).toLp 2 volume)
          (sobolevOneLineDeriv (E := E) (b 0) u) +
        inner ℝ ((∂_{b 1} psi).toLp 2 volume)
          (sobolevOneLineDeriv (E := E) (b 1) u) +
        inner ℝ (f.toLp 2 volume) V = 0
    rw [l2_real_inner_eq_re_complex_inner,
      l2_real_inner_eq_re_complex_inner,
      l2_real_inner_eq_re_complex_inner]
    simp only [Complex.neg_re, Complex.add_re] at hre
    linarith
  have hxzero := henergy.continuousAt.continuousWithinAt.eq_const_of_mem_closure
    hxClosure hcore
  exact hxzero

/-- Caccioppoli estimate obtained by using the square of a real cutoff in the weak
energy identity. -/
theorem localized_square_energy_bound
    (b : OrthonormalBasis (Fin 2) ℝ E)
    (q : SchwartzMap E ℂ) (hq : IsRealSchwartz q)
    (u U V : Lp ℂ 2 (volume : Measure E))
    (hbase : sobolevOneBase (E := E) u = U)
    (hequation :
      TemperedDistribution.smulLeftCLM ℂ
          (fun x ↦ schwartzProduct q q x)
          (Δ (U : TemperedDistribution E ℂ)) =
        (V : TemperedDistribution E ℂ)) :
    inner ℝ U V ≤
      ‖schwartzLpMultiplier (E := E) (∂_{b 0} q) U‖ ^ 2 +
        ‖schwartzLpMultiplier (E := E) (∂_{b 1} q) U‖ ^ 2 := by
  let g := schwartzProduct q q
  have hg : IsRealSchwartz g := by
    intro x
    simp only [g, schwartzProduct_apply]
    change Complex.conjCAE (q x * q x) = q x * q x
    rw [map_mul, show Complex.conjCAE (q x) = q x from hq x]
  have henergy := localized_weak_energy_identity (E := E) b g hg u U V hbase hequation
  simp only [sobolevOneTripleRecovery, sobolevOneTripleMultiplier,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', add_apply] at henergy
  rw [hbase] at henergy
  change inner ℝ
        (schwartzLpMultiplier (E := E) g
            (sobolevOneLineDeriv (E := E) (b 0) u) +
          schwartzLpMultiplier (E := E) (∂_{b 0} g) U)
        (sobolevOneLineDeriv (E := E) (b 0) u) +
      inner ℝ
        (schwartzLpMultiplier (E := E) g
            (sobolevOneLineDeriv (E := E) (b 1) u) +
          schwartzLpMultiplier (E := E) (∂_{b 1} g) U)
        (sobolevOneLineDeriv (E := E) (b 1) u) +
      inner ℝ U V = 0 at henergy
  rw [show g = schwartzProduct q q from rfl] at henergy
  rw [← schwartzLpMultiplier_comp, ← schwartzLpMultiplier_comp] at henergy
  rw [schwartzLpMultiplier_lineDeriv_square,
    schwartzLpMultiplier_lineDeriv_square] at henergy
  rw [inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left] at henergy
  let dx := sobolevOneLineDeriv (E := E) (b 0) u
  let dy := sobolevOneLineDeriv (E := E) (b 1) u
  let qdx := schwartzLpMultiplier (E := E) q
    dx
  let qdy := schwartzLpMultiplier (E := E) q
    dy
  let dxqU := schwartzLpMultiplier (E := E) (∂_{b 0} q) U
  let dyqU := schwartzLpMultiplier (E := E) (∂_{b 1} q) U
  have hmainx : inner ℝ
      (schwartzLpMultiplier (E := E) q qdx) dx = ‖qdx‖ ^ 2 := by
    rw [schwartzLpMultiplier_inner_comm q hq]
    exact real_inner_self_eq_norm_sq qdx
  have hmainy : inner ℝ
      (schwartzLpMultiplier (E := E) q qdy) dy = ‖qdy‖ ^ 2 := by
    rw [schwartzLpMultiplier_inner_comm q hq]
    exact real_inner_self_eq_norm_sq qdy
  have hcrossx : inner ℝ
      (schwartzLpMultiplier (E := E) q dxqU) dx = inner ℝ dxqU qdx := by
    exact schwartzLpMultiplier_inner_comm q hq dxqU dx
  have hcrossy : inner ℝ
      (schwartzLpMultiplier (E := E) q dyqU) dy = inner ℝ dyqU qdy := by
    exact schwartzLpMultiplier_inner_comm q hq dyqU dy
  change inner ℝ (schwartzLpMultiplier (E := E) q qdx) dx +
        2 * inner ℝ (schwartzLpMultiplier (E := E) q dxqU) dx +
      (inner ℝ (schwartzLpMultiplier (E := E) q qdy) dy +
        2 * inner ℝ (schwartzLpMultiplier (E := E) q dyqU) dy) +
      inner ℝ U V = 0 at henergy
  rw [hmainx, hmainy, hcrossx, hcrossy] at henergy
  have hxnonneg : 0 ≤ ‖qdx + dxqU‖ ^ 2 := sq_nonneg _
  have hynonneg : 0 ≤ ‖qdy + dyqU‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real] at hxnonneg hynonneg
  rw [real_inner_comm dxqU qdx] at hxnonneg
  rw [real_inner_comm dyqU qdy] at hynonneg
  change inner ℝ U V ≤ ‖dxqU‖ ^ 2 + ‖dyqU‖ ^ 2
  nlinarith

end RiemannianFluids.EuclideanSobolev
