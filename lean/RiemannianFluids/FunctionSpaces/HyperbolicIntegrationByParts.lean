import RiemannianFluids.FunctionSpaces.HyperbolicFirstOrder
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts on the measured hyperbolic plane

This module proves the two frame integration-by-parts identities on the smooth compact core of
the Poincare half-plane.  The proof extends compactly supported fields by zero to the ambient
real plane and applies Mathlib's Euclidean line-derivative theorem to the correctly weighted
fields.  In the oriented orthonormal frame `e₁ = y ∂x`, `e₂ = y ∂y`, the results are

    ∫ f (e₁ g) dvol = -∫ (e₁ f) g dvol,
    ∫ f (e₂ g) dvol = -∫ (e₂ f - f) g dvol.

The extra zeroth-order term in the second identity records `div(e₂) = -1`.  These identities
are the analytic input for the formal-adjoint relations `d₀* = δ₁` and `d₁* = δ₂`, and hence
for closing the concrete hyperbolic de Rham complex.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Bundle Complex Filter Function MeasureTheory Set Topology
open scoped Bundle ContDiff ENNReal Manifold NNReal RealInnerProductSpace Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extension by zero from the open upper half-plane to its ambient real plane. -/
noncomputable def ambientExtendZero (f : HyperbolicPlane → F) : ℂ → F :=
  Function.extend ((↑) : HyperbolicPlane → ℂ) f 0

@[simp] theorem ambientExtendZero_coe (f : HyperbolicPlane → F)
    (p : HyperbolicPlane) : ambientExtendZero f (p : ℂ) = f p := by
  exact UpperHalfPlane.coe_injective.extend_apply f 0 p

example {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      UpperHalfPlane.ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using! tendsto_id
  · simpa using! contDiffAt_id.congr_of_eventuallyEq
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz)

theorem mfderiv_ofComplex_real {z : ℂ} (hz : 0 < z.im) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      UpperHalfPlane.ofComplex z = ContinuousLinearMap.id ℝ ℂ := by
  have hof : UpperHalfPlane.ofComplex z = (⟨z, hz⟩ : HyperbolicPlane) :=
    UpperHalfPlane.ofComplex_apply_of_im_pos hz
  have hdiff : MDifferentiableAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) UpperHalfPlane.ofComplex z :=
    (show ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      UpperHalfPlane.ofComplex z by
        rw [contMDiffAt_iff]
        constructor
        · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
          refine Tendsto.congr'
            (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).symm ?_
          simpa [hof] using! tendsto_id
        · simpa using! contDiffAt_id.congr_of_eventuallyEq
            (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (I := modelWithCornersSelf ℝ ℂ)
    (I' := modelWithCornersSelf ℝ ℂ) (I'' := modelWithCornersSelf ℝ ℂ)
    (x := z) (f := UpperHalfPlane.ofComplex)
    (g := ((↑) : HyperbolicPlane → ℂ))
    (mdifferentiable_coe _) hdiff
  have hlhs : mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (((↑) : HyperbolicPlane → ℂ) ∘ UpperHalfPlane.ofComplex) z =
        ContinuousLinearMap.id ℝ ℂ := by
    rw [(UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).mfderiv_eq]
    exact mfderiv_id
  rw [hlhs, hof, mfderiv_coe] at hchain
  ext v
  have hv := DFunLike.congr_fun hchain.symm v
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
    UpperHalfPlane.ofComplex z v = v
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
    UpperHalfPlane.ofComplex z v = v at hv
  exact hv

theorem contDiffAt_ofComplex_real {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      UpperHalfPlane.ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using! tendsto_id
  · simpa using! contDiffAt_id.congr_of_eventuallyEq
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz)

theorem hasCompactSupport_ambientExtendZero
    (f : HyperbolicSmoothCompactSection F) :
    HasCompactSupport (ambientExtendZero f.toFun) :=
  f.hasCompactSupport_toFun.extend_zero UpperHalfPlane.continuous_coe

theorem continuous_ambientExtendZero
    (f : HyperbolicSmoothCompactSection F) :
    Continuous (ambientExtendZero f.toFun) := by
  apply continuous_of_tsupport
  intro z hz
  have hzimage : z ∈ ((↑) : HyperbolicPlane → ℂ) '' tsupport f.toFun :=
    f.hasCompactSupport_toFun.tsupport_extend_zero_subset
      UpperHalfPlane.continuous_coe hz
  rcases hzimage with ⟨p, -, rfl⟩
  rw [← isOpenEmbedding_coe.continuousAt_iff, ambientExtendZero,
    Function.extend_comp UpperHalfPlane.coe_injective]
  exact f.contMDiff_toFun.continuous.continuousAt

theorem ambientExtendZero_eventuallyEq_comp_ofComplex
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    ambientExtendZero f.toFun =ᶠ[𝓝 (p : ℂ)]
      f.toFun ∘ UpperHalfPlane.ofComplex := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos]
    with w hw
  rw [show w = ((⟨w, hw⟩ : HyperbolicPlane) : ℂ) by rfl,
    ambientExtendZero_coe]
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw]

theorem contDiff_ambientExtendZero
    (f : HyperbolicSmoothCompactSection F) :
    ContDiff ℝ ∞ (ambientExtendZero f.toFun) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (ambientExtendZero f.toFun)
  · have hzimage : z ∈ ((↑) : HyperbolicPlane → ℂ) '' tsupport f.toFun :=
      f.hasCompactSupport_toFun.tsupport_extend_zero_subset
        UpperHalfPlane.continuous_coe hz
    rcases hzimage with ⟨p, -, rfl⟩
    have hfAt : ContMDiffAt (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ F) ∞ f.toFun
        (UpperHalfPlane.ofComplex (p : ℂ)) := by
      simpa using f.contMDiff_toFun p
    have hcomp : ContDiffAt ℝ ∞ (f.toFun ∘ UpperHalfPlane.ofComplex) (p : ℂ) :=
      (hfAt.comp _ (contDiffAt_ofComplex_real p.im_pos)).contDiffAt
    exact hcomp.congr_of_eventuallyEq
      (ambientExtendZero_eventuallyEq_comp_ofComplex f p)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem integral_comap_eq_integral_ambientExtendZero
    [CompleteSpace F] (f : HyperbolicSmoothCompactSection F) :
    (∫ p, f p ∂(volume.comap ((↑) : HyperbolicPlane → ℂ))) =
      ∫ z, ambientExtendZero f.toFun z ∂volume := by
  have hpres : MeasurePreserving ((↑) : HyperbolicPlane → ℂ)
      (volume.comap ((↑) : HyperbolicPlane → ℂ))
      (volume.restrict (Set.range ((↑) : HyperbolicPlane → ℂ))) :=
    ⟨UpperHalfPlane.measurable_coe, by
      rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
  calc
    (∫ p, f p ∂(volume.comap ((↑) : HyperbolicPlane → ℂ))) =
        ∫ p, ambientExtendZero f.toFun (p : ℂ)
          ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)) := by simp
    _ = ∫ z, ambientExtendZero f.toFun z
          ∂(volume.restrict (Set.range ((↑) : HyperbolicPlane → ℂ))) :=
      hpres.integral_comp UpperHalfPlane.measurableEmbedding_coe _
    _ = ∫ z, ambientExtendZero f.toFun z ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
        exact Function.extend_apply' _ _ _ hz

/-- Multiply a compact core field by the hyperbolic volume density in Euclidean coordinates. -/
noncomputable def densityWeightedCore
    (f : HyperbolicSmoothCompactSection F) : HyperbolicSmoothCompactSection F :=
  ⟨fun p ↦ ((p.im ^ 2)⁻¹ : ℝ) • f p,
    fun p ↦ (contMDiffAt_im_sq_inv p).smul (f.contMDiff_toFun p),
    f.hasCompactSupport_toFun.smul_left⟩

@[simp] theorem densityWeightedCore_apply
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    densityWeightedCore f p = ((p.im ^ 2)⁻¹ : ℝ) • f p :=
  rfl

theorem integral_hyperbolic_eq_integral_ambientDensity
    [CompleteSpace F] (f : HyperbolicSmoothCompactSection F) :
    (∫ p, f p ∂hyperbolicVolume) =
      ∫ z, ambientExtendZero (densityWeightedCore f).toFun z ∂volume := by
  rw [hyperbolicVolume_def]
  let density : HyperbolicPlane → ℝ≥0 := fun p ↦
    (1 / NNReal.mk p.im p.im_pos.le) ^ 2
  have him : Measurable (fun p : HyperbolicPlane ↦ p.im) :=
    (contMDiff_im (n := 0)).continuous.measurable
  have hdensity : Measurable density := by
    rw [← measurable_coe_nnreal_real_iff]
    simpa only [density, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk,
      Pi.div_apply, Pi.one_apply] using
      ((measurable_const.div him).pow_const 2)
  change (∫ p, f p
      ∂(volume.comap ((↑) : HyperbolicPlane → ℂ)).withDensity fun p ↦ density p) = _
  rw [integral_withDensity_eq_integral_smul hdensity]
  have hfun : (fun p : HyperbolicPlane ↦ density p • f p) =
      (densityWeightedCore f).toFun := by
    funext p
    simp [density, densityWeightedCore, NNReal.smul_def, div_pow]
  rw [hfun]
  exact integral_comap_eq_integral_ambientExtendZero
    (densityWeightedCore f)

theorem fderiv_comp_ofComplex_eq_manifoldDerivative
    (f : HyperbolicPlane → F)
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ f)
    (p : HyperbolicPlane) :
    fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) (p : ℂ) =
      manifoldDerivativeFun f p := by
  change fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) (p : ℂ) =
    mvfderiv (modelWithCornersSelf ℝ ℂ) f p
  have hcomp := mfderiv_comp (I := modelWithCornersSelf ℝ ℂ)
    (I' := modelWithCornersSelf ℝ ℂ) (I'' := modelWithCornersSelf ℝ F)
    (x := (p : ℂ)) (f := UpperHalfPlane.ofComplex) (g := f)
    (by simpa using (hf p).mdifferentiableAt (by simp))
    ((show ContMDiffAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) ∞ UpperHalfPlane.ofComplex (p : ℂ) by
        exact (by
          rw [contMDiffAt_iff]
          constructor
          · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
            refine Tendsto.congr'
              (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex p.im_pos).symm ?_
            simpa [UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos] using! tendsto_id
          · simpa using! contDiffAt_id.congr_of_eventuallyEq
              (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex p.im_pos))).mdifferentiableAt (by simp))
  simp only [mfderiv_eq_fderiv] at hcomp
  rw [hcomp]
  rw [mfderiv_ofComplex_real p.im_pos]
  rw [UpperHalfPlane.ofComplex_apply]
  ext v
  rfl

theorem fderiv_ambientExtendZero_coe
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    fderiv ℝ (ambientExtendZero f.toFun) (p : ℂ) =
      manifoldDerivativeFun f.toFun p := by
  rw [(ambientExtendZero_eventuallyEq_comp_ofComplex f p).fderiv_eq]
  exact fderiv_comp_ofComplex_eq_manifoldDerivative
    f.toFun f.contMDiff_toFun p

theorem fderiv_ambientExtendZero_coe_apply_one
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    fderiv ℝ (ambientExtendZero f.toFun) (p : ℂ) 1 =
      (p.im)⁻¹ • horizontalDerivative f.toFun p := by
  rw [fderiv_ambientExtendZero_coe]
  change manifoldDerivativeFun f.toFun p 1 =
    (p.im)⁻¹ • manifoldDerivativeFun f.toFun p (p.im : ℂ)
  have hmap := (manifoldDerivativeFun f.toFun p).map_smul (p.im) (1 : ℂ)
  have hmap' : manifoldDerivativeFun f.toFun p (p.im : ℂ) =
      p.im • manifoldDerivativeFun f.toFun p 1 := by
    simpa only [Complex.real_smul, mul_one] using hmap
  rw [hmap']
  simp [im_ne_zero p]

theorem fderiv_ambientExtendZero_coe_apply_I
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    fderiv ℝ (ambientExtendZero f.toFun) (p : ℂ) Complex.I =
      (p.im)⁻¹ • verticalDerivative f.toFun p := by
  rw [fderiv_ambientExtendZero_coe]
  change manifoldDerivativeFun f.toFun p Complex.I =
    (p.im)⁻¹ • manifoldDerivativeFun f.toFun p ((p.im : ℂ) * Complex.I)
  have hmap := (manifoldDerivativeFun f.toFun p).map_smul (p.im) Complex.I
  have hmap' : manifoldDerivativeFun f.toFun p ((p.im : ℂ) * Complex.I) =
      p.im • manifoldDerivativeFun f.toFun p Complex.I := by
    simpa only [Complex.real_smul] using hmap
  rw [hmap']
  simp [im_ne_zero p]

/-- Multiply a compact core field by one inverse power of height. -/
noncomputable def inverseImWeightedCore
    (f : HyperbolicSmoothCompactSection F) : HyperbolicSmoothCompactSection F :=
  ⟨fun p ↦ (p.im)⁻¹ • f p,
    fun p ↦ (contMDiffAt_im_inv p).smul (f.contMDiff_toFun p),
    f.hasCompactSupport_toFun.smul_left⟩

@[simp] theorem inverseImWeightedCore_apply
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    inverseImWeightedCore f p = (p.im)⁻¹ • f p :=
  rfl

theorem mvfderiv_im_inv (p : HyperbolicPlane)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) p) :
    mvfderiv (modelWithCornersSelf ℝ ℂ) (fun q : HyperbolicPlane ↦ (q.im)⁻¹) p v =
      -((p.im ^ 2)⁻¹) * Complex.im v := by
  have hinv : HasMFDerivAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) (fun q : HyperbolicPlane ↦ (q.im)⁻¹) p
      (-((p.im ^ 2)⁻¹) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) :=
    (hasMFDerivAt_im p).inv (im_ne_zero p)
  show mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
    (fun q : HyperbolicPlane ↦ (q.im)⁻¹) p v = _
  rw [hinv.mfderiv]
  rfl

theorem horizontalDerivative_inverseImWeightedCore
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    horizontalDerivative (inverseImWeightedCore f).toFun p =
      (p.im)⁻¹ * horizontalDerivative f.toFun p := by
  change mvfderiv (modelWithCornersSelf ℝ ℂ)
      (fun q : HyperbolicPlane ↦ (q.im)⁻¹ * f q) p (p.im : ℂ) = _
  rw [show (fun q : HyperbolicPlane ↦ (q.im)⁻¹ * f q) =
      (fun q ↦ (q.im)⁻¹) * f.toFun by rfl]
  rw [mvfderiv_mul
    ((contMDiffAt_im_inv (n := ∞) p).mdifferentiableAt (by simp))
    ((f.contMDiff_toFun p).mdifferentiableAt (by simp))]
  change p.im⁻¹ * manifoldDerivativeFun f.toFun p (p.im : ℂ) +
      f p * mvfderiv (modelWithCornersSelf ℝ ℂ)
        (fun q : HyperbolicPlane ↦ (q.im)⁻¹) p (p.im : ℂ) = _
  rw [mvfderiv_im_inv]
  simp [horizontalDerivative, horizontalFrameVector, manifoldDerivativeFun]

theorem verticalDerivative_inverseImWeightedCore
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    verticalDerivative (inverseImWeightedCore f).toFun p =
      (p.im)⁻¹ * (verticalDerivative f.toFun p - f p) := by
  change mvfderiv (modelWithCornersSelf ℝ ℂ)
      (fun q : HyperbolicPlane ↦ (q.im)⁻¹ * f q) p
        ((p.im : ℂ) * Complex.I) = _
  rw [show (fun q : HyperbolicPlane ↦ (q.im)⁻¹ * f q) =
      (fun q ↦ (q.im)⁻¹) * f.toFun by rfl]
  rw [mvfderiv_mul
    ((contMDiffAt_im_inv (n := ∞) p).mdifferentiableAt (by simp))
    ((f.contMDiff_toFun p).mdifferentiableAt (by simp))]
  change p.im⁻¹ * manifoldDerivativeFun f.toFun p
        ((p.im : ℂ) * Complex.I) +
      f p * mvfderiv (modelWithCornersSelf ℝ ℂ)
        (fun q : HyperbolicPlane ↦ (q.im)⁻¹) p
          ((p.im : ℂ) * Complex.I) = _
  rw [mvfderiv_im_inv]
  simp [verticalDerivative, verticalFrameVector, manifoldDerivativeFun]
  field_simp [im_ne_zero p]
  ring

theorem fderiv_ambientInverseIm_coe_apply_one
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    fderiv ℝ (ambientExtendZero (inverseImWeightedCore f).toFun)
        (p : ℂ) 1 =
      (p.im ^ 2)⁻¹ * horizontalDerivative f.toFun p := by
  rw [fderiv_ambientExtendZero_coe_apply_one,
    horizontalDerivative_inverseImWeightedCore]
  simp only [smul_eq_mul]
  field_simp [im_ne_zero p]

theorem fderiv_ambientInverseIm_coe_apply_I
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    fderiv ℝ (ambientExtendZero (inverseImWeightedCore f).toFun)
        (p : ℂ) Complex.I =
      (p.im ^ 2)⁻¹ * (verticalDerivative f.toFun p - f p) := by
  rw [fderiv_ambientExtendZero_coe_apply_I,
    verticalDerivative_inverseImWeightedCore]
  simp only [smul_eq_mul]
  field_simp [im_ne_zero p]

/-- Pointwise product on the scalar compact core. -/
noncomputable def scalarProductCore
    (f g : HyperbolicSmoothCompactScalar) : HyperbolicSmoothCompactScalar :=
  ⟨fun p ↦ f p * g p,
    f.contMDiff_toFun.mul g.contMDiff_toFun,
    f.hasCompactSupport_toFun.mul_right⟩

@[simp] theorem scalarProductCore_apply
    (f g : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    scalarProductCore f g p = f p * g p :=
  rfl

theorem integrable_fderiv_mul_ambient
    (f g : HyperbolicSmoothCompactScalar) (v : ℂ) :
    Integrable (fun z ↦
      fderiv ℝ (ambientExtendZero f.toFun) z v *
        ambientExtendZero g.toFun z) volume := by
  have hderivContinuous : Continuous (fun z ↦
      fderiv ℝ (ambientExtendZero f.toFun) z v) :=
    (contDiff_ambientExtendZero f).continuous_fderiv_apply (by simp) |>.comp
      (continuous_id.prodMk continuous_const)
  have hsupp : HasCompactSupport (fun z ↦
      fderiv ℝ (ambientExtendZero f.toFun) z v) :=
    (hasCompactSupport_ambientExtendZero f).fderiv_apply ℝ v
  exact (hderivContinuous.mul (continuous_ambientExtendZero g))
    |>.integrable_of_hasCompactSupport hsupp.mul_right

theorem integrable_ambient_mul_fderiv
    (f g : HyperbolicSmoothCompactScalar) (v : ℂ) :
    Integrable (fun z ↦ ambientExtendZero f.toFun z *
      fderiv ℝ (ambientExtendZero g.toFun) z v) volume := by
  simpa only [mul_comm] using integrable_fderiv_mul_ambient g f v

theorem integrable_ambient_mul_ambient
    (f g : HyperbolicSmoothCompactScalar) :
    Integrable (fun z ↦ ambientExtendZero f.toFun z *
      ambientExtendZero g.toFun z) volume :=
  ((continuous_ambientExtendZero f).mul
    (continuous_ambientExtendZero g)).integrable_of_hasCompactSupport
      (hasCompactSupport_ambientExtendZero f).mul_right

theorem ambient_horizontal_left
    (f g : HyperbolicSmoothCompactScalar) (z : ℂ) :
    ambientExtendZero
        (densityWeightedCore
          (scalarProductCore f (horizontalDerivativeCore g))).toFun z =
      ambientExtendZero (inverseImWeightedCore f).toFun z *
        fderiv ℝ (ambientExtendZero g.toFun) z 1 := by
  by_cases hz : z ∈ Set.range ((↑) : HyperbolicPlane → ℂ)
  · rcases hz with ⟨p, rfl⟩
    rw [ambientExtendZero_coe, ambientExtendZero_coe,
      fderiv_ambientExtendZero_coe_apply_one]
    change (p.im ^ 2)⁻¹ * (f p * horizontalDerivative g.toFun p) =
      p.im⁻¹ * f p * (p.im⁻¹ * horizontalDerivative g.toFun p)
    field_simp [im_ne_zero p]
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz,
      Pi.zero_apply, zero_mul]

theorem ambient_horizontal_right
    (f g : HyperbolicSmoothCompactScalar) (z : ℂ) :
    ambientExtendZero
        (densityWeightedCore
          (scalarProductCore (horizontalDerivativeCore f) g)).toFun z =
      fderiv ℝ
          (ambientExtendZero (inverseImWeightedCore f).toFun) z 1 *
        ambientExtendZero g.toFun z := by
  by_cases hz : z ∈ Set.range ((↑) : HyperbolicPlane → ℂ)
  · rcases hz with ⟨p, rfl⟩
    rw [ambientExtendZero_coe, ambientExtendZero_coe,
      fderiv_ambientInverseIm_coe_apply_one]
    change (p.im ^ 2)⁻¹ * (horizontalDerivative f.toFun p * g p) =
      (p.im ^ 2)⁻¹ * horizontalDerivative f.toFun p * g p
    ring
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz,
      Pi.zero_apply, mul_zero]

/-- Horizontal frame integration by parts for smooth compact scalar fields. -/
theorem integral_mul_horizontalDerivative
    (f g : HyperbolicSmoothCompactScalar) :
    (∫ p, f p * horizontalDerivative g.toFun p ∂hyperbolicVolume) =
      -(∫ p, horizontalDerivative f.toFun p * g p ∂hyperbolicVolume) := by
  let fw := inverseImWeightedCore f
  let lhsCore := scalarProductCore f (horizontalDerivativeCore g)
  let rhsCore := scalarProductCore (horizontalDerivativeCore f) g
  have hibp :
      (∫ z, ambientExtendZero fw.toFun z *
        fderiv ℝ (ambientExtendZero g.toFun) z 1 ∂volume) =
      -(∫ z, fderiv ℝ (ambientExtendZero fw.toFun) z 1 *
        ambientExtendZero g.toFun z ∂volume) := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_fderiv_mul_ambient fw g 1
    · exact integrable_ambient_mul_fderiv fw g 1
    · exact integrable_ambient_mul_ambient fw g
    · intro z _
      exact (contDiff_ambientExtendZero fw).differentiable (by simp) z
    · intro z _
      exact (contDiff_ambientExtendZero g).differentiable (by simp) z
  change (∫ p, lhsCore p ∂hyperbolicVolume) =
    -(∫ p, rhsCore p ∂hyperbolicVolume)
  rw [integral_hyperbolic_eq_integral_ambientDensity lhsCore,
    integral_hyperbolic_eq_integral_ambientDensity rhsCore]
  calc
    (∫ z, ambientExtendZero (densityWeightedCore lhsCore).toFun z
        ∂volume) =
        ∫ z, ambientExtendZero fw.toFun z *
          fderiv ℝ (ambientExtendZero g.toFun) z 1 ∂volume :=
      integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ by
        exact ambient_horizontal_left f g z
    _ = -(∫ z, fderiv ℝ (ambientExtendZero fw.toFun) z 1 *
          ambientExtendZero g.toFun z ∂volume) := hibp
    _ = -(∫ z, ambientExtendZero (densityWeightedCore rhsCore).toFun z
          ∂volume) := by
      congr 1
      exact (integral_congr_ae <| Filter.Eventually.of_forall fun z ↦
        ambient_horizontal_right f g z).symm

theorem ambient_vertical_left
    (f g : HyperbolicSmoothCompactScalar) (z : ℂ) :
    ambientExtendZero
        (densityWeightedCore
          (scalarProductCore f (verticalDerivativeCore g))).toFun z =
      ambientExtendZero (inverseImWeightedCore f).toFun z *
        fderiv ℝ (ambientExtendZero g.toFun) z Complex.I := by
  by_cases hz : z ∈ Set.range ((↑) : HyperbolicPlane → ℂ)
  · rcases hz with ⟨p, rfl⟩
    rw [ambientExtendZero_coe, ambientExtendZero_coe,
      fderiv_ambientExtendZero_coe_apply_I]
    change (p.im ^ 2)⁻¹ * (f p * verticalDerivative g.toFun p) =
      p.im⁻¹ * f p * (p.im⁻¹ * verticalDerivative g.toFun p)
    field_simp [im_ne_zero p]
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz,
      Pi.zero_apply, zero_mul]

theorem ambient_vertical_right
    (f g : HyperbolicSmoothCompactScalar) (z : ℂ) :
    ambientExtendZero
        (densityWeightedCore
          (scalarProductCore (verticalDerivativeCore f - f) g)).toFun z =
      fderiv ℝ
          (ambientExtendZero (inverseImWeightedCore f).toFun) z Complex.I *
        ambientExtendZero g.toFun z := by
  by_cases hz : z ∈ Set.range ((↑) : HyperbolicPlane → ℂ)
  · rcases hz with ⟨p, rfl⟩
    rw [ambientExtendZero_coe, ambientExtendZero_coe,
      fderiv_ambientInverseIm_coe_apply_I]
    change (p.im ^ 2)⁻¹ *
        ((verticalDerivative f.toFun p - f p) * g p) =
      (p.im ^ 2)⁻¹ * (verticalDerivative f.toFun p - f p) * g p
    ring
  · simp only [ambientExtendZero, Function.extend_apply' _ _ _ hz,
      Pi.zero_apply, mul_zero]

/-- Vertical frame integration by parts, including the divergence correction
`div(e₂) = -1`. -/
theorem integral_mul_verticalDerivative
    (f g : HyperbolicSmoothCompactScalar) :
    (∫ p, f p * verticalDerivative g.toFun p ∂hyperbolicVolume) =
      -(∫ p, (verticalDerivative f.toFun p - f p) * g p ∂hyperbolicVolume) := by
  let fw := inverseImWeightedCore f
  let lhsCore := scalarProductCore f (verticalDerivativeCore g)
  let rhsCore := scalarProductCore (verticalDerivativeCore f - f) g
  have hibp :
      (∫ z, ambientExtendZero fw.toFun z *
        fderiv ℝ (ambientExtendZero g.toFun) z Complex.I ∂volume) =
      -(∫ z, fderiv ℝ (ambientExtendZero fw.toFun) z Complex.I *
        ambientExtendZero g.toFun z ∂volume) := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_fderiv_mul_ambient fw g Complex.I
    · exact integrable_ambient_mul_fderiv fw g Complex.I
    · exact integrable_ambient_mul_ambient fw g
    · intro z _
      exact (contDiff_ambientExtendZero fw).differentiable (by simp) z
    · intro z _
      exact (contDiff_ambientExtendZero g).differentiable (by simp) z
  change (∫ p, lhsCore p ∂hyperbolicVolume) =
    -(∫ p, rhsCore p ∂hyperbolicVolume)
  rw [integral_hyperbolic_eq_integral_ambientDensity lhsCore,
    integral_hyperbolic_eq_integral_ambientDensity rhsCore]
  calc
    (∫ z, ambientExtendZero (densityWeightedCore lhsCore).toFun z
        ∂volume) =
        ∫ z, ambientExtendZero fw.toFun z *
          fderiv ℝ (ambientExtendZero g.toFun) z Complex.I ∂volume :=
      integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ by
        exact ambient_vertical_left f g z
    _ = -(∫ z, fderiv ℝ (ambientExtendZero fw.toFun) z Complex.I *
          ambientExtendZero g.toFun z ∂volume) := hibp
    _ = -(∫ z, ambientExtendZero (densityWeightedCore rhsCore).toFun z
          ∂volume) := by
      congr 1
      exact (integral_congr_ae <| Filter.Eventually.of_forall fun z ↦
        ambient_vertical_right f g z).symm

end RiemannianFluids.HyperbolicPlane
