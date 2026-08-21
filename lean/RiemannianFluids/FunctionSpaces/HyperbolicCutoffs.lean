import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import RiemannianFluids.FunctionSpaces.HyperbolicFirstOrder

/-!
# Smooth complete-manifold cutoffs on the hyperbolic plane

This module constructs the concrete exhaustion used by the global CCP25 argument.  Instead of
formalizing smoothness of distance at the basepoint, it uses the smooth proper function

`r(x,y) = log ((x^2 + y^2 + 1) / y) = log (2 cosh (dist ((x,y), i)))`.

Its hyperbolic gradient has norm at most one.  Composing `r/R` with one fixed smooth Euclidean
bump therefore gives compactly supported smooth cutoffs whose first derivatives are `O(1/R)`.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Complex Function MeasureTheory Metric Set
open scoped ContDiff Manifold RealInnerProductSpace

/-- The canonical identification of a real vector space with its tangent space is pointwise the
identity.  Naming this fact avoids repeated elaboration problems around Mathlib's intentionally
opaque tangent-space instances. -/
theorem fromTangentSpace_real_apply (x : ℝ)
    (v : TangentSpace (modelWithCornersSelf ℝ ℝ) x) :
    NormedSpace.fromTangentSpace x v = v :=
  rfl

/-- Preferred basepoint `i` of the upper half-plane. -/
def hyperbolicCutoffBasepoint : HyperbolicPlane :=
  ⟨Complex.I, by simp⟩

@[simp] theorem hyperbolicCutoffBasepoint_re :
    (hyperbolicCutoffBasepoint : ℂ).re = 0 := by
  simp [hyperbolicCutoffBasepoint]

@[simp] theorem hyperbolicCutoffBasepoint_im :
    hyperbolicCutoffBasepoint.im = 1 := by
  simp [hyperbolicCutoffBasepoint, HyperbolicPlane.im]

/-- Twice the hyperbolic cosine of distance from the preferred basepoint, in smooth
upper-half-plane coordinates. -/
def hyperbolicExhaustionWeight (p : HyperbolicPlane) : ℝ :=
  (((p : ℂ).re ^ 2 + p.im ^ 2 + 1) / p.im)

theorem hyperbolicExhaustionWeight_pos (p : HyperbolicPlane) :
    0 < hyperbolicExhaustionWeight p := by
  unfold hyperbolicExhaustionWeight
  exact div_pos (by positivity) p.im_pos

theorem contMDiff_hyperbolicExhaustionWeight :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      hyperbolicExhaustionWeight := by
  have hre : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : HyperbolicPlane ↦ (p : ℂ).re) :=
    Complex.reCLM.contMDiff.comp contMDiff_coe
  exact (((hre.pow 2).add (contMDiff_im.pow 2)).add contMDiff_const).div₀
    contMDiff_im (fun p ↦ im_ne_zero p)

/-- The real coordinate differentiates to the real-part functional in the global chart. -/
theorem hasMFDerivAt_re (p : HyperbolicPlane) :
    HasMFDerivAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      (fun q : HyperbolicPlane ↦ (q : ℂ).re) p
      (Complex.reCLM : ℂ →L[ℝ] ℝ) := by
  have hre : HasMFDerivAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) Complex.re (p : ℂ)
      (Complex.reCLM : ℂ →L[ℝ] ℝ) :=
    Complex.reCLM.hasFDerivAt.hasMFDerivAt
  have h := hre.comp p (hasMFDerivAt_coe p)
  convert h using 1
  · rfl
  · exact (ContinuousLinearMap.comp_id (Complex.reCLM : ℂ →L[ℝ] ℝ)).symm

/-- Full chart formula for the derivative of the positive exhaustion weight. -/
theorem manifoldDerivativeFun_hyperbolicExhaustionWeight
    (p : HyperbolicPlane) (v : ℂ) :
    manifoldDerivativeFun hyperbolicExhaustionWeight p v =
      (2 * (p : ℂ).re / p.im) * v.re +
        ((p.im ^ 2 - (p : ℂ).re ^ 2 - 1) / p.im ^ 2) * v.im := by
  let x : HyperbolicPlane → ℝ := fun q ↦ (q : ℂ).re
  let y : HyperbolicPlane → ℝ := im
  have hx : HasMFDerivAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) x p
      (Complex.reCLM : ℂ →L[ℝ] ℝ) :=
    hasMFDerivAt_re p
  have hy : HasMFDerivAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) y p
      (Complex.imCLM : ℂ →L[ℝ] ℝ) :=
    hasMFDerivAt_im p
  have hnum := ((hx.mul hx).add (hy.mul hy)).add (hasMFDerivAt_const (1 : ℝ) p)
  have hweight := hnum.div hy (im_ne_zero p)
  have hderiv := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) hweight.mfderiv
  change manifoldDerivativeFun
      (fun q ↦ ((x q * x q + y q * y q) + 1) / y q) p v = _ at hderiv
  change manifoldDerivativeFun
      (fun q ↦ ((x q * x q + y q * y q) + 1) / y q) p v =
        (1 / y p) *
            (x p * v.re + x p * v.re + (y p * v.im + y p * v.im) + 0) -
          ((x p * x p + y p * y p + 1) / y p ^ 2) * v.im at hderiv
  have hfun : hyperbolicExhaustionWeight =
      (fun q ↦ ((x q * x q + y q * y q) + 1) / y q) := by
    funext q
    simp [hyperbolicExhaustionWeight, x, y, pow_two]
  rw [hfun]
  rw [hderiv]
  dsimp [x, y]
  field_simp [im_ne_zero p]
  ring

/-- Smooth proper exhaustion equivalent to radial distance. -/
def hyperbolicExhaustion (p : HyperbolicPlane) : ℝ :=
  Real.log (hyperbolicExhaustionWeight p)

theorem contMDiff_hyperbolicExhaustion :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      hyperbolicExhaustion := by
  intro p
  exact (Real.contDiffAt_log.2 (hyperbolicExhaustionWeight_pos p).ne').comp_contMDiffAt
    (contMDiff_hyperbolicExhaustionWeight p)

/-- Differentiating the logarithmic exhaustion multiplies the weight derivative by the
reciprocal weight. -/
theorem manifoldDerivativeFun_hyperbolicExhaustion
    (p : HyperbolicPlane) (v : ℂ) :
    manifoldDerivativeFun hyperbolicExhaustion p v =
      (hyperbolicExhaustionWeight p)⁻¹ *
        manifoldDerivativeFun hyperbolicExhaustionWeight p v := by
  let x : ℂ → ℝ := Complex.re
  let y : ℂ → ℝ := Complex.im
  let weight : ℂ → ℝ := fun z ↦
    (x z * x z + y z * y z + 1) * (y z)⁻¹
  have hx : HasFDerivAt x (Complex.reCLM : ℂ →L[ℝ] ℝ) (p : ℂ) :=
    Complex.reCLM.hasFDerivAt
  have hy : HasFDerivAt y (Complex.imCLM : ℂ →L[ℝ] ℝ) (p : ℂ) :=
    Complex.imCLM.hasFDerivAt
  have hnum := ((hx.mul hx).add (hy.mul hy)).add_const (1 : ℝ)
  have hyinv := (hasFDerivAt_inv (im_ne_zero p)).comp (p : ℂ) hy
  have hweight := hnum.mul hyinv
  have hlog := hweight.log (by
    change weight (p : ℂ) ≠ 0
    dsimp [weight, x, y]
    apply mul_ne_zero
    · nlinarith [sq_nonneg (p : ℂ).re, sq_nonneg (p : ℂ).im]
    · exact inv_ne_zero (im_ne_zero p))
  have hmanifold := hlog.hasMFDerivAt.comp p (hasMFDerivAt_coe p)
  let D : ℂ →L[ℝ] ℝ :=
    (weight (p : ℂ))⁻¹ •
      ((x (p : ℂ) * x (p : ℂ) + y (p : ℂ) * y (p : ℂ) + 1) •
          (ContinuousLinearMap.toSpanSingleton ℝ (-(y (p : ℂ) ^ 2)⁻¹)).comp
            (Complex.imCLM : ℂ →L[ℝ] ℝ) +
        (y (p : ℂ))⁻¹ •
          (x (p : ℂ) • (Complex.reCLM : ℂ →L[ℝ] ℝ) +
            x (p : ℂ) • (Complex.reCLM : ℂ →L[ℝ] ℝ) +
            (y (p : ℂ) • (Complex.imCLM : ℂ →L[ℝ] ℝ) +
              y (p : ℂ) • (Complex.imCLM : ℂ →L[ℝ] ℝ))))
  have hmanifold' : HasMFDerivAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ)
      ((fun z ↦ Real.log (weight z)) ∘ ((↑) : HyperbolicPlane → ℂ)) p D := by
    convert hmanifold using 1
    · rfl
    · exact (ContinuousLinearMap.comp_id D).symm
  have hderiv := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) hmanifold'.mfderiv
  dsimp [D] at hderiv
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul] at hderiv
  change manifoldDerivativeFun
      ((fun z ↦ Real.log (weight z)) ∘ ((↑) : HyperbolicPlane → ℂ)) p v =
        (weight (p : ℂ))⁻¹ *
          ((x (p : ℂ) * x (p : ℂ) + y (p : ℂ) * y (p : ℂ) + 1) *
              (v.im * -(y (p : ℂ) ^ 2)⁻¹) +
            (y (p : ℂ))⁻¹ *
              (x (p : ℂ) * v.re + x (p : ℂ) * v.re +
                (y (p : ℂ) * v.im + y (p : ℂ) * v.im))) at hderiv
  have hfun : hyperbolicExhaustion =
      ((fun z ↦ Real.log (weight z)) ∘ ((↑) : HyperbolicPlane → ℂ)) := by
    funext q
    change Real.log
        ((((q : ℂ).re ^ 2 + (q : ℂ).im ^ 2 + 1) / (q : ℂ).im)) =
      Real.log (((q : ℂ).re * (q : ℂ).re +
        (q : ℂ).im * (q : ℂ).im + 1) * ((q : ℂ).im)⁻¹)
    congr 1
    rw [div_eq_mul_inv]
    ring
  rw [hfun, hderiv, manifoldDerivativeFun_hyperbolicExhaustionWeight]
  dsimp [weight, x, y]
  rw [hyperbolicExhaustionWeight]
  have hre : UpperHalfPlane.re p = (p : ℂ).re := rfl
  have him : UpperHalfPlane.im p = p.im := rfl
  rw [hre, him]
  field_simp [im_ne_zero p]
  ring

/-- Exact horizontal-frame derivative of the smooth radial exhaustion. -/
theorem horizontalDerivative_hyperbolicExhaustion (p : HyperbolicPlane) :
    horizontalDerivative hyperbolicExhaustion p =
      2 * (p : ℂ).re * p.im /
        ((p : ℂ).re ^ 2 + p.im ^ 2 + 1) := by
  rw [horizontalDerivative, manifoldDerivativeFun_hyperbolicExhaustion,
    manifoldDerivativeFun_hyperbolicExhaustionWeight]
  simp only [horizontalFrameVector, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero]
  rw [hyperbolicExhaustionWeight]
  field_simp [im_ne_zero p]

/-- Exact vertical-frame derivative of the smooth radial exhaustion. -/
theorem verticalDerivative_hyperbolicExhaustion (p : HyperbolicPlane) :
    verticalDerivative hyperbolicExhaustion p =
      (p.im ^ 2 - (p : ℂ).re ^ 2 - 1) /
        ((p : ℂ).re ^ 2 + p.im ^ 2 + 1) := by
  rw [verticalDerivative, manifoldDerivativeFun_hyperbolicExhaustion,
    manifoldDerivativeFun_hyperbolicExhaustionWeight]
  simp only [verticalFrameVector, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    sub_zero]
  rw [hyperbolicExhaustionWeight]
  field_simp [im_ne_zero p]
  ring

/-- The smooth exhaustion has hyperbolic frame-gradient norm at most one.  This is the
quantitative completeness estimate needed by the Gaffney cutoff argument. -/
theorem hyperbolicExhaustion_frameGradient_sq_le_one (p : HyperbolicPlane) :
    horizontalDerivative hyperbolicExhaustion p ^ 2 +
        verticalDerivative hyperbolicExhaustion p ^ 2 ≤ 1 := by
  rw [horizontalDerivative_hyperbolicExhaustion,
    verticalDerivative_hyperbolicExhaustion]
  let x := (p : ℂ).re
  let y := p.im
  let D := x ^ 2 + y ^ 2 + 1
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hid : (2 * x * y) ^ 2 + (y ^ 2 - x ^ 2 - 1) ^ 2 + 4 * y ^ 2 = D ^ 2 := by
    dsimp [D]
    ring
  have hnum : (2 * x * y) ^ 2 + (y ^ 2 - x ^ 2 - 1) ^ 2 ≤ D ^ 2 := by
    nlinarith [sq_nonneg y]
  calc
    (2 * x * y / D) ^ 2 + ((y ^ 2 - x ^ 2 - 1) / D) ^ 2 =
        ((2 * x * y) ^ 2 + (y ^ 2 - x ^ 2 - 1) ^ 2) / D ^ 2 := by
          field_simp [hD.ne']
    _ ≤ 1 := (div_le_one (sq_pos_of_pos hD)).2 hnum

theorem abs_horizontalDerivative_hyperbolicExhaustion_le_one
    (p : HyperbolicPlane) :
    |horizontalDerivative hyperbolicExhaustion p| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  nlinarith [hyperbolicExhaustion_frameGradient_sq_le_one p,
    sq_nonneg (verticalDerivative hyperbolicExhaustion p)]

theorem abs_verticalDerivative_hyperbolicExhaustion_le_one
    (p : HyperbolicPlane) :
    |verticalDerivative hyperbolicExhaustion p| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  nlinarith [hyperbolicExhaustion_frameGradient_sq_le_one p,
    sq_nonneg (horizontalDerivative hyperbolicExhaustion p)]

theorem hyperbolicExhaustionWeight_eq_two_mul_cosh_dist
    (p : HyperbolicPlane) :
    hyperbolicExhaustionWeight p =
      2 * Real.cosh (dist p hyperbolicCutoffBasepoint) := by
  rw [UpperHalfPlane.cosh_dist']
  simp only [hyperbolicExhaustionWeight, hyperbolicCutoffBasepoint,
    HyperbolicPlane.im, UpperHalfPlane.re, UpperHalfPlane.im, Complex.I_re,
    Complex.I_im, sub_zero, one_pow, mul_one]
  field_simp [im_ne_zero p]

/-- The smooth exhaustion dominates genuine hyperbolic distance from the basepoint. -/
theorem dist_le_hyperbolicExhaustion (p : HyperbolicPlane) :
    dist p hyperbolicCutoffBasepoint ≤ hyperbolicExhaustion p := by
  let d := dist p hyperbolicCutoffBasepoint
  have hdexp : Real.exp d ≤ hyperbolicExhaustionWeight p := by
    rw [hyperbolicExhaustionWeight_eq_two_mul_cosh_dist]
    change Real.exp d ≤ 2 * Real.cosh d
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-d)]
  have hlog : Real.exp (hyperbolicExhaustion p) =
      hyperbolicExhaustionWeight p := by
    exact Real.exp_log (hyperbolicExhaustionWeight_pos p)
  apply Real.exp_le_exp.mp
  rw [hlog]
  exact hdexp

theorem hyperbolicExhaustion_nonneg (p : HyperbolicPlane) :
    0 ≤ hyperbolicExhaustion p :=
  (dist_nonneg.trans (dist_le_hyperbolicExhaustion p))

/-- A fixed scalar bump, equal to one on `[-1,1]` and supported in `(-2,2)`. -/
def hyperbolicRadialBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

theorem exists_hyperbolicRadialBumpDerivativeBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv hyperbolicRadialBump t| ≤ C := by
  obtain ⟨C, hC⟩ :=
    ((hyperbolicRadialBump.contDiff (n := ⊤)).continuous_deriv (by simp)).bounded_above_of_compact_support
      hyperbolicRadialBump.hasCompactSupport.deriv
  refine ⟨C, ?_, ?_⟩
  · exact (norm_nonneg (deriv hyperbolicRadialBump 0)).trans (hC 0)
  · intro t
    simpa [Real.norm_eq_abs] using hC t

/-- One global bound for the derivative of the fixed one-dimensional profile. -/
noncomputable def hyperbolicRadialBumpDerivativeBound : ℝ :=
  Classical.choose exists_hyperbolicRadialBumpDerivativeBound

theorem hyperbolicRadialBumpDerivativeBound_nonneg :
    0 ≤ hyperbolicRadialBumpDerivativeBound :=
  (Classical.choose_spec exists_hyperbolicRadialBumpDerivativeBound).1

theorem abs_deriv_hyperbolicRadialBump_le (t : ℝ) :
    |deriv hyperbolicRadialBump t| ≤ hyperbolicRadialBumpDerivativeBound :=
  (Classical.choose_spec exists_hyperbolicRadialBumpDerivativeBound).2 t

/-- Radius-`R` cutoff obtained from the smooth exhaustion. -/
def hyperbolicCutoff (R : ℝ) (p : HyperbolicPlane) : ℝ :=
  hyperbolicRadialBump (hyperbolicExhaustion p / R)

theorem contMDiff_hyperbolicCutoff (R : ℝ) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      (hyperbolicCutoff R) := by
  change ContMDiff (modelWithCornersSelf ℝ ℂ)
    (modelWithCornersSelf ℝ ℝ) ∞
    (hyperbolicRadialBump ∘ fun p ↦ hyperbolicExhaustion p / R)
  exact hyperbolicRadialBump.contDiff.comp_contMDiff
    (contMDiff_hyperbolicExhaustion.div_const R)

/-- Dividing a scalar field by a constant divides every directional derivative by the same
constant. -/
theorem manifoldDerivativeFun_hyperbolicExhaustion_div
    (R : ℝ) (p : HyperbolicPlane) (v : ℂ) :
    manifoldDerivativeFun (fun q ↦ hyperbolicExhaustion q / R) p v =
      manifoldDerivativeFun hyperbolicExhaustion p v / R := by
  have hr : MDifferentiableAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) hyperbolicExhaustion p :=
    (contMDiff_hyperbolicExhaustion p).mdifferentiableAt (by simp)
  have hconst : MDifferentiableAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) (fun _ : HyperbolicPlane ↦ R⁻¹) p :=
    mdifferentiableAt_const
  have h := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
    (mvfderiv_mul hconst hr)
  change manifoldDerivativeFun
      ((fun _ : HyperbolicPlane ↦ R⁻¹) * hyperbolicExhaustion) p v = _ at h
  have hfun : (fun q : HyperbolicPlane ↦ hyperbolicExhaustion q / R) =
      (fun _ : HyperbolicPlane ↦ R⁻¹) * hyperbolicExhaustion := by
    funext q
    simp [div_eq_mul_inv, mul_comm]
  rw [mvfderiv_const] at h
  simp only [smul_zero, add_zero] at h
  rw [hfun, h]
  set_option backward.isDefEq.respectTransparency false in
    change R⁻¹ * manifoldDerivativeFun hyperbolicExhaustion p v = _
  simp [div_eq_mul_inv, mul_comm]

/-- Chain rule from a manifold scalar field into an ordinary Fréchet-differentiable scalar
function, stated for the vector-valued derivative so no target-tangent identification leaks into
later estimates. -/
theorem manifoldDerivativeFun_comp_hasFDerivAt
    {f : HyperbolicPlane → ℝ} {g : ℝ → ℝ} {g' : ℝ →L[ℝ] ℝ}
    (p : HyperbolicPlane) (v : ℂ)
    (hf : MDifferentiableAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) f p)
    (hg : HasFDerivAt g g' (f p)) :
    manifoldDerivativeFun (g ∘ f) p v = g' (manifoldDerivativeFun f p v) := by
  have hcomp := hg.hasMFDerivAt.comp p hf.hasMFDerivAt
  rw [manifoldDerivativeFun, mvfderiv, hcomp.mfderiv]
  change NormedSpace.fromTangentSpace (𝕜 := ℝ) (g (f p))
      (g' ((mfderiv (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℝ) f p) v)) =
    g' (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f p)
      ((mfderiv (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ ℝ) f p) v))
  rw [fromTangentSpace_real_apply, fromTangentSpace_real_apply]

/-- Chain rule for the cutoff profile along any chart tangent vector. -/
theorem manifoldDerivativeFun_hyperbolicCutoff
    (R : ℝ) (p : HyperbolicPlane) (v : ℂ) :
    manifoldDerivativeFun (hyperbolicCutoff R) p v =
      deriv hyperbolicRadialBump (hyperbolicExhaustion p / R) *
        (manifoldDerivativeFun hyperbolicExhaustion p v / R) := by
  let scaled : HyperbolicPlane → ℝ := fun q ↦ hyperbolicExhaustion q / R
  have hscaled : MDifferentiableAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℝ) scaled p :=
    ((contMDiff_hyperbolicExhaustion.div_const R) p).mdifferentiableAt (by simp)
  have hbumpDiff : DifferentiableAt ℝ (hyperbolicRadialBump : ℝ → ℝ) (scaled p) :=
    (hyperbolicRadialBump.contDiff (n := ⊤)).differentiable (by simp) (scaled p)
  have hchain := manifoldDerivativeFun_comp_hasFDerivAt p v hscaled
    hbumpDiff.hasDerivAt.hasFDerivAt
  have hchain' : manifoldDerivativeFun (hyperbolicRadialBump ∘ scaled) p v =
      deriv hyperbolicRadialBump (scaled p) *
        manifoldDerivativeFun scaled p v := by
    simpa [smul_eq_mul, mul_comm] using hchain
  have hfun : hyperbolicCutoff R = hyperbolicRadialBump ∘ scaled := rfl
  rw [hfun, hchain']
  exact congrArg (fun z ↦ deriv hyperbolicRadialBump (scaled p) * z)
    (manifoldDerivativeFun_hyperbolicExhaustion_div R p v)

theorem horizontalDerivative_hyperbolicCutoff (R : ℝ) (p : HyperbolicPlane) :
    horizontalDerivative (hyperbolicCutoff R) p =
      deriv hyperbolicRadialBump (hyperbolicExhaustion p / R) *
        (horizontalDerivative hyperbolicExhaustion p / R) := by
  simpa [horizontalDerivative] using
    manifoldDerivativeFun_hyperbolicCutoff R p (horizontalFrameVector p)

theorem verticalDerivative_hyperbolicCutoff (R : ℝ) (p : HyperbolicPlane) :
    verticalDerivative (hyperbolicCutoff R) p =
      deriv hyperbolicRadialBump (hyperbolicExhaustion p / R) *
        (verticalDerivative hyperbolicExhaustion p / R) := by
  simpa [verticalDerivative] using
    manifoldDerivativeFun_hyperbolicCutoff R p (verticalFrameVector p)

/-- Each frame derivative of the radius-`R` cutoff is bounded by one fixed constant divided by
`R`; in particular the cutoff gradients vanish uniformly as `R → ∞`. -/
theorem abs_horizontalDerivative_hyperbolicCutoff_le
    (R : ℝ) (hR : 0 < R) (p : HyperbolicPlane) :
    |horizontalDerivative (hyperbolicCutoff R) p| ≤
      hyperbolicRadialBumpDerivativeBound / R := by
  rw [horizontalDerivative_hyperbolicCutoff, abs_mul, abs_div, abs_of_pos hR]
  have hscaled : |horizontalDerivative hyperbolicExhaustion p| / R ≤ 1 / R :=
    div_le_div_of_nonneg_right
      (abs_horizontalDerivative_hyperbolicExhaustion_le_one p) hR.le
  calc
    |deriv hyperbolicRadialBump (hyperbolicExhaustion p / R)| *
        (|horizontalDerivative hyperbolicExhaustion p| / R) ≤
      hyperbolicRadialBumpDerivativeBound * (1 / R) :=
        mul_le_mul
          (abs_deriv_hyperbolicRadialBump_le (hyperbolicExhaustion p / R))
          hscaled
          (div_nonneg (abs_nonneg _) hR.le)
          hyperbolicRadialBumpDerivativeBound_nonneg
    _ = hyperbolicRadialBumpDerivativeBound / R := by ring

theorem abs_verticalDerivative_hyperbolicCutoff_le
    (R : ℝ) (hR : 0 < R) (p : HyperbolicPlane) :
    |verticalDerivative (hyperbolicCutoff R) p| ≤
      hyperbolicRadialBumpDerivativeBound / R := by
  rw [verticalDerivative_hyperbolicCutoff, abs_mul, abs_div, abs_of_pos hR]
  have hscaled : |verticalDerivative hyperbolicExhaustion p| / R ≤ 1 / R :=
    div_le_div_of_nonneg_right
      (abs_verticalDerivative_hyperbolicExhaustion_le_one p) hR.le
  calc
    |deriv hyperbolicRadialBump (hyperbolicExhaustion p / R)| *
        (|verticalDerivative hyperbolicExhaustion p| / R) ≤
      hyperbolicRadialBumpDerivativeBound * (1 / R) :=
        mul_le_mul
          (abs_deriv_hyperbolicRadialBump_le (hyperbolicExhaustion p / R))
          hscaled
          (div_nonneg (abs_nonneg _) hR.le)
          hyperbolicRadialBumpDerivativeBound_nonneg
    _ = hyperbolicRadialBumpDerivativeBound / R := by ring

theorem hyperbolicCutoff_nonneg (R : ℝ) (p : HyperbolicPlane) :
    0 ≤ hyperbolicCutoff R p :=
  hyperbolicRadialBump.nonneg

theorem hyperbolicCutoff_le_one (R : ℝ) (p : HyperbolicPlane) :
    hyperbolicCutoff R p ≤ 1 :=
  hyperbolicRadialBump.le_one

/-- The radius-`R` cutoff is supported in the genuine hyperbolic ball of radius `2R`. -/
theorem support_hyperbolicCutoff_subset_ball (R : ℝ) (hR : 0 < R) :
    support (hyperbolicCutoff R) ⊆
      Metric.ball hyperbolicCutoffBasepoint (2 * R) := by
  intro p hp
  have harg : hyperbolicExhaustion p / R ∈ Metric.ball (0 : ℝ) 2 := by
    have hbump : hyperbolicExhaustion p / R ∈ support hyperbolicRadialBump := by
      exact hp
    rw [hyperbolicRadialBump.support_eq] at hbump
    simpa [hyperbolicRadialBump] using hbump
  have habs : |hyperbolicExhaustion p / R| < 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using harg
  have hratio : hyperbolicExhaustion p / R < 2 :=
    lt_of_le_of_lt (le_abs_self _) habs
  have hexhaustion : hyperbolicExhaustion p < 2 * R :=
    (div_lt_iff₀ hR).mp hratio
  exact lt_of_le_of_lt (dist_le_hyperbolicExhaustion p) hexhaustion

/-- The concrete cutoff has compact support because the hyperbolic metric is proper. -/
theorem hasCompactSupport_hyperbolicCutoff (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (hyperbolicCutoff R) := by
  apply (isCompact_closedBall hyperbolicCutoffBasepoint (2 * R)).of_isClosed_subset
    isClosed_closure
  exact closure_minimal
    ((support_hyperbolicCutoff_subset_ball R hR).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

/-- The cutoff is identically one on the exhaustion sublevel `r ≤ R`. -/
theorem hyperbolicCutoff_eq_one_of_exhaustion_le
    (R : ℝ) (hR : 0 < R) (p : HyperbolicPlane)
    (hp : hyperbolicExhaustion p ≤ R) :
    hyperbolicCutoff R p = 1 := by
  apply hyperbolicRadialBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (hyperbolicExhaustion_nonneg p) hR.le)]
  exact (div_le_one hR).2 hp

/-- The radius-`R` cutoff as an element of the actual smooth compact scalar core. -/
noncomputable def hyperbolicCutoffCore (R : ℝ) (hR : 0 < R) :
    HyperbolicSmoothCompactScalar :=
  ⟨hyperbolicCutoff R, contMDiff_hyperbolicCutoff R,
    hasCompactSupport_hyperbolicCutoff R hR⟩

@[simp] theorem hyperbolicCutoffCore_apply
    (R : ℝ) (hR : 0 < R) (p : HyperbolicPlane) :
    hyperbolicCutoffCore R hR p = hyperbolicCutoff R p :=
  rfl

/-- Canonical integer-indexed complete-manifold cutoff exhaustion. -/
noncomputable def hyperbolicCutoffCoreSequence (n : ℕ) :
    HyperbolicSmoothCompactScalar :=
  hyperbolicCutoffCore ((n : ℝ) + 1) (by positivity)

@[simp] theorem hyperbolicCutoffCoreSequence_apply
    (n : ℕ) (p : HyperbolicPlane) :
    hyperbolicCutoffCoreSequence n p =
      hyperbolicCutoff ((n : ℝ) + 1) p :=
  rfl

/-- Every point eventually lies in the region where the canonical cutoff is exactly one. -/
theorem eventually_hyperbolicCutoffCoreSequence_eq_one (p : HyperbolicPlane) :
    (fun n ↦ hyperbolicCutoffCoreSequence n p) =ᶠ[Filter.atTop]
      (fun _ : ℕ ↦ 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (hyperbolicExhaustion p)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [hyperbolicCutoffCoreSequence_apply]
  apply hyperbolicCutoff_eq_one_of_exhaustion_le ((n : ℝ) + 1) (by positivity) p
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem tendsto_hyperbolicCutoffCoreSequence_apply (p : HyperbolicPlane) :
    Filter.Tendsto (fun n ↦ hyperbolicCutoffCoreSequence n p)
      Filter.atTop (nhds 1) :=
  (eventually_hyperbolicCutoffCoreSequence_eq_one p).tendsto

/-- The uniform first-derivative envelope of the canonical cutoff sequence tends to zero. -/
theorem tendsto_hyperbolicCutoffDerivativeBound :
    Filter.Tendsto
      (fun n : ℕ ↦ hyperbolicRadialBumpDerivativeBound / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      hyperbolicRadialBumpDerivativeBound

end RiemannianFluids.HyperbolicPlane
