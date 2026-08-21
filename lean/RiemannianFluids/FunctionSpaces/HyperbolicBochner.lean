import RiemannianFluids.FunctionSpaces.HyperbolicSobolev
import Mathlib.Analysis.Calculus.VectorField

/-!
# Bochner--Weitzenbock identity on the complete hyperbolic plane

This module proves the curvature-sensitive identity on the compactly supported smooth
one-form core of the upper-half-plane model:

`‖∇ alpha‖₂² = ‖d alpha‖₂² + ‖delta alpha‖₂² + ‖alpha‖₂²`.

The proof is internal to the concrete frame calculus.  Its only global analytic input is the
hyperbolic integration-by-parts theorem already proved for compactly supported fields.  This is
the `N = 2`, `k = 1`, curvature `-1` specialization of the identity used by CCP25 to identify
the covariant `H¹` norm with a weighted Hodge graph norm.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Complex Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate ContDiff RealInnerProductSpace

noncomputable def ambientHorizontalFrameCLM : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.imCLM

noncomputable def ambientHorizontalFrame : ℂ → ℂ :=
  ambientHorizontalFrameCLM

noncomputable def ambientVerticalFrameCLM : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp ambientHorizontalFrameCLM

noncomputable def ambientVerticalFrame : ℂ → ℂ :=
  ambientVerticalFrameCLM

theorem fderiv_ambientHorizontalFrame (z : ℂ) :
    fderiv ℝ ambientHorizontalFrame z = Complex.ofRealCLM.comp Complex.imCLM := by
  rw [ambientHorizontalFrame, ContinuousLinearMap.fderiv]
  rfl

theorem fderiv_ambientVerticalFrame (z : ℂ) :
    fderiv ℝ ambientVerticalFrame z =
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp
        (Complex.ofRealCLM.comp Complex.imCLM) := by
  rw [ambientVerticalFrame, ContinuousLinearMap.fderiv]
  rfl

theorem lieBracket_ambientFrames (z : ℂ) :
    VectorField.lieBracket ℝ ambientHorizontalFrame ambientVerticalFrame z =
      -ambientHorizontalFrame z := by
  rw [VectorField.lieBracket, fderiv_ambientHorizontalFrame,
    fderiv_ambientVerticalFrame]
  simp [ambientHorizontalFrame, ambientVerticalFrame,
    ambientHorizontalFrameCLM, ambientVerticalFrameCLM]

theorem ambientHorizontalFrame_coe (p : HyperbolicPlane) :
    ambientHorizontalFrame (p : ℂ) = horizontalFrameVector p := by
  simp [ambientHorizontalFrame, ambientHorizontalFrameCLM,
    horizontalFrameVector, UpperHalfPlane.coe_im]
  exact p.coe_im.symm

theorem ambientVerticalFrame_coe (p : HyperbolicPlane) :
    ambientVerticalFrame (p : ℂ) = verticalFrameVector p := by
  simp [ambientVerticalFrame, ambientVerticalFrameCLM,
    ambientHorizontalFrameCLM, verticalFrameVector, UpperHalfPlane.coe_im,
    mul_comm]
  exact p.coe_im.symm

theorem ambientExtendZero_horizontalDerivative_eventuallyEq
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    ambientExtendZero (horizontalDerivativeCore f).toFun =ᶠ[𝓝 (p : ℂ)]
      fun z ↦ fderiv ℝ (ambientExtendZero f.toFun) z
        (ambientHorizontalFrame z) := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos]
    with z hz
  let q : HyperbolicPlane := ⟨z, hz⟩
  change ambientExtendZero (horizontalDerivativeCore f).toFun (q : ℂ) =
    fderiv ℝ (ambientExtendZero f.toFun) (q : ℂ)
      (ambientHorizontalFrame (q : ℂ))
  rw [ambientExtendZero_coe, fderiv_ambientExtendZero_coe]
  rfl

theorem ambientExtendZero_verticalDerivative_eventuallyEq
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    ambientExtendZero (verticalDerivativeCore f).toFun =ᶠ[𝓝 (p : ℂ)]
      fun z ↦ fderiv ℝ (ambientExtendZero f.toFun) z
        (ambientVerticalFrame z) := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos]
    with z hz
  let q : HyperbolicPlane := ⟨z, hz⟩
  change ambientExtendZero (verticalDerivativeCore f).toFun (q : ℂ) =
    fderiv ℝ (ambientExtendZero f.toFun) (q : ℂ)
      (ambientVerticalFrame (q : ℂ))
  rw [ambientExtendZero_coe, fderiv_ambientExtendZero_coe]
  simp [verticalDerivativeCore, verticalDerivative, verticalFrameVector,
    ambientVerticalFrame, ambientVerticalFrameCLM, ambientHorizontalFrameCLM]
  rw [mul_comm]
  rfl

theorem frameDerivative_commutator
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    horizontalDerivative (verticalDerivativeCore f).toFun p -
        verticalDerivative (horizontalDerivativeCore f).toFun p =
      -horizontalDerivative f.toFun p := by
  have htwo_le : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hn : minSmoothness ℝ (2 : ℕ∞ω) ≤ ∞ := by
    simpa using htwo_le
  have h := VectorField.fderiv_apply_lieBracket
    (n := ∞)
    (x := (p : ℂ))
    (V := ambientHorizontalFrame) (W := ambientVerticalFrame)
    (contDiff_ambientExtendZero f).contDiffAt
    hn
    (ambientVerticalFrameCLM.differentiableAt)
    (ambientHorizontalFrameCLM.differentiableAt)
  rw [lieBracket_ambientFrames] at h
  rw [← (ambientExtendZero_verticalDerivative_eventuallyEq f p).fderiv_eq,
    ← (ambientExtendZero_horizontalDerivative_eventuallyEq f p).fderiv_eq] at h
  simp_rw [fderiv_ambientExtendZero_coe] at h
  simp_rw [ambientHorizontalFrame_coe, ambientVerticalFrame_coe] at h
  simpa [horizontalDerivative, verticalDerivative] using h.symm

theorem integral_sub_mul
    (f g h : HyperbolicSmoothCompactScalar) :
    (∫ p, (f p - g p) * h p ∂hyperbolicVolume) =
      (∫ p, f p * h p ∂hyperbolicVolume) -
        ∫ p, g p * h p ∂hyperbolicVolume := by
  rw [← integral_sub
    (integrable_smoothCompact_product f h)
    (integrable_smoothCompact_product g h)]
  apply integral_congr_ae
  filter_upwards with p
  ring

theorem integral_mixed_cross_zero
    (a b : HyperbolicSmoothCompactScalar) :
    (∫ p, horizontalDerivative b.toFun p * verticalDerivative a.toFun p -
        horizontalDerivative a.toFun p * verticalDerivative b.toFun p
      ∂hyperbolicVolume) = 0 := by
  let X := ∫ p, horizontalDerivative b.toFun p * verticalDerivative a.toFun p
    ∂hyperbolicVolume
  let Y := ∫ p, horizontalDerivative a.toFun p * verticalDerivative b.toFun p
    ∂hyperbolicVolume
  let A := ∫ p, horizontalDerivative (verticalDerivativeCore a).toFun p * b p
    ∂hyperbolicVolume
  let B := ∫ p, horizontalDerivative (verticalDerivativeCore b).toFun p * a p
    ∂hyperbolicVolume
  let C := ∫ p, verticalDerivative (horizontalDerivativeCore a).toFun p * b p
    ∂hyperbolicVolume
  let D := ∫ p, horizontalDerivative a.toFun p * b p ∂hyperbolicVolume
  let E := ∫ p, verticalDerivative (horizontalDerivativeCore b).toFun p * a p
    ∂hyperbolicVolume
  let F := ∫ p, horizontalDerivative b.toFun p * a p ∂hyperbolicVolume
  have hX : X = -A := by
    dsimp only [X, A]
    calc
      (∫ p, horizontalDerivative b.toFun p * verticalDerivative a.toFun p
          ∂hyperbolicVolume) =
          ∫ p, verticalDerivative a.toFun p * horizontalDerivative b.toFun p
            ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = -(∫ p, horizontalDerivative (verticalDerivativeCore a).toFun p * b p
            ∂hyperbolicVolume) :=
        integral_mul_horizontalDerivative (verticalDerivativeCore a) b
  have hY : Y = -B := by
    dsimp only [Y, B]
    calc
      (∫ p, horizontalDerivative a.toFun p * verticalDerivative b.toFun p
          ∂hyperbolicVolume) =
          ∫ p, verticalDerivative b.toFun p * horizontalDerivative a.toFun p
            ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = -(∫ p, horizontalDerivative (verticalDerivativeCore b).toFun p * a p
            ∂hyperbolicVolume) :=
        integral_mul_horizontalDerivative (verticalDerivativeCore b) a
  have hA : A = C - D := by
    dsimp only [A, C, D]
    calc
      (∫ p, horizontalDerivative (verticalDerivativeCore a).toFun p * b p
          ∂hyperbolicVolume) =
          ∫ p, (verticalDerivative (horizontalDerivativeCore a).toFun p -
            horizontalDerivative a.toFun p) * b p ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        have hcomm := frameDerivative_commutator a p
        congr 1
        linarith
      _ = (∫ p, verticalDerivative (horizontalDerivativeCore a).toFun p * b p
            ∂hyperbolicVolume) -
          ∫ p, horizontalDerivative a.toFun p * b p ∂hyperbolicVolume :=
        integral_sub_mul
          (verticalDerivativeCore (horizontalDerivativeCore a))
          (horizontalDerivativeCore a) b
  have hB : B = E - F := by
    dsimp only [B, E, F]
    calc
      (∫ p, horizontalDerivative (verticalDerivativeCore b).toFun p * a p
          ∂hyperbolicVolume) =
          ∫ p, (verticalDerivative (horizontalDerivativeCore b).toFun p -
            horizontalDerivative b.toFun p) * a p ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        have hcomm := frameDerivative_commutator b p
        congr 1
        linarith
      _ = (∫ p, verticalDerivative (horizontalDerivativeCore b).toFun p * a p
            ∂hyperbolicVolume) -
          ∫ p, horizontalDerivative b.toFun p * a p ∂hyperbolicVolume :=
        integral_sub_mul
          (verticalDerivativeCore (horizontalDerivativeCore b))
          (horizontalDerivativeCore b) a
  have hC : C = -(Y - D) := by
    have hv := integral_mul_verticalDerivative b (horizontalDerivativeCore a)
    have hsplit :
        (∫ p, (verticalDerivative b.toFun p - b p) *
          horizontalDerivative a.toFun p ∂hyperbolicVolume) = Y - D := by
      calc
        _ = (∫ p, verticalDerivative b.toFun p *
              horizontalDerivative a.toFun p ∂hyperbolicVolume) -
            ∫ p, b p * horizontalDerivative a.toFun p
              ∂hyperbolicVolume :=
          integral_sub_mul (verticalDerivativeCore b) b
            (horizontalDerivativeCore a)
        _ = Y - D := by
          congr 1 <;> apply integral_congr_ae <;> filter_upwards with p <;> ring
    dsimp only [C]
    calc
      (∫ p, verticalDerivative (horizontalDerivativeCore a).toFun p * b p
          ∂hyperbolicVolume) =
          ∫ p, b p * verticalDerivative (horizontalDerivativeCore a).toFun p
            ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = -(∫ p, (verticalDerivative b.toFun p - b p) *
            horizontalDerivative a.toFun p ∂hyperbolicVolume) := hv
      _ = -(Y - D) := by rw [hsplit]
  have hE : E = -(X - F) := by
    have hv := integral_mul_verticalDerivative a (horizontalDerivativeCore b)
    have hsplit :
        (∫ p, (verticalDerivative a.toFun p - a p) *
          horizontalDerivative b.toFun p ∂hyperbolicVolume) = X - F := by
      calc
        _ = (∫ p, verticalDerivative a.toFun p *
              horizontalDerivative b.toFun p ∂hyperbolicVolume) -
            ∫ p, a p * horizontalDerivative b.toFun p
              ∂hyperbolicVolume :=
          integral_sub_mul (verticalDerivativeCore a) a
            (horizontalDerivativeCore b)
        _ = X - F := by
          congr 1 <;> apply integral_congr_ae <;> filter_upwards with p <;> ring
    dsimp only [E]
    calc
      (∫ p, verticalDerivative (horizontalDerivativeCore b).toFun p * a p
          ∂hyperbolicVolume) =
          ∫ p, a p * verticalDerivative (horizontalDerivativeCore b).toFun p
            ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = -(∫ p, (verticalDerivative a.toFun p - a p) *
            horizontalDerivative b.toFun p ∂hyperbolicVolume) := hv
      _ = -(X - F) := by rw [hsplit]
  have hXY : X - Y = 0 := by
    linarith only [hX, hY, hA, hB, hC, hE]
  calc
    (∫ p, horizontalDerivative b.toFun p * verticalDerivative a.toFun p -
        horizontalDerivative a.toFun p * verticalDerivative b.toFun p
        ∂hyperbolicVolume) = X - Y := by
      dsimp only [X, Y]
      have hIntX : Integrable (fun p ↦ horizontalDerivative b.toFun p *
          verticalDerivative a.toFun p) hyperbolicVolume := by
        exact integrable_smoothCompact_product
          (horizontalDerivativeCore b) (verticalDerivativeCore a)
      have hIntY : Integrable (fun p ↦ horizontalDerivative a.toFun p *
          verticalDerivative b.toFun p) hyperbolicVolume := by
        exact integrable_smoothCompact_product
          (horizontalDerivativeCore a) (verticalDerivativeCore b)
      rw [integral_sub hIntX hIntY]
    _ = 0 := hXY

theorem two_mul_integral_mul_verticalDerivative_self
    (f : HyperbolicSmoothCompactScalar) :
    2 * (∫ p, f p * verticalDerivative f.toFun p ∂hyperbolicVolume) =
      ∫ p, f p * f p ∂hyperbolicVolume := by
  have h := integral_mul_verticalDerivative f f
  have hcomm :
      (∫ p, f p * verticalDerivative f.toFun p ∂hyperbolicVolume) =
        ∫ p, verticalDerivative f.toFun p * f p ∂hyperbolicVolume := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hsplit :
      (∫ p, (verticalDerivative f.toFun p - f p) * f p
        ∂hyperbolicVolume) =
        (∫ p, verticalDerivative f.toFun p * f p ∂hyperbolicVolume) -
          ∫ p, f p * f p ∂hyperbolicVolume :=
    integral_sub_mul (verticalDerivativeCore f) f f
  rw [hcomm, hsplit] at h
  linarith only [h, hcomm]

theorem integrable_smoothCompact
    (f : HyperbolicSmoothCompactScalar) :
    Integrable f.toFun hyperbolicVolume :=
  f.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
    f.hasCompactSupport_toFun

noncomputable def smoothCompactIntegral :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] ℝ where
  toFun := fun f ↦ ∫ p, f p ∂hyperbolicVolume
  map_add' f g := by
    change (∫ p, f p + g p ∂hyperbolicVolume) =
      (∫ p, f p ∂hyperbolicVolume) + ∫ p, g p ∂hyperbolicVolume
    exact integral_add (integrable_smoothCompact f)
      (integrable_smoothCompact g)
  map_smul' c f := by
    change (∫ p, c * f p ∂hyperbolicVolume) =
      c * ∫ p, f p ∂hyperbolicVolume
    rw [integral_const_mul]

@[simp] theorem smoothCompactIntegral_apply
    (f : HyperbolicSmoothCompactScalar) :
    smoothCompactIntegral f = ∫ p, f p ∂hyperbolicVolume :=
  rfl

noncomputable def squareCore
    (f : HyperbolicSmoothCompactScalar) : HyperbolicSmoothCompactScalar :=
  scalarProductCore f f

@[simp] theorem squareCore_apply
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    squareCore f p = f p ^ 2 := by
  change f p * f p = f p ^ 2
  ring

noncomputable def covariantEnergyDensityCore
    (alpha : HyperbolicSmoothCompactOneForm) : HyperbolicSmoothCompactScalar :=
  squareCore (covariantComponent00Core alpha) +
    squareCore (covariantComponent01Core alpha) +
    squareCore (covariantComponent10Core alpha) +
    squareCore (covariantComponent11Core alpha)

noncomputable def hodgeEnergyDensityCore
    (alpha : HyperbolicSmoothCompactOneForm) : HyperbolicSmoothCompactScalar :=
  squareCore (oneFormExteriorDerivativeCore alpha) +
    squareCore (oneFormCodifferentialCore alpha)

noncomputable def oneFormEnergyDensityCore
    (alpha : HyperbolicSmoothCompactOneForm) : HyperbolicSmoothCompactScalar :=
  squareCore (oneFormComponentCore 0 alpha) +
    squareCore (oneFormComponentCore 1 alpha)

theorem covariantEnergyDensityCore_apply
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    covariantEnergyDensityCore alpha p =
      ‖oneFormCovariantDerivativeCore alpha p‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change squareCore (covariantComponent00Core alpha) p +
      squareCore (covariantComponent01Core alpha) p +
      squareCore (covariantComponent10Core alpha) p +
      squareCore (covariantComponent11Core alpha) p = _
  simp only [squareCore_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    oneFormCovariantDerivativeCore_apply_00,
    oneFormCovariantDerivativeCore_apply_01,
    oneFormCovariantDerivativeCore_apply_10,
    oneFormCovariantDerivativeCore_apply_11]
  change (horizontalDerivative (fun q ↦ alpha q 0) p - alpha p 1) ^ 2 +
      (horizontalDerivative (fun q ↦ alpha q 1) p + alpha p 0) ^ 2 +
      verticalDerivative (fun q ↦ alpha q 0) p ^ 2 +
      verticalDerivative (fun q ↦ alpha q 1) p ^ 2 = _
  ring

theorem hodgeEnergyDensityCore_apply
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    hodgeEnergyDensityCore alpha p =
      ‖oneFormHodgeDerivativeCore alpha p‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change squareCore (oneFormExteriorDerivativeCore alpha) p +
      squareCore (oneFormCodifferentialCore alpha) p = _
  simp only [squareCore_apply, Fin.sum_univ_two,
    oneFormHodgeDerivativeCore_apply_zero,
    oneFormHodgeDerivativeCore_apply_one]

theorem oneFormEnergyDensityCore_apply
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormEnergyDensityCore alpha p = ‖alpha p‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change squareCore (oneFormComponentCore 0 alpha) p +
      squareCore (oneFormComponentCore 1 alpha) p = _
  simp only [squareCore_apply, Fin.sum_univ_two,
    oneFormComponentCore_apply]

theorem hyperbolicBochnerEnergyDensity_algebra
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    covariantEnergyDensityCore alpha p -
        hodgeEnergyDensityCore alpha p -
        oneFormEnergyDensityCore alpha p =
      2 * (horizontalDerivative (fun q ↦ alpha q 1) p *
          verticalDerivative (fun q ↦ alpha q 0) p -
        horizontalDerivative (fun q ↦ alpha q 0) p *
          verticalDerivative (fun q ↦ alpha q 1) p) +
      2 * (alpha p 0 * verticalDerivative (fun q ↦ alpha q 0) p) +
      2 * (alpha p 1 * verticalDerivative (fun q ↦ alpha q 1) p) -
      (alpha p 0) ^ 2 - (alpha p 1) ^ 2 := by
  rw [covariantEnergyDensityCore_apply,
    hodgeEnergyDensityCore_apply,
    oneFormEnergyDensityCore_apply,
    EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    oneFormCovariantDerivativeCore_apply_00,
    oneFormCovariantDerivativeCore_apply_01,
    oneFormCovariantDerivativeCore_apply_10,
    oneFormCovariantDerivativeCore_apply_11,
    oneFormHodgeDerivativeCore_apply_zero,
    oneFormHodgeDerivativeCore_apply_one,
    oneFormExteriorDerivativeCore_apply,
    oneFormCodifferentialCore_apply]
  ring

noncomputable def mixedEnergyDensityCore
    (alpha : HyperbolicSmoothCompactOneForm) : HyperbolicSmoothCompactScalar :=
  scalarProductCore
      (horizontalDerivativeCore (oneFormComponentCore 1 alpha))
      (verticalDerivativeCore (oneFormComponentCore 0 alpha)) -
    scalarProductCore
      (horizontalDerivativeCore (oneFormComponentCore 0 alpha))
      (verticalDerivativeCore (oneFormComponentCore 1 alpha))

noncomputable def verticalSelfEnergyDensityCore
    (i : Fin 2) (alpha : HyperbolicSmoothCompactOneForm) :
    HyperbolicSmoothCompactScalar :=
  scalarProductCore (oneFormComponentCore i alpha)
    (verticalDerivativeCore (oneFormComponentCore i alpha))

@[simp] theorem mixedEnergyDensityCore_apply
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    mixedEnergyDensityCore alpha p =
      horizontalDerivative (fun q ↦ alpha q 1) p *
          verticalDerivative (fun q ↦ alpha q 0) p -
        horizontalDerivative (fun q ↦ alpha q 0) p *
          verticalDerivative (fun q ↦ alpha q 1) p := by
  rfl

@[simp] theorem verticalSelfEnergyDensityCore_apply
    (i : Fin 2) (alpha : HyperbolicSmoothCompactOneForm)
    (p : HyperbolicPlane) :
    verticalSelfEnergyDensityCore i alpha p =
      alpha p i * verticalDerivative (fun q ↦ alpha q i) p := by
  rfl

theorem hyperbolicBochnerEnergyDensityCore_identity
    (alpha : HyperbolicSmoothCompactOneForm) :
    covariantEnergyDensityCore alpha -
        hodgeEnergyDensityCore alpha -
        oneFormEnergyDensityCore alpha =
      (2 : ℝ) • mixedEnergyDensityCore alpha +
        (2 : ℝ) • verticalSelfEnergyDensityCore 0 alpha +
        (2 : ℝ) • verticalSelfEnergyDensityCore 1 alpha -
        squareCore (oneFormComponentCore 0 alpha) -
        squareCore (oneFormComponentCore 1 alpha) := by
  apply DFunLike.ext _ _
  intro p
  change covariantEnergyDensityCore alpha p -
      hodgeEnergyDensityCore alpha p -
      oneFormEnergyDensityCore alpha p =
    2 * mixedEnergyDensityCore alpha p +
      2 * verticalSelfEnergyDensityCore 0 alpha p +
      2 * verticalSelfEnergyDensityCore 1 alpha p -
      squareCore (oneFormComponentCore 0 alpha) p -
      squareCore (oneFormComponentCore 1 alpha) p
  rw [hyperbolicBochnerEnergyDensity_algebra alpha p]
  simp only [mixedEnergyDensityCore_apply,
    verticalSelfEnergyDensityCore_apply, squareCore_apply,
    oneFormComponentCore_apply]

theorem integral_hyperbolicBochnerWeitzenbock
    (alpha : HyperbolicSmoothCompactOneForm) :
    smoothCompactIntegral (covariantEnergyDensityCore alpha) =
      smoothCompactIntegral (hodgeEnergyDensityCore alpha) +
        smoothCompactIntegral (oneFormEnergyDensityCore alpha) := by
  have hmix : smoothCompactIntegral
      (mixedEnergyDensityCore alpha) = 0 := by
    change (∫ p, horizontalDerivative (fun q ↦ alpha q 1) p *
        verticalDerivative (fun q ↦ alpha q 0) p -
        horizontalDerivative (fun q ↦ alpha q 0) p *
          verticalDerivative (fun q ↦ alpha q 1) p
      ∂hyperbolicVolume) = 0
    exact integral_mixed_cross_zero
      (oneFormComponentCore 0 alpha) (oneFormComponentCore 1 alpha)
  have hself0 : 2 * smoothCompactIntegral
      (verticalSelfEnergyDensityCore 0 alpha) =
        smoothCompactIntegral
          (squareCore (oneFormComponentCore 0 alpha)) := by
    rw [smoothCompactIntegral_apply, smoothCompactIntegral_apply]
    calc
      2 * (∫ p, verticalSelfEnergyDensityCore 0 alpha p
          ∂hyperbolicVolume) =
          2 * (∫ p, (oneFormComponentCore 0 alpha) p *
            verticalDerivative (oneFormComponentCore 0 alpha).toFun p
          ∂hyperbolicVolume) := by
        congr 1
      _ = ∫ p, (oneFormComponentCore 0 alpha) p *
          (oneFormComponentCore 0 alpha) p ∂hyperbolicVolume :=
        two_mul_integral_mul_verticalDerivative_self
          (oneFormComponentCore 0 alpha)
      _ = ∫ p, squareCore (oneFormComponentCore 0 alpha) p
          ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        rw [squareCore_apply, pow_two]
  have hself1 : 2 * smoothCompactIntegral
      (verticalSelfEnergyDensityCore 1 alpha) =
        smoothCompactIntegral
          (squareCore (oneFormComponentCore 1 alpha)) := by
    rw [smoothCompactIntegral_apply, smoothCompactIntegral_apply]
    calc
      2 * (∫ p, verticalSelfEnergyDensityCore 1 alpha p
          ∂hyperbolicVolume) =
          2 * (∫ p, (oneFormComponentCore 1 alpha) p *
            verticalDerivative (oneFormComponentCore 1 alpha).toFun p
          ∂hyperbolicVolume) := by
        congr 1
      _ = ∫ p, (oneFormComponentCore 1 alpha) p *
          (oneFormComponentCore 1 alpha) p ∂hyperbolicVolume :=
        two_mul_integral_mul_verticalDerivative_self
          (oneFormComponentCore 1 alpha)
      _ = ∫ p, squareCore (oneFormComponentCore 1 alpha) p
          ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        rw [squareCore_apply, pow_two]
  have henergy := congrArg smoothCompactIntegral
    (hyperbolicBochnerEnergyDensityCore_identity alpha)
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at henergy
  linarith only [henergy, hmix, hself0, hself1]

/-! ## Hilbert-space form -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The squared `L²` norm of an included smooth compact section is the integral of its
pointwise squared norm. -/
theorem norm_sq_smoothCompact_toL2
    (f : HyperbolicSmoothCompactSection F) :
    ‖f.toL2‖ ^ 2 = ∫ p, ‖f p‖ ^ 2 ∂hyperbolicVolume := by
  rw [← real_inner_self_eq_norm_sq, inner_smoothCompact_toL2]
  apply integral_congr_ae
  filter_upwards with p
  rw [real_inner_self_eq_norm_sq]

/-- The compact-core Bochner--Weitzenbock identity as an equality of actual `L²` norms. -/
theorem hyperbolicBochnerWeitzenbockCore_norm_sq
    (alpha : HyperbolicSmoothCompactOneForm) :
    ‖hyperbolicNablaOneCoreL2 alpha‖ ^ 2 =
      ‖hyperbolicHodgeOneCoreL2 alpha‖ ^ 2 +
        ‖hyperbolicSmoothCompactToL2 alpha‖ ^ 2 := by
  change ‖(oneFormCovariantDerivativeCore alpha).toL2‖ ^ 2 =
    ‖(oneFormHodgeDerivativeCore alpha).toL2‖ ^ 2 + ‖alpha.toL2‖ ^ 2
  rw [norm_sq_smoothCompact_toL2, norm_sq_smoothCompact_toL2,
    norm_sq_smoothCompact_toL2]
  simpa only [smoothCompactIntegral_apply,
    covariantEnergyDensityCore_apply, hodgeEnergyDensityCore_apply,
    oneFormEnergyDensityCore_apply] using
      integral_hyperbolicBochnerWeitzenbock alpha

end RiemannianFluids.HyperbolicPlane
