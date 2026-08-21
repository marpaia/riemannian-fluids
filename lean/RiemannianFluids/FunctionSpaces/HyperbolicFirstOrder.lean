import RiemannianFluids.Analysis.ClosedOperators
import RiemannianFluids.FunctionSpaces.HyperbolicL2

/-!
# First-order de Rham operators on the measured hyperbolic plane

This module constructs the compact-core differential operators that generate the global
hyperbolic Hilbert complex.  One-forms are written in the oriented orthonormal coframe
`(θ¹, θ²) = (dx/y, dy/y)`.  If `α = a θ¹ + b θ²` and
`e₁ = y ∂x`, `e₂ = y ∂y`, then

    d f       = (e₁ f) θ¹ + (e₂ f) θ²,
    d α       = (e₁ b + a - e₂ a) θ¹∧θ²,
    δ α       = -e₁ a + b - e₂ b,
    δ(c θ¹∧θ²) = (e₂ c) θ¹ - (e₁ c) θ².

The zero-order terms are not conventions inserted by hand: they are the connection/divergence
terms of the moving orthonormal frame.  The resulting maps are first constructed on the actual
smooth compact cores and then transported, injectively, to densely defined `LinearPMap`s on the
concrete `L²` quotients from `HyperbolicL2`.
-/

noncomputable section

namespace RiemannianFluids
namespace HyperbolicPlane

open Bundle ENNReal Function MeasureTheory Pointwise Set
open scoped Bundle ContDiff ENNReal Manifold RealInnerProductSpace

/-! ## Smooth directional derivatives in the orthonormal frame -/

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The manifold derivative family in the global upper-half-plane chart. -/
noncomputable def manifoldDerivativeFun (f : HyperbolicPlane → F) :
    HyperbolicPlane → (ℂ →L[ℝ] F) :=
  fun p ↦ mvfderiv (modelWithCornersSelf ℝ ℂ) f p

/-- In the single global chart, the derivative family of a `C^(k+1)` fixed-fiber field is
`C^k`. -/
theorem contMDiffAt_manifoldDerivativeFun {k : ℕ∞ω}
    (f : HyperbolicPlane → F) (p₀ : HyperbolicPlane)
    (hf : ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F)
      (k + 1) f p₀) :
    ContMDiffAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (ℂ →L[ℝ] F)) k (manifoldDerivativeFun f) p₀ := by
  have h := hf.mfderiv_const (m := k) le_rfl
  refine h.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun p ↦ ?_
  have hcoord : inTangentCoordinates (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ F) id f
      (fun q ↦ mfderiv (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ F) f q) p₀ p = manifoldDerivativeFun f p := by
    ext v
    show (trivializationAt F (TangentSpace (modelWithCornersSelf ℝ F))
        (f p₀)).continuousLinearMapAt ℝ (f p)
        (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) f p
          ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ))
            p₀).symmL ℝ p v)) = manifoldDerivativeFun f p v
    rw [tangent_symmL, TangentBundle.continuousLinearMapAt_model_space]
    rfl
  exact hcoord.symm

/-- Smooth fields have a smooth manifold-derivative family in the global chart. -/
theorem contMDiff_manifoldDerivativeFun (f : HyperbolicPlane → F)
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ f) :
    ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (ℂ →L[ℝ] F)) ∞ (manifoldDerivativeFun f) := by
  intro p
  apply contMDiffAt_manifoldDerivativeFun (k := ∞) f p
  simpa using hf p

/-- The horizontal orthonormal frame vector `e₁ = y ∂x`. -/
noncomputable def horizontalFrameVector (p : HyperbolicPlane) : ℂ :=
  p.im

/-- The vertical orthonormal frame vector `e₂ = y ∂y`. -/
noncomputable def verticalFrameVector (p : HyperbolicPlane) : ℂ :=
  (p.im : ℂ) * Complex.I

theorem contMDiff_horizontalFrameVector {n : ℕ∞ω} :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) n
      horizontalFrameVector := by
  change ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) n
    (fun p ↦ Complex.ofRealCLM (im p))
  exact Complex.ofRealCLM.contMDiff.comp (contMDiff_im (n := n))

theorem contMDiff_verticalFrameVector {n : ℕ∞ω} :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) n
      verticalFrameVector := by
  have h := ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).contMDiff.comp
    (contMDiff_horizontalFrameVector (n := n))
  convert h using 1
  funext p
  exact mul_comm _ _

/-- Differentiate a fixed-fiber field along `e₁`. -/
noncomputable def horizontalDerivative (f : HyperbolicPlane → F) :
    HyperbolicPlane → F :=
  fun p ↦ manifoldDerivativeFun f p (horizontalFrameVector p)

/-- Differentiate a fixed-fiber field along `e₂`. -/
noncomputable def verticalDerivative (f : HyperbolicPlane → F) :
    HyperbolicPlane → F :=
  fun p ↦ manifoldDerivativeFun f p (verticalFrameVector p)

theorem contMDiff_horizontalDerivative (f : HyperbolicPlane → F)
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ f) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞
      (horizontalDerivative f) :=
  (contMDiff_manifoldDerivativeFun f hf).clm_apply
    (contMDiff_horizontalFrameVector (n := ∞))

theorem contMDiff_verticalDerivative (f : HyperbolicPlane → F)
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞ f) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) ∞
      (verticalDerivative f) :=
  (contMDiff_manifoldDerivativeFun f hf).clm_apply
    (contMDiff_verticalFrameVector (n := ∞))

/-- The manifold derivative vanishes outside the topological support of the field. -/
theorem manifoldDerivativeFun_eq_zero_of_notMem_tsupport
    (f : HyperbolicPlane → F) (p : HyperbolicPlane) (hp : p ∉ tsupport f) :
    manifoldDerivativeFun f p = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hp
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := modelWithCornersSelf ℝ ℂ)
    (I' := modelWithCornersSelf ℝ F) hp
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ F) f p = 0
  rw [hmf]
  exact mfderiv_const

theorem support_horizontalDerivative_subset (f : HyperbolicPlane → F) :
    support (horizontalDerivative f) ⊆ tsupport f := by
  intro p hp
  by_contra hpt
  apply hp
  rw [horizontalDerivative, manifoldDerivativeFun_eq_zero_of_notMem_tsupport f p hpt]
  rfl

theorem support_verticalDerivative_subset (f : HyperbolicPlane → F) :
    support (verticalDerivative f) ⊆ tsupport f := by
  intro p hp
  by_contra hpt
  apply hp
  rw [verticalDerivative, manifoldDerivativeFun_eq_zero_of_notMem_tsupport f p hpt]
  rfl

theorem hasCompactSupport_horizontalDerivative (f : HyperbolicPlane → F)
    (hf : HasCompactSupport f) : HasCompactSupport (horizontalDerivative f) :=
  hf.of_isClosed_subset isClosed_closure
    (closure_minimal (support_horizontalDerivative_subset f) hf.isClosed)

theorem hasCompactSupport_verticalDerivative (f : HyperbolicPlane → F)
    (hf : HasCompactSupport f) : HasCompactSupport (verticalDerivative f) :=
  hf.of_isClosed_subset isClosed_closure
    (closure_minimal (support_verticalDerivative_subset f) hf.isClosed)

/-! ## Linear operations on the smooth compact core -/

/-- Apply a fixed continuous linear map to a smooth compact section. -/
noncomputable def mapSmoothCompactSection (L : F →L[ℝ] G)
    (f : HyperbolicSmoothCompactSection F) : HyperbolicSmoothCompactSection G :=
  ⟨fun p ↦ L (f p), L.contMDiff.comp f.contMDiff_toFun,
    f.hasCompactSupport_toFun.mono (by
      intro p hp hzero
      apply hp
      simp [hzero])⟩

/-- Fiberwise application of a continuous linear map is linear on the smooth compact core. -/
noncomputable def mapSmoothCompactSectionLinear (L : F →L[ℝ] G) :
    HyperbolicSmoothCompactSection F →ₗ[ℝ] HyperbolicSmoothCompactSection G where
  toFun := mapSmoothCompactSection L
  map_add' f g := by
    apply DFunLike.ext _ _
    intro p
    exact L.map_add (f p) (g p)
  map_smul' c f := by
    apply DFunLike.ext _ _
    intro p
    exact L.map_smul c (f p)

@[simp] theorem mapSmoothCompactSectionLinear_apply (L : F →L[ℝ] G)
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    mapSmoothCompactSectionLinear L f p = L (f p) :=
  rfl

/-- Horizontal differentiation preserves the smooth compact core. -/
noncomputable def horizontalDerivativeCore
    (f : HyperbolicSmoothCompactSection F) : HyperbolicSmoothCompactSection F :=
  ⟨horizontalDerivative f.toFun,
    contMDiff_horizontalDerivative f.toFun f.contMDiff_toFun,
    hasCompactSupport_horizontalDerivative f.toFun f.hasCompactSupport_toFun⟩

/-- Vertical differentiation preserves the smooth compact core. -/
noncomputable def verticalDerivativeCore
    (f : HyperbolicSmoothCompactSection F) : HyperbolicSmoothCompactSection F :=
  ⟨verticalDerivative f.toFun,
    contMDiff_verticalDerivative f.toFun f.contMDiff_toFun,
    hasCompactSupport_verticalDerivative f.toFun f.hasCompactSupport_toFun⟩

/-- Horizontal frame differentiation as a linear endomorphism of the smooth compact core. -/
noncomputable def horizontalDerivativeCoreLinear :
    HyperbolicSmoothCompactSection F →ₗ[ℝ] HyperbolicSmoothCompactSection F where
  toFun := horizontalDerivativeCore
  map_add' f g := by
    apply DFunLike.ext _ _
    intro p
    change mvfderiv (modelWithCornersSelf ℝ ℂ) (f.toFun + g.toFun) p
      (horizontalFrameVector p) =
      mvfderiv (modelWithCornersSelf ℝ ℂ) f.toFun p (horizontalFrameVector p) +
      mvfderiv (modelWithCornersSelf ℝ ℂ) g.toFun p (horizontalFrameVector p)
    rw [mvfderiv_add (f.contMDiff_toFun.mdifferentiable (by simp) p)
      (g.contMDiff_toFun.mdifferentiable (by simp) p)]
    rfl
  map_smul' c f := by
    apply DFunLike.ext _ _
    intro p
    change mvfderiv (modelWithCornersSelf ℝ ℂ)
      ((fun _ : HyperbolicPlane ↦ c) • f.toFun) p (horizontalFrameVector p) =
      c • mvfderiv (modelWithCornersSelf ℝ ℂ) f.toFun p (horizontalFrameVector p)
    rw [mvfderiv_smul mdifferentiableAt_const
      (f.contMDiff_toFun.mdifferentiable (by simp) p)]
    simp [mvfderiv_const]

/-- Vertical frame differentiation as a linear endomorphism of the smooth compact core. -/
noncomputable def verticalDerivativeCoreLinear :
    HyperbolicSmoothCompactSection F →ₗ[ℝ] HyperbolicSmoothCompactSection F where
  toFun := verticalDerivativeCore
  map_add' f g := by
    apply DFunLike.ext _ _
    intro p
    change mvfderiv (modelWithCornersSelf ℝ ℂ) (f.toFun + g.toFun) p
      (verticalFrameVector p) =
      mvfderiv (modelWithCornersSelf ℝ ℂ) f.toFun p (verticalFrameVector p) +
      mvfderiv (modelWithCornersSelf ℝ ℂ) g.toFun p (verticalFrameVector p)
    rw [mvfderiv_add (f.contMDiff_toFun.mdifferentiable (by simp) p)
      (g.contMDiff_toFun.mdifferentiable (by simp) p)]
    rfl
  map_smul' c f := by
    apply DFunLike.ext _ _
    intro p
    change mvfderiv (modelWithCornersSelf ℝ ℂ)
      ((fun _ : HyperbolicPlane ↦ c) • f.toFun) p (verticalFrameVector p) =
      c • mvfderiv (modelWithCornersSelf ℝ ℂ) f.toFun p (verticalFrameVector p)
    rw [mvfderiv_smul mdifferentiableAt_const
      (f.contMDiff_toFun.mdifferentiable (by simp) p)]
    simp [mvfderiv_const]

@[simp] theorem horizontalDerivativeCoreLinear_apply
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    horizontalDerivativeCoreLinear f p = horizontalDerivative f.toFun p :=
  rfl

@[simp] theorem verticalDerivativeCoreLinear_apply
    (f : HyperbolicSmoothCompactSection F) (p : HyperbolicPlane) :
    verticalDerivativeCoreLinear f p = verticalDerivative f.toFun p :=
  rfl

/-! ## Compact-core de Rham operators -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Insert a scalar into one coordinate of a finite-dimensional Euclidean fiber. -/
noncomputable def euclideanCoordinateInjection (i : ι) :
    ℝ →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a ↦ EuclideanSpace.single i a
    map_add' := by
      intro a b
      ext j
      by_cases h : j = i <;> simp [h]
    map_smul' := by
      intro c a
      ext j
      by_cases h : j = i <;> simp [h] }

@[simp] theorem euclideanCoordinateInjection_apply (i j : ι) (a : ℝ) :
    euclideanCoordinateInjection i a j = if j = i then a else 0 := by
  simp [euclideanCoordinateInjection, PiLp.single_apply]

/-- Extract one orthonormal component of a compactly supported one-form. -/
noncomputable def oneFormComponentCore (i : Fin 2) :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  mapSmoothCompactSectionLinear (EuclideanSpace.proj i)

@[simp] theorem oneFormComponentCore_apply (i : Fin 2)
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormComponentCore i alpha p = alpha p i :=
  rfl

/-- Exterior derivative of compactly supported scalars, in the orthonormal coframe. -/
noncomputable def scalarExteriorDerivativeCore :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicSmoothCompactOneForm :=
  (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (0 : Fin 2))).comp horizontalDerivativeCoreLinear +
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (1 : Fin 2))).comp verticalDerivativeCoreLinear

theorem scalarExteriorDerivativeCore_apply_zero
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    scalarExteriorDerivativeCore f p 0 = horizontalDerivative f.toFun p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      ((horizontalDerivativeCoreLinear f) p) 0 +
    euclideanCoordinateInjection (1 : Fin 2)
      ((verticalDerivativeCoreLinear f) p) 0 = _
  rw [horizontalDerivativeCoreLinear_apply, verticalDerivativeCoreLinear_apply]
  simp

theorem scalarExteriorDerivativeCore_apply_one
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    scalarExteriorDerivativeCore f p 1 = verticalDerivative f.toFun p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      ((horizontalDerivativeCoreLinear f) p) 1 +
    euclideanCoordinateInjection (1 : Fin 2)
      ((verticalDerivativeCoreLinear f) p) 1 = _
  rw [horizontalDerivativeCoreLinear_apply, verticalDerivativeCoreLinear_apply]
  simp

/-- Exterior derivative of compactly supported one-forms, with two-forms identified with their
coefficient in the oriented unit volume form. -/
noncomputable def oneFormExteriorDerivativeCore :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  horizontalDerivativeCoreLinear.comp (oneFormComponentCore 1) +
    oneFormComponentCore 0 -
    verticalDerivativeCoreLinear.comp (oneFormComponentCore 0)

/-- Codifferential from compactly supported one-forms to scalars. -/
noncomputable def oneFormCodifferentialCore :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  -(horizontalDerivativeCoreLinear.comp (oneFormComponentCore 0)) +
    oneFormComponentCore 1 -
    verticalDerivativeCoreLinear.comp (oneFormComponentCore 1)

/-- Codifferential from compactly supported top forms to one-forms. -/
noncomputable def twoFormCodifferentialCore :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicSmoothCompactOneForm :=
  (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (0 : Fin 2))).comp verticalDerivativeCoreLinear -
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (1 : Fin 2))).comp horizontalDerivativeCoreLinear

theorem oneFormExteriorDerivativeCore_apply
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormExteriorDerivativeCore alpha p =
      horizontalDerivative (fun q ↦ alpha q 1) p + alpha p 0 -
        verticalDerivative (fun q ↦ alpha q 0) p := by
  change (horizontalDerivativeCoreLinear (oneFormComponentCore 1 alpha)) p +
      (oneFormComponentCore 0 alpha) p -
      (verticalDerivativeCoreLinear (oneFormComponentCore 0 alpha)) p = _
  rw [horizontalDerivativeCoreLinear_apply, verticalDerivativeCoreLinear_apply]
  rfl

theorem oneFormCodifferentialCore_apply
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormCodifferentialCore alpha p =
      -horizontalDerivative (fun q ↦ alpha q 0) p + alpha p 1 -
        verticalDerivative (fun q ↦ alpha q 1) p := by
  change -(horizontalDerivativeCoreLinear (oneFormComponentCore 0 alpha)) p +
      (oneFormComponentCore 1 alpha) p -
      (verticalDerivativeCoreLinear (oneFormComponentCore 1 alpha)) p = _
  rw [horizontalDerivativeCoreLinear_apply, verticalDerivativeCoreLinear_apply]
  rfl

theorem twoFormCodifferentialCore_apply_zero
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    twoFormCodifferentialCore f p 0 = verticalDerivative f.toFun p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      ((verticalDerivativeCoreLinear f) p) 0 -
    euclideanCoordinateInjection (1 : Fin 2)
      ((horizontalDerivativeCoreLinear f) p) 0 = _
  rw [horizontalDerivativeCoreLinear_apply, verticalDerivativeCoreLinear_apply]
  simp

theorem twoFormCodifferentialCore_apply_one
    (f : HyperbolicSmoothCompactScalar) (p : HyperbolicPlane) :
    twoFormCodifferentialCore f p 1 = -horizontalDerivative f.toFun p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      ((verticalDerivativeCoreLinear f) p) 1 -
    euclideanCoordinateInjection (1 : Fin 2)
      ((horizontalDerivativeCoreLinear f) p) 1 = _
  rw [horizontalDerivativeCoreLinear_apply, verticalDerivativeCoreLinear_apply]
  simp

/-! ## Covariant and Hodge first-order cores -/

/-- Four orthonormal-frame coefficients of the covariant derivative of a one-form.  The first
index is the differentiating frame direction and the second is the one-form component. -/
abbrev HyperbolicCovariantOneFormComponents :=
  EuclideanSpace ℝ (Fin 2 × Fin 2)

/-- Smooth compactly supported covariant derivatives in orthonormal components. -/
abbrev HyperbolicSmoothCompactCovariantOneForm :=
  HyperbolicSmoothCompactSection HyperbolicCovariantOneFormComponents

/-- The concrete `L²` target for covariant derivatives of one-forms. -/
abbrev HyperbolicCovariantOneFormL2 :=
  Lp HyperbolicCovariantOneFormComponents 2 hyperbolicVolume

noncomputable def covariantComponent00Core :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  horizontalDerivativeCoreLinear.comp (oneFormComponentCore 0) - oneFormComponentCore 1

noncomputable def covariantComponent01Core :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  horizontalDerivativeCoreLinear.comp (oneFormComponentCore 1) + oneFormComponentCore 0

noncomputable def covariantComponent10Core :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  verticalDerivativeCoreLinear.comp (oneFormComponentCore 0)

noncomputable def covariantComponent11Core :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  verticalDerivativeCoreLinear.comp (oneFormComponentCore 1)

/-- Levi--Civita covariant derivative of a compactly supported one-form in the global
orthonormal frame. -/
noncomputable def oneFormCovariantDerivativeCore :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactCovariantOneForm :=
  (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection ((0, 0) : Fin 2 × Fin 2))).comp covariantComponent00Core +
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection ((0, 1) : Fin 2 × Fin 2))).comp covariantComponent01Core +
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection ((1, 0) : Fin 2 × Fin 2))).comp covariantComponent10Core +
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection ((1, 1) : Fin 2 × Fin 2))).comp covariantComponent11Core

/-- The pair `(dα, δα)` as a two-component compact core field. -/
noncomputable def oneFormHodgeDerivativeCore :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactOneForm :=
  (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (0 : Fin 2))).comp oneFormExteriorDerivativeCore +
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (1 : Fin 2))).comp oneFormCodifferentialCore

theorem oneFormCovariantDerivativeCore_apply_00
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormCovariantDerivativeCore alpha p (0, 0) =
      horizontalDerivative (fun q ↦ alpha q 0) p - alpha p 1 := by
  change
    euclideanCoordinateInjection ((0, 0) : Fin 2 × Fin 2)
        ((covariantComponent00Core alpha) p) (0, 0) +
      euclideanCoordinateInjection ((0, 1) : Fin 2 × Fin 2)
        ((covariantComponent01Core alpha) p) (0, 0) +
      euclideanCoordinateInjection ((1, 0) : Fin 2 × Fin 2)
        ((covariantComponent10Core alpha) p) (0, 0) +
      euclideanCoordinateInjection ((1, 1) : Fin 2 × Fin 2)
        ((covariantComponent11Core alpha) p) (0, 0) = _
  simp [euclideanCoordinateInjection_apply]
  change (horizontalDerivativeCoreLinear (oneFormComponentCore 0 alpha)) p -
      (oneFormComponentCore 1 alpha) p = _
  rw [horizontalDerivativeCoreLinear_apply]
  rfl

theorem oneFormCovariantDerivativeCore_apply_01
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormCovariantDerivativeCore alpha p (0, 1) =
      horizontalDerivative (fun q ↦ alpha q 1) p + alpha p 0 := by
  change
    euclideanCoordinateInjection ((0, 0) : Fin 2 × Fin 2)
        ((covariantComponent00Core alpha) p) (0, 1) +
      euclideanCoordinateInjection ((0, 1) : Fin 2 × Fin 2)
        ((covariantComponent01Core alpha) p) (0, 1) +
      euclideanCoordinateInjection ((1, 0) : Fin 2 × Fin 2)
        ((covariantComponent10Core alpha) p) (0, 1) +
      euclideanCoordinateInjection ((1, 1) : Fin 2 × Fin 2)
        ((covariantComponent11Core alpha) p) (0, 1) = _
  simp [euclideanCoordinateInjection_apply]
  change (horizontalDerivativeCoreLinear (oneFormComponentCore 1 alpha)) p +
      (oneFormComponentCore 0 alpha) p = _
  rw [horizontalDerivativeCoreLinear_apply]
  rfl

theorem oneFormCovariantDerivativeCore_apply_10
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormCovariantDerivativeCore alpha p (1, 0) =
      verticalDerivative (fun q ↦ alpha q 0) p := by
  change
    euclideanCoordinateInjection ((0, 0) : Fin 2 × Fin 2)
        ((covariantComponent00Core alpha) p) (1, 0) +
      euclideanCoordinateInjection ((0, 1) : Fin 2 × Fin 2)
        ((covariantComponent01Core alpha) p) (1, 0) +
      euclideanCoordinateInjection ((1, 0) : Fin 2 × Fin 2)
        ((covariantComponent10Core alpha) p) (1, 0) +
      euclideanCoordinateInjection ((1, 1) : Fin 2 × Fin 2)
        ((covariantComponent11Core alpha) p) (1, 0) = _
  simp [euclideanCoordinateInjection_apply]
  exact verticalDerivativeCoreLinear_apply _ _

theorem oneFormCovariantDerivativeCore_apply_11
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormCovariantDerivativeCore alpha p (1, 1) =
      verticalDerivative (fun q ↦ alpha q 1) p := by
  change
    euclideanCoordinateInjection ((0, 0) : Fin 2 × Fin 2)
        ((covariantComponent00Core alpha) p) (1, 1) +
      euclideanCoordinateInjection ((0, 1) : Fin 2 × Fin 2)
        ((covariantComponent01Core alpha) p) (1, 1) +
      euclideanCoordinateInjection ((1, 0) : Fin 2 × Fin 2)
        ((covariantComponent10Core alpha) p) (1, 1) +
      euclideanCoordinateInjection ((1, 1) : Fin 2 × Fin 2)
        ((covariantComponent11Core alpha) p) (1, 1) = _
  simp [euclideanCoordinateInjection_apply]
  exact verticalDerivativeCoreLinear_apply _ _

theorem oneFormHodgeDerivativeCore_apply_zero
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormHodgeDerivativeCore alpha p 0 = oneFormExteriorDerivativeCore alpha p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      ((oneFormExteriorDerivativeCore alpha) p) 0 +
    euclideanCoordinateInjection (1 : Fin 2)
      ((oneFormCodifferentialCore alpha) p) 0 = _
  simp

theorem oneFormHodgeDerivativeCore_apply_one
    (alpha : HyperbolicSmoothCompactOneForm) (p : HyperbolicPlane) :
    oneFormHodgeDerivativeCore alpha p 1 = oneFormCodifferentialCore alpha p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      ((oneFormExteriorDerivativeCore alpha) p) 1 +
    euclideanCoordinateInjection (1 : Fin 2)
      ((oneFormCodifferentialCore alpha) p) 1 = _
  simp

/-! ## Densely defined operators on the concrete `L²` quotients -/

/-- Compact-core `d₀` with values in one-form `L²`. -/
noncomputable def hyperbolicDZeroCoreL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicOneFormL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).comp
      scalarExteriorDerivativeCore

/-- Compact-core `d₁` with top forms identified with scalar `L²`. -/
noncomputable def hyperbolicDOneCoreL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicScalarL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2).comp
      oneFormExteriorDerivativeCore

/-- Compact-core `δ₁`. -/
noncomputable def hyperbolicDeltaOneCoreL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicScalarL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2).comp
      oneFormCodifferentialCore

/-- Compact-core `δ₂`. -/
noncomputable def hyperbolicDeltaTwoCoreL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicOneFormL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).comp
      twoFormCodifferentialCore

/-- Compact-core covariant derivative with its four-component `L²` target. -/
noncomputable def hyperbolicNablaOneCoreL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicCovariantOneFormL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ]
      HyperbolicCovariantOneFormL2).comp oneFormCovariantDerivativeCore

/-- Compact-core pair `(d₁, δ₁)` with a two-component `L²` target. -/
noncomputable def hyperbolicHodgeOneCoreL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).comp
      oneFormHodgeDerivativeCore

/-- Densely defined scalar exterior derivative on the actual scalar `L²` quotient. -/
noncomputable def hyperbolicDZero : HyperbolicScalarL2 →ₗ.[ℝ] HyperbolicOneFormL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicDZeroCoreL2

/-- Densely defined one-form exterior derivative. -/
noncomputable def hyperbolicDOne : HyperbolicOneFormL2 →ₗ.[ℝ] HyperbolicScalarL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicDOneCoreL2

/-- Densely defined compact-core codifferential on one-forms. -/
noncomputable def hyperbolicDeltaOne : HyperbolicOneFormL2 →ₗ.[ℝ] HyperbolicScalarL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicDeltaOneCoreL2

/-- Densely defined compact-core codifferential on top forms. -/
noncomputable def hyperbolicDeltaTwo : HyperbolicScalarL2 →ₗ.[ℝ] HyperbolicOneFormL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicDeltaTwoCoreL2

/-- Densely defined compact-core covariant derivative on one-form `L²`. -/
noncomputable def hyperbolicNablaOne :
    HyperbolicOneFormL2 →ₗ.[ℝ] HyperbolicCovariantOneFormL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicNablaOneCoreL2

/-- Densely defined compact-core Hodge derivative `α ↦ (dα, δα)`. -/
noncomputable def hyperbolicHodgeOne : HyperbolicOneFormL2 →ₗ.[ℝ] HyperbolicOneFormL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicHodgeOneCoreL2

theorem hyperbolicDZero_dense_domain :
    Dense (hyperbolicDZero.domain : Set HyperbolicScalarL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _ hyperbolicSmoothCompactScalar_dense

theorem hyperbolicDOne_dense_domain :
    Dense (hyperbolicDOne.domain : Set HyperbolicOneFormL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _ hyperbolicSmoothCompactOneForm_dense

theorem hyperbolicDeltaOne_dense_domain :
    Dense (hyperbolicDeltaOne.domain : Set HyperbolicOneFormL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _ hyperbolicSmoothCompactOneForm_dense

theorem hyperbolicDeltaTwo_dense_domain :
    Dense (hyperbolicDeltaTwo.domain : Set HyperbolicScalarL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _ hyperbolicSmoothCompactScalar_dense

theorem hyperbolicNablaOne_dense_domain :
    Dense (hyperbolicNablaOne.domain : Set HyperbolicOneFormL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _ hyperbolicSmoothCompactOneForm_dense

theorem hyperbolicHodgeOne_dense_domain :
    Dense (hyperbolicHodgeOne.domain : Set HyperbolicOneFormL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _ hyperbolicSmoothCompactOneForm_dense

end HyperbolicPlane
end RiemannianFluids
