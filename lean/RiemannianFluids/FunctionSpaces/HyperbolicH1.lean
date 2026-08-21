import RiemannianFluids.FunctionSpaces.HyperbolicBochner

/-!
# The source-normalized one-form `H¹` space on the hyperbolic plane

CCP25 defines `H¹` as the completion of compactly supported smooth forms for

`[alpha, beta] = (alpha, beta)_{L²} + (nabla alpha, nabla beta)_{L²}`.

This file closes the concrete covariant derivative on the complete measured upper half-plane and
uses its graph as that Hilbert carrier.  The Bochner--Weitzenbock theorem then identifies its core
norm exactly with `2‖alpha‖₂² + ‖d alpha‖₂² + ‖delta alpha‖₂²`.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open MeasureTheory
open scoped RealInnerProductSpace

/-! ## Compact-core formal adjoint of the covariant derivative -/

/-- Extract one coefficient of a compactly supported covariant two-tensor. -/
noncomputable def covariantOneFormComponentCore (i : Fin 2 × Fin 2) :
    HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  mapSmoothCompactSectionLinear (EuclideanSpace.proj i)

@[simp] theorem covariantOneFormComponentCore_apply (i : Fin 2 × Fin 2)
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    covariantOneFormComponentCore i beta p = beta p i :=
  rfl

/-- First component of `nabla* beta` in the oriented hyperbolic frame. -/
noncomputable def covariantAdjointComponentZeroCore :
    HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  -(horizontalDerivativeCoreLinear.comp (covariantOneFormComponentCore (0, 0))) +
    covariantOneFormComponentCore (0, 1) -
    verticalDerivativeCoreLinear.comp (covariantOneFormComponentCore (1, 0)) +
    covariantOneFormComponentCore (1, 0)

/-- Second component of `nabla* beta` in the oriented hyperbolic frame. -/
noncomputable def covariantAdjointComponentOneCore :
    HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ] HyperbolicSmoothCompactScalar :=
  -(covariantOneFormComponentCore (0, 0)) -
    horizontalDerivativeCoreLinear.comp (covariantOneFormComponentCore (0, 1)) -
    verticalDerivativeCoreLinear.comp (covariantOneFormComponentCore (1, 1)) +
    covariantOneFormComponentCore (1, 1)

/-- Compact-core formal adjoint of the covariant derivative. -/
noncomputable def oneFormCovariantAdjointCore :
    HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ] HyperbolicSmoothCompactOneForm :=
  (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (0 : Fin 2))).comp covariantAdjointComponentZeroCore +
    (mapSmoothCompactSectionLinear
      (euclideanCoordinateInjection (1 : Fin 2))).comp covariantAdjointComponentOneCore

theorem covariantAdjointComponentZeroCore_apply
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    covariantAdjointComponentZeroCore beta p =
      -horizontalDerivative (fun q ↦ beta q (0, 0)) p + beta p (0, 1) -
        verticalDerivative (fun q ↦ beta q (1, 0)) p + beta p (1, 0) := by
  rfl

theorem covariantAdjointComponentOneCore_apply
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    covariantAdjointComponentOneCore beta p =
      -beta p (0, 0) - horizontalDerivative (fun q ↦ beta q (0, 1)) p -
        verticalDerivative (fun q ↦ beta q (1, 1)) p + beta p (1, 1) := by
  rfl

@[simp] theorem oneFormCovariantAdjointCore_apply_zero
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    oneFormCovariantAdjointCore beta p 0 = covariantAdjointComponentZeroCore beta p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      (covariantAdjointComponentZeroCore beta p) 0 +
    euclideanCoordinateInjection (1 : Fin 2)
      (covariantAdjointComponentOneCore beta p) 0 = _
  simp

@[simp] theorem oneFormCovariantAdjointCore_apply_one
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    oneFormCovariantAdjointCore beta p 1 = covariantAdjointComponentOneCore beta p := by
  change euclideanCoordinateInjection (0 : Fin 2)
      (covariantAdjointComponentZeroCore beta p) 1 +
    euclideanCoordinateInjection (1 : Fin 2)
      (covariantAdjointComponentOneCore beta p) 1 = _
  simp

/-- Horizontal frame integration by parts, oriented with the derivative on the first factor. -/
theorem smoothCompactIntegral_horizontalDerivative_mul
    (f g : HyperbolicSmoothCompactScalar) :
    smoothCompactIntegral
        (scalarProductCore (horizontalDerivativeCore f) g) =
      -smoothCompactIntegral
        (scalarProductCore f (horizontalDerivativeCore g)) := by
  simp only [smoothCompactIntegral_apply]
  calc
    (∫ p, horizontalDerivative f.toFun p * g p ∂hyperbolicVolume) =
        ∫ p, g p * horizontalDerivative f.toFun p ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = -(∫ p, horizontalDerivative g.toFun p * f p ∂hyperbolicVolume) :=
      integral_mul_horizontalDerivative g f
    _ = -(∫ p, f p * horizontalDerivative g.toFun p ∂hyperbolicVolume) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      ring

/-- Vertical frame integration by parts, including `div(e₂) = -1`. -/
theorem smoothCompactIntegral_verticalDerivative_mul
    (f g : HyperbolicSmoothCompactScalar) :
    smoothCompactIntegral
        (scalarProductCore (verticalDerivativeCore f) g) =
      -smoothCompactIntegral
        (scalarProductCore f (verticalDerivativeCore g - g)) := by
  simp only [smoothCompactIntegral_apply]
  calc
    (∫ p, verticalDerivative f.toFun p * g p ∂hyperbolicVolume) =
        ∫ p, g p * verticalDerivative f.toFun p ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = -(∫ p, (verticalDerivative g.toFun p - g p) * f p
          ∂hyperbolicVolume) := integral_mul_verticalDerivative g f
    _ = -(∫ p, f p * (verticalDerivative g.toFun p - g p)
          ∂hyperbolicVolume) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      ring

/-- Expanded form of vertical integration by parts. -/
theorem smoothCompactIntegral_verticalDerivative_mul_expanded
    (f g : HyperbolicSmoothCompactScalar) :
    smoothCompactIntegral
        (scalarProductCore (verticalDerivativeCore f) g) =
      -smoothCompactIntegral
          (scalarProductCore f (verticalDerivativeCore g)) +
        smoothCompactIntegral (scalarProductCore f g) := by
  rw [smoothCompactIntegral_verticalDerivative_mul]
  have hproduct :
      scalarProductCore f (verticalDerivativeCore g - g) =
        scalarProductCore f (verticalDerivativeCore g) - scalarProductCore f g := by
    apply DFunLike.ext _ _
    intro p
    change f p * (verticalDerivative g.toFun p - g p) =
      f p * verticalDerivative g.toFun p - f p * g p
    ring
  rw [hproduct, map_sub]
  ring

/-- The pointwise covariant-derivative pairing written as a smooth compact scalar core. -/
noncomputable def covariantPairingCore
    (alpha : HyperbolicSmoothCompactOneForm)
    (beta : HyperbolicSmoothCompactCovariantOneForm) :
    HyperbolicSmoothCompactScalar :=
  scalarProductCore
      (horizontalDerivativeCore (oneFormComponentCore 0 alpha))
      (covariantOneFormComponentCore (0, 0) beta) -
    scalarProductCore (oneFormComponentCore 1 alpha)
      (covariantOneFormComponentCore (0, 0) beta) +
    scalarProductCore
      (horizontalDerivativeCore (oneFormComponentCore 1 alpha))
      (covariantOneFormComponentCore (0, 1) beta) +
    scalarProductCore (oneFormComponentCore 0 alpha)
      (covariantOneFormComponentCore (0, 1) beta) +
    scalarProductCore
      (verticalDerivativeCore (oneFormComponentCore 0 alpha))
      (covariantOneFormComponentCore (1, 0) beta) +
    scalarProductCore
      (verticalDerivativeCore (oneFormComponentCore 1 alpha))
      (covariantOneFormComponentCore (1, 1) beta)

/-- The pointwise pairing with the compact-core covariant adjoint. -/
noncomputable def covariantAdjointPairingCore
    (alpha : HyperbolicSmoothCompactOneForm)
    (beta : HyperbolicSmoothCompactCovariantOneForm) :
    HyperbolicSmoothCompactScalar :=
  -scalarProductCore (oneFormComponentCore 0 alpha)
      (horizontalDerivativeCore (covariantOneFormComponentCore (0, 0) beta)) +
    scalarProductCore (oneFormComponentCore 0 alpha)
      (covariantOneFormComponentCore (0, 1) beta) -
    scalarProductCore (oneFormComponentCore 0 alpha)
      (verticalDerivativeCore (covariantOneFormComponentCore (1, 0) beta)) +
    scalarProductCore (oneFormComponentCore 0 alpha)
      (covariantOneFormComponentCore (1, 0) beta) -
    scalarProductCore (oneFormComponentCore 1 alpha)
      (covariantOneFormComponentCore (0, 0) beta) -
    scalarProductCore (oneFormComponentCore 1 alpha)
      (horizontalDerivativeCore (covariantOneFormComponentCore (0, 1) beta)) -
    scalarProductCore (oneFormComponentCore 1 alpha)
      (verticalDerivativeCore (covariantOneFormComponentCore (1, 1) beta)) +
    scalarProductCore (oneFormComponentCore 1 alpha)
      (covariantOneFormComponentCore (1, 1) beta)

theorem covariantPairingCore_apply
    (alpha : HyperbolicSmoothCompactOneForm)
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    covariantPairingCore alpha beta p =
      inner ℝ (oneFormCovariantDerivativeCore alpha p) (beta p) := by
  change
    horizontalDerivative (fun q ↦ alpha q 0) p * beta p (0, 0) -
          alpha p 1 * beta p (0, 0) +
        horizontalDerivative (fun q ↦ alpha q 1) p * beta p (0, 1) +
      alpha p 0 * beta p (0, 1) +
      verticalDerivative (fun q ↦ alpha q 0) p * beta p (1, 0) +
      verticalDerivative (fun q ↦ alpha q 1) p * beta p (1, 1) = _
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Real.inner_apply,
    oneFormCovariantDerivativeCore_apply_00,
    oneFormCovariantDerivativeCore_apply_01,
    oneFormCovariantDerivativeCore_apply_10,
    oneFormCovariantDerivativeCore_apply_11]
  ring

theorem covariantAdjointPairingCore_apply
    (alpha : HyperbolicSmoothCompactOneForm)
    (beta : HyperbolicSmoothCompactCovariantOneForm) (p : HyperbolicPlane) :
    covariantAdjointPairingCore alpha beta p =
      inner ℝ (alpha p) (oneFormCovariantAdjointCore beta p) := by
  change
    -(alpha p 0 * horizontalDerivative (fun q ↦ beta q (0, 0)) p) +
          alpha p 0 * beta p (0, 1) -
        alpha p 0 * verticalDerivative (fun q ↦ beta q (1, 0)) p +
      alpha p 0 * beta p (1, 0) -
      alpha p 1 * beta p (0, 0) -
      alpha p 1 * horizontalDerivative (fun q ↦ beta q (0, 1)) p -
      alpha p 1 * verticalDerivative (fun q ↦ beta q (1, 1)) p +
      alpha p 1 * beta p (1, 1) = _
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
    oneFormCovariantAdjointCore_apply_zero,
    oneFormCovariantAdjointCore_apply_one,
    covariantAdjointComponentZeroCore_apply,
    covariantAdjointComponentOneCore_apply]
  ring

theorem smoothCompactIntegral_covariantPairing
    (alpha : HyperbolicSmoothCompactOneForm)
    (beta : HyperbolicSmoothCompactCovariantOneForm) :
    smoothCompactIntegral (covariantPairingCore alpha beta) =
      smoothCompactIntegral (covariantAdjointPairingCore alpha beta) := by
  have h00 := smoothCompactIntegral_horizontalDerivative_mul
    (oneFormComponentCore 0 alpha) (covariantOneFormComponentCore (0, 0) beta)
  have h01 := smoothCompactIntegral_horizontalDerivative_mul
    (oneFormComponentCore 1 alpha) (covariantOneFormComponentCore (0, 1) beta)
  have h10 := smoothCompactIntegral_verticalDerivative_mul_expanded
    (oneFormComponentCore 0 alpha) (covariantOneFormComponentCore (1, 0) beta)
  have h11 := smoothCompactIntegral_verticalDerivative_mul_expanded
    (oneFormComponentCore 1 alpha) (covariantOneFormComponentCore (1, 1) beta)
  simp only [covariantPairingCore, covariantAdjointPairingCore,
    map_add, map_sub, map_neg] at *
  linarith only [h00, h01, h10, h11]

/-- Compactly supported covariant differentiation and the displayed core operator are formal
adjoints in the actual measured `L²` pairings. -/
theorem hyperbolicNablaOne_core_pairing
    (alpha : HyperbolicSmoothCompactOneForm)
    (beta : HyperbolicSmoothCompactCovariantOneForm) :
    inner ℝ (hyperbolicNablaOneCoreL2 alpha)
        (hyperbolicSmoothCompactToL2 beta) =
      inner ℝ (hyperbolicSmoothCompactToL2 alpha)
        (hyperbolicSmoothCompactToL2 (oneFormCovariantAdjointCore beta)) := by
  change inner ℝ (oneFormCovariantDerivativeCore alpha).toL2 beta.toL2 =
    inner ℝ alpha.toL2 (oneFormCovariantAdjointCore beta).toL2
  rw [inner_smoothCompact_toL2, inner_smoothCompact_toL2]
  calc
    (∫ p, inner ℝ (oneFormCovariantDerivativeCore alpha p) (beta p)
        ∂hyperbolicVolume) =
        smoothCompactIntegral (covariantPairingCore alpha beta) := by
      rw [smoothCompactIntegral_apply]
      apply integral_congr_ae
      filter_upwards with p
      exact (covariantPairingCore_apply alpha beta p).symm
    _ = smoothCompactIntegral (covariantAdjointPairingCore alpha beta) :=
      smoothCompactIntegral_covariantPairing alpha beta
    _ = ∫ p, inner ℝ (alpha p) (oneFormCovariantAdjointCore beta p)
          ∂hyperbolicVolume := by
      rw [smoothCompactIntegral_apply]
      apply integral_congr_ae
      filter_upwards with p
      exact covariantAdjointPairingCore_apply alpha beta p

/-! ## Closed covariant derivative and the CCP25 `H¹` carrier -/

/-- Compact-core covariant adjoint with values in one-form `L²`. -/
noncomputable def hyperbolicNablaOneAdjointCoreL2 :
    HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ] HyperbolicOneFormL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).comp
      oneFormCovariantAdjointCore

/-- Densely defined compact-core formal adjoint of `hyperbolicNablaOne`. -/
noncomputable def hyperbolicNablaOneAdjoint :
    HyperbolicCovariantOneFormL2 →ₗ.[ℝ] HyperbolicOneFormL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactCovariantOneForm →ₗ[ℝ]
        HyperbolicCovariantOneFormL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicNablaOneAdjointCoreL2

theorem hyperbolicNablaOne_isFormalAdjoint :
    hyperbolicNablaOne.IsFormalAdjoint hyperbolicNablaOneAdjoint := by
  intro x y
  rcases x.property with ⟨alpha, halpha⟩
  rcases y.property with ⟨beta, hbeta⟩
  let xCore : hyperbolicNablaOne.domain :=
    ⟨hyperbolicSmoothCompactToL2 alpha, ⟨alpha, rfl⟩⟩
  let yCore : hyperbolicNablaOneAdjoint.domain :=
    ⟨hyperbolicSmoothCompactToL2 beta, ⟨beta, rfl⟩⟩
  have hx : x = xCore := by
    apply Subtype.ext
    exact halpha.symm
  have hy : y = yCore := by
    apply Subtype.ext
    exact hbeta.symm
  rw [hx, hy]
  simpa only [xCore, yCore, hyperbolicNablaOne,
    hyperbolicNablaOneAdjoint, hyperbolicNablaOneAdjointCoreL2,
    LinearMap.coe_comp, Function.comp_apply,
    linearPMapOfInjectiveCore_apply,
    Subtype.coe_mk] using hyperbolicNablaOne_core_pairing alpha beta

theorem hyperbolicNablaOneAdjoint_dense_domain :
    Dense (hyperbolicNablaOneAdjoint.domain : Set HyperbolicCovariantOneFormL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _
    hyperbolicSmoothCompactSection_dense

/-- The concrete covariant derivative is closable; this follows from its proved densely defined
formal adjoint, not from an analytic assumption. -/
theorem hyperbolicNablaOne_isClosable : hyperbolicNablaOne.IsClosable :=
  isClosable_of_formalAdjoint hyperbolicNablaOne_isFormalAdjoint
    hyperbolicNablaOneAdjoint_dense_domain

/-- The minimal closed covariant derivative of one-forms on the complete hyperbolic plane. -/
noncomputable def hyperbolicNablaOneClosed :
    DenselyDefinedClosedLinearOperator ℝ HyperbolicOneFormL2
      HyperbolicCovariantOneFormL2 :=
  DenselyDefinedClosedLinearOperator.ofClosable hyperbolicNablaOne
    hyperbolicNablaOne_isClosable hyperbolicNablaOne_dense_domain

/-- CCP25's one-form `H¹` Hilbert carrier: the graph of the minimal closed covariant derivative.
Its inner product is literally `(alpha,beta)₂ + (nabla alpha,nabla beta)₂`. -/
abbrev HyperbolicCovariantGraphH1 :=
  hyperbolicNablaOneClosed.toClosedLinearOperator.GraphSpace

noncomputable instance hyperbolicCovariantGraphH1Complete :
    CompleteSpace HyperbolicCovariantGraphH1 := inferInstance

/-- Continuous inclusion from source-normalized `H¹` into one-form `L²`. -/
noncomputable def hyperbolicCovariantGraphH1ToL2 :
    HyperbolicCovariantGraphH1 →L[ℝ] HyperbolicOneFormL2 :=
  hyperbolicNablaOneClosed.toClosedLinearOperator.base

/-- Continuous closed covariant derivative on source-normalized `H¹`. -/
noncomputable def hyperbolicCovariantGraphH1Nabla :
    HyperbolicCovariantGraphH1 →L[ℝ] HyperbolicCovariantOneFormL2 :=
  hyperbolicNablaOneClosed.toClosedLinearOperator.value

/-- A compactly supported smooth one-form as an element of the closed covariant domain. -/
noncomputable def hyperbolicNablaOneClosedCoreDomain
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicNablaOneClosed.operator.domain :=
  ⟨hyperbolicSmoothCompactToL2 alpha,
    hyperbolicNablaOne.le_closure.1 ⟨alpha, rfl⟩⟩

/-- The core inclusion into the closed covariant domain is linear. -/
noncomputable def hyperbolicNablaOneClosedCoreDomainLinear :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ]
      hyperbolicNablaOneClosed.operator.domain where
  toFun := hyperbolicNablaOneClosedCoreDomain
  map_add' alpha beta := by
    apply Subtype.ext
    exact (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).map_add alpha beta
  map_smul' c alpha := by
    apply Subtype.ext
    exact (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).map_smul c alpha

/-- Canonical inclusion of the smooth compact one-form core into source-normalized `H¹`. -/
noncomputable def hyperbolicSmoothCompactOneFormToCovariantGraphH1 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicCovariantGraphH1 :=
  (hyperbolicNablaOneClosed.toClosedLinearOperator.domainGraphLinearEquiv).toLinearMap.comp
    hyperbolicNablaOneClosedCoreDomainLinear

@[simp] theorem hyperbolicSmoothCompactOneFormToCovariantGraphH1_apply
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha =
      hyperbolicNablaOneClosed.toClosedLinearOperator.graphMk
        (hyperbolicNablaOneClosedCoreDomain alpha) :=
  rfl

@[simp] theorem hyperbolicCovariantGraphH1ToL2_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicCovariantGraphH1ToL2 (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha) =
      hyperbolicSmoothCompactToL2 alpha := by
  simp only [hyperbolicCovariantGraphH1ToL2,
    hyperbolicSmoothCompactOneFormToCovariantGraphH1_apply,
    ClosedLinearOperator.base_graphMk]
  rfl

@[simp] theorem hyperbolicCovariantGraphH1Nabla_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicCovariantGraphH1Nabla (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha) =
      hyperbolicNablaOneCoreL2 alpha := by
  simp only [hyperbolicCovariantGraphH1Nabla,
    hyperbolicSmoothCompactOneFormToCovariantGraphH1_apply,
    ClosedLinearOperator.value_graphMk]
  change hyperbolicNablaOne.closure (hyperbolicNablaOneClosedCoreDomain alpha) = _
  let coreDomain : hyperbolicNablaOne.domain :=
    ⟨hyperbolicSmoothCompactToL2 alpha, ⟨alpha, rfl⟩⟩
  have hvalue := hyperbolicNablaOne.le_closure.2
    (x := coreDomain) (y := hyperbolicNablaOneClosedCoreDomain alpha) rfl
  symm
  simpa only [coreDomain, hyperbolicNablaOne,
    linearPMapOfInjectiveCore_apply, Subtype.coe_mk] using hvalue

/-- The graph inner product is exactly CCP25 Definition 2.6 on the smooth compact core. -/
theorem inner_hyperbolicSmoothCompactOneFormToCovariantGraphH1
    (alpha beta : HyperbolicSmoothCompactOneForm) :
    inner ℝ (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha)
        (hyperbolicSmoothCompactOneFormToCovariantGraphH1 beta) =
      inner ℝ (hyperbolicSmoothCompactToL2 alpha)
          (hyperbolicSmoothCompactToL2 beta) +
        inner ℝ (hyperbolicNablaOneCoreL2 alpha)
          (hyperbolicNablaOneCoreL2 beta) := by
  calc
    inner ℝ (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha)
        (hyperbolicSmoothCompactOneFormToCovariantGraphH1 beta) =
      inner ℝ
          (hyperbolicCovariantGraphH1ToL2 (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha))
          (hyperbolicCovariantGraphH1ToL2 (hyperbolicSmoothCompactOneFormToCovariantGraphH1 beta)) +
        inner ℝ
          (hyperbolicCovariantGraphH1Nabla (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha))
          (hyperbolicCovariantGraphH1Nabla (hyperbolicSmoothCompactOneFormToCovariantGraphH1 beta)) :=
      ClosedLinearOperator.inner_graph _ _ _
    _ = _ := by rw [hyperbolicCovariantGraphH1ToL2_core,
      hyperbolicCovariantGraphH1ToL2_core, hyperbolicCovariantGraphH1Nabla_core,
      hyperbolicCovariantGraphH1Nabla_core]

/-- On the smooth core the source `H¹` norm is exactly the curvature-weighted Hodge graph norm.
This is the `N=2`, `k=1`, `a=1` specialization of CCP25 Lemma 2.7. -/
theorem norm_sq_hyperbolicSmoothCompactOneFormToCovariantGraphH1
    (alpha : HyperbolicSmoothCompactOneForm) :
    ‖hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha‖ ^ 2 =
      2 * ‖hyperbolicSmoothCompactToL2 alpha‖ ^ 2 +
        ‖hyperbolicHodgeOneCoreL2 alpha‖ ^ 2 := by
  calc
    ‖hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha‖ ^ 2 =
      ‖hyperbolicCovariantGraphH1ToL2
          (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha)‖ ^ 2 +
        ‖hyperbolicCovariantGraphH1Nabla
          (hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha)‖ ^ 2 :=
      ClosedLinearOperator.norm_sq_graph _ _
    _ = ‖hyperbolicSmoothCompactToL2 alpha‖ ^ 2 +
        ‖hyperbolicNablaOneCoreL2 alpha‖ ^ 2 := by
      rw [hyperbolicCovariantGraphH1ToL2_core, hyperbolicCovariantGraphH1Nabla_core]
    _ = _ := by
      rw [hyperbolicBochnerWeitzenbockCore_norm_sq]
      ring

/-- The packed Hodge derivative has squared norm equal to the sum of the exterior and
codifferential squared norms. -/
theorem norm_sq_hyperbolicHodgeOneCoreL2
    (alpha : HyperbolicSmoothCompactOneForm) :
    ‖hyperbolicHodgeOneCoreL2 alpha‖ ^ 2 =
      ‖hyperbolicDOneCoreL2 alpha‖ ^ 2 +
        ‖hyperbolicDeltaOneCoreL2 alpha‖ ^ 2 := by
  change ‖(oneFormHodgeDerivativeCore alpha).toL2‖ ^ 2 =
    ‖(oneFormExteriorDerivativeCore alpha).toL2‖ ^ 2 +
      ‖(oneFormCodifferentialCore alpha).toL2‖ ^ 2
  rw [norm_sq_smoothCompact_toL2, norm_sq_smoothCompact_toL2,
    norm_sq_smoothCompact_toL2]
  calc
    (∫ p, ‖oneFormHodgeDerivativeCore alpha p‖ ^ 2 ∂hyperbolicVolume) =
        smoothCompactIntegral (hodgeEnergyDensityCore alpha) := by
      rw [smoothCompactIntegral_apply]
      apply integral_congr_ae
      filter_upwards with p
      exact (hodgeEnergyDensityCore_apply alpha p).symm
    _ = smoothCompactIntegral (squareCore (oneFormExteriorDerivativeCore alpha)) +
        smoothCompactIntegral (squareCore (oneFormCodifferentialCore alpha)) := by
      simp only [hodgeEnergyDensityCore, map_add]
    _ = (∫ p, ‖oneFormExteriorDerivativeCore alpha p‖ ^ 2
          ∂hyperbolicVolume) +
        ∫ p, ‖oneFormCodifferentialCore alpha p‖ ^ 2
          ∂hyperbolicVolume := by
      simp only [smoothCompactIntegral_apply, Real.norm_eq_abs, sq_abs,
        squareCore_apply]

/-- Fully expanded source normalization from CCP25 Lemma 2.7. -/
theorem norm_sq_hyperbolicSmoothCompactOneFormToCovariantGraphH1_expanded
    (alpha : HyperbolicSmoothCompactOneForm) :
    ‖hyperbolicSmoothCompactOneFormToCovariantGraphH1 alpha‖ ^ 2 =
      2 * ‖hyperbolicSmoothCompactToL2 alpha‖ ^ 2 +
        ‖hyperbolicDOneCoreL2 alpha‖ ^ 2 +
        ‖hyperbolicDeltaOneCoreL2 alpha‖ ^ 2 := by
  rw [norm_sq_hyperbolicSmoothCompactOneFormToCovariantGraphH1,
    norm_sq_hyperbolicHodgeOneCoreL2]
  ring

/-- Bilinear Bochner--Weitzenbock identity obtained by real polarization of the proved norm
identity. -/
theorem inner_hyperbolicNablaOneCoreL2
    (alpha beta : HyperbolicSmoothCompactOneForm) :
    inner ℝ (hyperbolicNablaOneCoreL2 alpha)
        (hyperbolicNablaOneCoreL2 beta) =
      inner ℝ (hyperbolicHodgeOneCoreL2 alpha)
          (hyperbolicHodgeOneCoreL2 beta) +
        inner ℝ (hyperbolicSmoothCompactToL2 alpha)
          (hyperbolicSmoothCompactToL2 beta) := by
  have hsum := hyperbolicBochnerWeitzenbockCore_norm_sq (alpha + beta)
  have halpha := hyperbolicBochnerWeitzenbockCore_norm_sq alpha
  have hbeta := hyperbolicBochnerWeitzenbockCore_norm_sq beta
  simp only [map_add, norm_add_sq_real] at hsum
  linarith only [hsum, halpha, hbeta]

/-! ## Concrete source completion with continuous Hodge coordinates -/

/-- Ambient Hilbert space used to realize the source completion.  The first coordinate is the
one-form itself; the second contains a duplicate of the one-form and its packed `(d,delta)`
derivative.  Consequently the ambient norm squared is exactly
`2‖alpha‖₂² + ‖(d alpha,delta alpha)‖₂²`. -/
abbrev HyperbolicOneFormH1Ambient :=
  WithLp 2 (HyperbolicOneFormL2 ×
    WithLp 2 (HyperbolicOneFormL2 × HyperbolicOneFormL2))

/-- Isometric source-core model supplied by the Bochner--Weitzenbock identity. -/
noncomputable def hyperbolicOneFormH1CoreAmbient :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormH1Ambient :=
  (WithLp.linearEquiv 2 ℝ
      (HyperbolicOneFormL2 ×
        WithLp 2 (HyperbolicOneFormL2 × HyperbolicOneFormL2))).symm.toLinearMap.comp
    ((hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).prod
      ((WithLp.linearEquiv 2 ℝ
          (HyperbolicOneFormL2 × HyperbolicOneFormL2)).symm.toLinearMap.comp
        ((hyperbolicSmoothCompactToL2 :
            HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).prod
          hyperbolicHodgeOneCoreL2)))

@[simp] theorem hyperbolicOneFormH1CoreAmbient_apply
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormH1CoreAmbient alpha =
      WithLp.toLp 2
        (hyperbolicSmoothCompactToL2 alpha,
          WithLp.toLp 2
            (hyperbolicSmoothCompactToL2 alpha,
              hyperbolicHodgeOneCoreL2 alpha)) :=
  rfl

/-- CCP25's source-normalized one-form `H¹`: the closure of compact smooth one-forms in a
concrete Hilbert model whose norm is exactly `(alpha,alpha)₂ + (nabla alpha,nabla alpha)₂`. -/
noncomputable abbrev HyperbolicOneFormH1 : Submodule ℝ HyperbolicOneFormH1Ambient :=
  (LinearMap.range hyperbolicOneFormH1CoreAmbient).topologicalClosure

/-- A named induced inner product keeps the scalar-module instance coherent for downstream
orthogonal-complement constructions on the completion subtype. -/
noncomputable instance (priority := 2000) hyperbolicOneFormH1InnerProductSpace :
    InnerProductSpace ℝ HyperbolicOneFormH1 :=
  Submodule.innerProductSpace HyperbolicOneFormH1

noncomputable instance (priority := 2000) hyperbolicOneFormH1Module :
    Module ℝ HyperbolicOneFormH1 :=
  hyperbolicOneFormH1InnerProductSpace.toNormedSpace.toModule

noncomputable instance hyperbolicOneFormH1Complete : CompleteSpace HyperbolicOneFormH1 :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range hyperbolicOneFormH1CoreAmbient)

/-- Canonical dense inclusion of compact smooth one-forms into the source completion. -/
noncomputable def hyperbolicSmoothCompactOneFormToH1 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormH1 :=
  LinearMap.codRestrict HyperbolicOneFormH1 hyperbolicOneFormH1CoreAmbient fun alpha ↦
    (Submodule.le_topologicalClosure
      (s := LinearMap.range hyperbolicOneFormH1CoreAmbient)) ⟨alpha, rfl⟩

/-- Compactly supported smooth one-forms have dense range in the source-defined `H¹`
completion.  This is the public density theorem corresponding to CCP25 Definition 2.6. -/
theorem hyperbolicSmoothCompactOneFormToH1_denseRange :
    DenseRange hyperbolicSmoothCompactOneFormToH1 := by
  let s : Set HyperbolicOneFormH1Ambient :=
    Set.range hyperbolicOneFormH1CoreAmbient
  let t : Set HyperbolicOneFormH1Ambient := closure s
  have hi : s ⊆ t := subset_closure
  have hinc : DenseRange (Set.inclusion hi) :=
    (denseRange_inclusion_iff hi).2 subset_rfl
  have hfactor : DenseRange
      (Set.rangeFactorization
        (hyperbolicOneFormH1CoreAmbient :
          HyperbolicSmoothCompactOneForm → HyperbolicOneFormH1Ambient)) :=
    Set.rangeFactorization_surjective.denseRange
  exact hinc.comp hfactor (continuous_inclusion hi)

@[simp] theorem hyperbolicSmoothCompactOneFormToH1_coe
    (alpha : HyperbolicSmoothCompactOneForm) :
    (hyperbolicSmoothCompactOneFormToH1 alpha : HyperbolicOneFormH1Ambient) =
      hyperbolicOneFormH1CoreAmbient alpha :=
  rfl

/-- Continuous inclusion of source `H¹` into the actual one-form `L²` quotient. -/
noncomputable def hyperbolicOneFormH1ToL2 :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormL2 :=
  (WithLp.fstL 2 ℝ HyperbolicOneFormL2
      (WithLp 2 (HyperbolicOneFormL2 × HyperbolicOneFormL2))).comp
    (Submodule.subtypeL HyperbolicOneFormH1)

/-- The duplicated `L²` coordinate used to encode the curvature contribution in the source
norm.  It agrees with `hyperbolicOneFormH1ToL2` on the whole completion. -/
noncomputable def hyperbolicOneFormH1DuplicateL2 :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormL2 :=
  (WithLp.fstL 2 ℝ HyperbolicOneFormL2 HyperbolicOneFormL2).comp
    ((WithLp.sndL 2 ℝ HyperbolicOneFormL2
      (WithLp 2 (HyperbolicOneFormL2 × HyperbolicOneFormL2))).comp
        (Submodule.subtypeL HyperbolicOneFormH1))

/-- Continuous packed Hodge derivative `(d,delta)` on source `H¹`. -/
noncomputable def hyperbolicOneFormH1Hodge :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormL2 :=
  (WithLp.sndL 2 ℝ HyperbolicOneFormL2 HyperbolicOneFormL2).comp
    ((WithLp.sndL 2 ℝ HyperbolicOneFormL2
      (WithLp 2 (HyperbolicOneFormL2 × HyperbolicOneFormL2))).comp
        (Submodule.subtypeL HyperbolicOneFormH1))

@[simp] theorem hyperbolicOneFormH1ToL2_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormH1ToL2 (hyperbolicSmoothCompactOneFormToH1 alpha) =
      hyperbolicSmoothCompactToL2 alpha :=
  rfl

@[simp] theorem hyperbolicOneFormH1DuplicateL2_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormH1DuplicateL2 (hyperbolicSmoothCompactOneFormToH1 alpha) =
      hyperbolicSmoothCompactToL2 alpha :=
  rfl

@[simp] theorem hyperbolicOneFormH1Hodge_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormH1Hodge (hyperbolicSmoothCompactOneFormToH1 alpha) =
      hyperbolicHodgeOneCoreL2 alpha :=
  rfl

/-- The two ambient copies of the one-form coefficient remain equal after completion. -/
theorem hyperbolicOneFormH1DuplicateL2_eq_toL2 :
    hyperbolicOneFormH1DuplicateL2 = hyperbolicOneFormH1ToL2 := by
  have hfun := hyperbolicSmoothCompactOneFormToH1_denseRange.equalizer
    hyperbolicOneFormH1DuplicateL2.continuous
    hyperbolicOneFormH1ToL2.continuous (by
      funext alpha
      simp only [Function.comp_apply,
        hyperbolicOneFormH1DuplicateL2_core,
        hyperbolicOneFormH1ToL2_core])
  exact ContinuousLinearMap.ext fun u ↦ congrFun hfun u

/-- Coordinate projection on the one-form `L²` coefficient carrier. -/
noncomputable def hyperbolicOneFormL2Component (i : Fin 2) :
    HyperbolicOneFormL2 →L[ℝ] HyperbolicScalarL2 :=
  (EuclideanSpace.proj i).compLpL 2 hyperbolicVolume

theorem hyperbolicOneFormL2Component_smoothCompact
    (i : Fin 2) (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormL2Component i alpha.toL2 =
      (oneFormComponentCore i alpha).toL2 := by
  apply Lp.ext
  filter_upwards [
      (EuclideanSpace.proj i :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' alpha.toL2,
      alpha.toL2_coe,
      (oneFormComponentCore i alpha).toL2_coe] with p hproj halpha hcomponent
  change ((EuclideanSpace.proj i :
      HyperbolicOneFormComponents →L[ℝ] ℝ).compLp alpha.toL2) p =
    (oneFormComponentCore i alpha).toL2 p
  rw [hproj, hcomponent, halpha]
  rfl

/-- The two scalar coefficient projections jointly separate one-form `L²` classes. -/
theorem hyperbolicOneFormL2_eq_zero_of_components
    (w : HyperbolicOneFormL2)
    (hzero : hyperbolicOneFormL2Component 0 w = 0)
    (hone : hyperbolicOneFormL2Component 1 w = 0) :
    w = 0 := by
  apply Lp.ext
  filter_upwards [
      (EuclideanSpace.proj (0 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' w,
      (EuclideanSpace.proj (1 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' w]
      with p hprojZero hprojOne
  apply PiLp.ext
  intro i
  fin_cases i
  · have hval := congrArg (fun q : HyperbolicScalarL2 ↦ q p) hzero
    change ((EuclideanSpace.proj (0 : Fin 2) :
      HyperbolicOneFormComponents →L[ℝ] ℝ).compLp w) p =
        (0 : HyperbolicScalarL2) p at hval
    rw [hprojZero] at hval
    simpa using hval
  · have hval := congrArg (fun q : HyperbolicScalarL2 ↦ q p) hone
    change ((EuclideanSpace.proj (1 : Fin 2) :
      HyperbolicOneFormComponents →L[ℝ] ℝ).compLp w) p =
        (0 : HyperbolicScalarL2) p at hval
    rw [hprojOne] at hval
    simpa using hval

/-- The one-form `L²` pairing is the sum of the two scalar coefficient pairings. -/
theorem inner_hyperbolicOneFormL2_components (w z : HyperbolicOneFormL2) :
    inner ℝ w z =
      inner ℝ (hyperbolicOneFormL2Component 0 w)
          (hyperbolicOneFormL2Component 0 z) +
        inner ℝ (hyperbolicOneFormL2Component 1 w)
          (hyperbolicOneFormL2Component 1 z) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def,
    ← integral_add
      (MeasureTheory.L2.integrable_inner (hyperbolicOneFormL2Component 0 w)
        (hyperbolicOneFormL2Component 0 z))
      (MeasureTheory.L2.integrable_inner (hyperbolicOneFormL2Component 1 w)
        (hyperbolicOneFormL2Component 1 z))]
  apply integral_congr_ae
  filter_upwards [
      (EuclideanSpace.proj (0 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' w,
      (EuclideanSpace.proj (0 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' z,
      (EuclideanSpace.proj (1 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' w,
      (EuclideanSpace.proj (1 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).coeFn_compLp' z]
      with p hw0 hz0 hw1 hz1
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Real.inner_apply, hyperbolicOneFormL2Component]
  change w p 0 * z p 0 + w p 1 * z p 1 =
    ((EuclideanSpace.proj (0 : Fin 2) :
      HyperbolicOneFormComponents →L[ℝ] ℝ).compLp w) p *
      ((EuclideanSpace.proj (0 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).compLp z) p +
    ((EuclideanSpace.proj (1 : Fin 2) :
      HyperbolicOneFormComponents →L[ℝ] ℝ).compLp w) p *
      ((EuclideanSpace.proj (1 : Fin 2) :
        HyperbolicOneFormComponents →L[ℝ] ℝ).compLp z) p
  rw [hw0, hz0, hw1, hz1]
  rfl

/-- A scalar `L²` class vanishes when its pairing with every compact smooth scalar vanishes. -/
theorem hyperbolicScalarL2_eq_zero_of_inner_smoothCompact
    (w : HyperbolicScalarL2)
    (h : ∀ f : HyperbolicSmoothCompactScalar,
      inner ℝ (hyperbolicSmoothCompactToL2 f) w = 0) :
    w = 0 := by
  have hdense : DenseRange
      (hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactScalar → HyperbolicScalarL2) :=
    hyperbolicSmoothCompactScalar_dense
  have hfun : (fun v : HyperbolicScalarL2 ↦ inner ℝ v w) =
      fun _ : HyperbolicScalarL2 ↦ (0 : ℝ) :=
    hdense.equalizer
      (continuous_id.inner continuous_const) continuous_const (by
        funext f
        exact h f)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  exact congrFun hfun w

/-- Continuous weak exterior derivative `d : H¹(Λ¹) → L²(Λ²)`. -/
noncomputable def hyperbolicOneFormH1DOne :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicScalarL2 :=
  (hyperbolicOneFormL2Component 0).comp hyperbolicOneFormH1Hodge

/-- Continuous weak codifferential `delta : H¹(Λ¹) → L²(Λ⁰)`. -/
noncomputable def hyperbolicOneFormH1DeltaOne :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicScalarL2 :=
  (hyperbolicOneFormL2Component 1).comp hyperbolicOneFormH1Hodge

@[simp] theorem hyperbolicOneFormH1DOne_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormH1DOne (hyperbolicSmoothCompactOneFormToH1 alpha) =
      hyperbolicDOneCoreL2 alpha := by
  rw [hyperbolicOneFormH1DOne, ContinuousLinearMap.comp_apply,
    hyperbolicOneFormH1Hodge_core]
  change hyperbolicOneFormL2Component 0
      (oneFormHodgeDerivativeCore alpha).toL2 =
    (oneFormExteriorDerivativeCore alpha).toL2
  rw [hyperbolicOneFormL2Component_smoothCompact]
  apply congrArg HyperbolicSmoothCompactSection.toL2
  apply DFunLike.ext _ _
  intro p
  exact oneFormHodgeDerivativeCore_apply_zero alpha p

@[simp] theorem hyperbolicOneFormH1DeltaOne_core
    (alpha : HyperbolicSmoothCompactOneForm) :
    hyperbolicOneFormH1DeltaOne (hyperbolicSmoothCompactOneFormToH1 alpha) =
      hyperbolicDeltaOneCoreL2 alpha := by
  rw [hyperbolicOneFormH1DeltaOne, ContinuousLinearMap.comp_apply,
    hyperbolicOneFormH1Hodge_core]
  change hyperbolicOneFormL2Component 1
      (oneFormHodgeDerivativeCore alpha).toL2 =
    (oneFormCodifferentialCore alpha).toL2
  rw [hyperbolicOneFormL2Component_smoothCompact]
  apply congrArg HyperbolicSmoothCompactSection.toL2
  apply DFunLike.ext _ _
  intro p
  exact oneFormHodgeDerivativeCore_apply_one alpha p

/-- The packed Hodge derivative vanishes exactly when both weak de Rham components vanish. -/
theorem hyperbolicOneFormH1Hodge_eq_zero_iff (u : HyperbolicOneFormH1) :
    hyperbolicOneFormH1Hodge u = 0 ↔
      hyperbolicOneFormH1DOne u = 0 ∧
        hyperbolicOneFormH1DeltaOne u = 0 := by
  constructor
  · intro h
    constructor
    · simpa only [hyperbolicOneFormH1DOne, ContinuousLinearMap.comp_apply,
        map_zero] using congrArg (hyperbolicOneFormL2Component 0) h
    · simpa only [hyperbolicOneFormH1DeltaOne, ContinuousLinearMap.comp_apply,
        map_zero] using congrArg (hyperbolicOneFormL2Component 1) h
  · rintro ⟨hd, hdelta⟩
    apply hyperbolicOneFormL2_eq_zero_of_components
    · simpa only [hyperbolicOneFormH1DOne,
        ContinuousLinearMap.comp_apply] using hd
    · simpa only [hyperbolicOneFormH1DeltaOne,
        ContinuousLinearMap.comp_apply] using hdelta

/-! ## Weak de Rham identities on the completed source space -/

/-- The weak exterior derivative carried by `H¹` is the distributional exterior derivative of
its `L²` representative. -/
theorem hyperbolicOneFormH1DOne_deltaTwo_pairing
    (u : HyperbolicOneFormH1) (f : HyperbolicSmoothCompactScalar) :
    inner ℝ (hyperbolicOneFormH1DOne u) (hyperbolicSmoothCompactToL2 f) =
      inner ℝ (hyperbolicOneFormH1ToL2 u) (hyperbolicDeltaTwoCoreL2 f) := by
  have hfun :
      (fun v : HyperbolicOneFormH1 ↦
          inner ℝ (hyperbolicOneFormH1DOne v)
            (hyperbolicSmoothCompactToL2 f)) =
        fun v : HyperbolicOneFormH1 ↦
          inner ℝ (hyperbolicOneFormH1ToL2 v)
            (hyperbolicDeltaTwoCoreL2 f) :=
    hyperbolicSmoothCompactOneFormToH1_denseRange.equalizer
      (hyperbolicOneFormH1DOne.continuous.inner continuous_const)
      (hyperbolicOneFormH1ToL2.continuous.inner continuous_const) (by
        funext alpha
        simpa only [Function.comp_apply,
          hyperbolicOneFormH1DOne_core,
          hyperbolicOneFormH1ToL2_core] using
          hyperbolicDOne_deltaTwo_core_pairing alpha f)
  exact congrFun hfun u

/-- The weak codifferential carried by `H¹` is the distributional codifferential of its `L²`
representative. -/
theorem hyperbolicDZero_H1DeltaOne_pairing
    (f : HyperbolicSmoothCompactScalar) (u : HyperbolicOneFormH1) :
    inner ℝ (hyperbolicDZeroCoreL2 f) (hyperbolicOneFormH1ToL2 u) =
      inner ℝ (hyperbolicSmoothCompactToL2 f)
        (hyperbolicOneFormH1DeltaOne u) := by
  have hfun :
      (fun v : HyperbolicOneFormH1 ↦
          inner ℝ (hyperbolicDZeroCoreL2 f)
            (hyperbolicOneFormH1ToL2 v)) =
        fun v : HyperbolicOneFormH1 ↦
          inner ℝ (hyperbolicSmoothCompactToL2 f)
            (hyperbolicOneFormH1DeltaOne v) :=
    hyperbolicSmoothCompactOneFormToH1_denseRange.equalizer
      (continuous_const.inner hyperbolicOneFormH1ToL2.continuous)
      (continuous_const.inner hyperbolicOneFormH1DeltaOne.continuous) (by
        funext alpha
        simpa only [Function.comp_apply,
          hyperbolicOneFormH1ToL2_core,
          hyperbolicOneFormH1DeltaOne_core] using
          hyperbolicDZero_deltaOne_core_pairing f alpha)
  exact congrFun hfun u

/-- The completed Hilbert structure is exactly the polarized CCP25 norm: two copies of the
`L²` pairing plus the packed weak Hodge-derivative pairing. -/
theorem inner_hyperbolicOneFormH1 (u v : HyperbolicOneFormH1) :
    inner ℝ u v =
      2 * inner ℝ (hyperbolicOneFormH1ToL2 u)
          (hyperbolicOneFormH1ToL2 v) +
        inner ℝ (hyperbolicOneFormH1Hodge u)
          (hyperbolicOneFormH1Hodge v) := by
  change inner ℝ (u : HyperbolicOneFormH1Ambient)
      (v : HyperbolicOneFormH1Ambient) = _
  simp only [WithLp.prod_inner_apply, hyperbolicOneFormH1ToL2,
    hyperbolicOneFormH1Hodge, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, WithLp.fstL_apply, WithLp.sndL_apply]
  have hduplicate := DFunLike.congr_fun
    hyperbolicOneFormH1DuplicateL2_eq_toL2 u
  have hduplicate' := DFunLike.congr_fun
    hyperbolicOneFormH1DuplicateL2_eq_toL2 v
  change (u : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.1 =
      (u : HyperbolicOneFormH1Ambient).ofLp.1 at hduplicate
  change (v : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.1 =
      (v : HyperbolicOneFormH1Ambient).ofLp.1 at hduplicate'
  change
    inner ℝ (u : HyperbolicOneFormH1Ambient).ofLp.1
        (v : HyperbolicOneFormH1Ambient).ofLp.1 +
      (inner ℝ (u : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.1
          (v : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.1 +
        inner ℝ (u : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.2
          (v : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.2) =
      2 * inner ℝ (u : HyperbolicOneFormH1Ambient).ofLp.1
          (v : HyperbolicOneFormH1Ambient).ofLp.1 +
        inner ℝ (u : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.2
          (v : HyperbolicOneFormH1Ambient).ofLp.2.ofLp.2
  rw [hduplicate, hduplicate']
  ring

/-- Fully expanded completed source pairing in weak de Rham coordinates. -/
theorem inner_hyperbolicOneFormH1_expanded (u v : HyperbolicOneFormH1) :
    inner ℝ u v =
      2 * inner ℝ (hyperbolicOneFormH1ToL2 u)
          (hyperbolicOneFormH1ToL2 v) +
        inner ℝ (hyperbolicOneFormH1DOne u)
          (hyperbolicOneFormH1DOne v) +
        inner ℝ (hyperbolicOneFormH1DeltaOne u)
          (hyperbolicOneFormH1DeltaOne v) := by
  have hhodge := inner_hyperbolicOneFormL2_components
    (hyperbolicOneFormH1Hodge u) (hyperbolicOneFormH1Hodge v)
  rw [inner_hyperbolicOneFormH1, hhodge]
  simp only [hyperbolicOneFormH1DOne, hyperbolicOneFormH1DeltaOne,
    ContinuousLinearMap.comp_apply]
  ring

/-- Global source norm identity on the completed `H¹` carrier. -/
theorem norm_sq_hyperbolicOneFormH1 (u : HyperbolicOneFormH1) :
    ‖u‖ ^ 2 = 2 * ‖hyperbolicOneFormH1ToL2 u‖ ^ 2 +
      ‖hyperbolicOneFormH1Hodge u‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_hyperbolicOneFormH1 u u

/-- The public completion has exactly the source inner product on the compact core. -/
theorem inner_hyperbolicSmoothCompactOneFormToH1
    (alpha beta : HyperbolicSmoothCompactOneForm) :
    inner ℝ (hyperbolicSmoothCompactOneFormToH1 alpha)
        (hyperbolicSmoothCompactOneFormToH1 beta) =
      inner ℝ (hyperbolicSmoothCompactToL2 alpha)
          (hyperbolicSmoothCompactToL2 beta) +
        inner ℝ (hyperbolicNablaOneCoreL2 alpha)
          (hyperbolicNablaOneCoreL2 beta) := by
  change inner ℝ (hyperbolicSmoothCompactToL2 alpha)
        (hyperbolicSmoothCompactToL2 beta) +
      (inner ℝ (hyperbolicSmoothCompactToL2 alpha)
          (hyperbolicSmoothCompactToL2 beta) +
        inner ℝ (hyperbolicHodgeOneCoreL2 alpha)
          (hyperbolicHodgeOneCoreL2 beta)) = _
  rw [inner_hyperbolicNablaOneCoreL2]
  ring

/-- Exact source norm on the public completion core. -/
theorem norm_sq_hyperbolicSmoothCompactOneFormToH1
    (alpha : HyperbolicSmoothCompactOneForm) :
    ‖hyperbolicSmoothCompactOneFormToH1 alpha‖ ^ 2 =
      2 * ‖hyperbolicSmoothCompactToL2 alpha‖ ^ 2 +
        ‖hyperbolicHodgeOneCoreL2 alpha‖ ^ 2 := by
  change ‖WithLp.toLp 2
      (hyperbolicSmoothCompactToL2 alpha,
        WithLp.toLp 2
          (hyperbolicSmoothCompactToL2 alpha,
            hyperbolicHodgeOneCoreL2 alpha))‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  ring

theorem norm_sq_hyperbolicSmoothCompactOneFormToH1_expanded
    (alpha : HyperbolicSmoothCompactOneForm) :
    ‖hyperbolicSmoothCompactOneFormToH1 alpha‖ ^ 2 =
      2 * ‖hyperbolicSmoothCompactToL2 alpha‖ ^ 2 +
        ‖hyperbolicDOneCoreL2 alpha‖ ^ 2 +
        ‖hyperbolicDeltaOneCoreL2 alpha‖ ^ 2 := by
  rw [norm_sq_hyperbolicSmoothCompactOneFormToH1,
    norm_sq_hyperbolicHodgeOneCoreL2]
  ring

/-- The closed covariant derivative retains the original compactly supported smooth domain as a
Mathlib `HasCore`; equivalently, its graph is the closure of the compact-core graph. -/
theorem hyperbolicNablaOneClosed_hasSmoothCompactCore :
    hyperbolicNablaOneClosed.operator.HasCore hyperbolicNablaOne.domain :=
  ClosedLinearOperator.ofClosable_hasCore hyperbolicNablaOne
    hyperbolicNablaOne_isClosable

/-! ## The compact de Rham complex -/

/-- Exterior differentiation squares to zero from compactly supported scalars to top forms. -/
theorem oneFormExteriorDerivativeCore_scalarExteriorDerivativeCore
    (f : HyperbolicSmoothCompactScalar) :
    oneFormExteriorDerivativeCore (scalarExteriorDerivativeCore f) = 0 := by
  apply DFunLike.ext _ _
  intro p
  have hzero : (fun q ↦ scalarExteriorDerivativeCore f q 0) =
      (horizontalDerivativeCore f).toFun := by
    funext q
    exact scalarExteriorDerivativeCore_apply_zero f q
  have hone : (fun q ↦ scalarExteriorDerivativeCore f q 1) =
      (verticalDerivativeCore f).toFun := by
    funext q
    exact scalarExteriorDerivativeCore_apply_one f q
  rw [oneFormExteriorDerivativeCore_apply, hzero, hone,
    scalarExteriorDerivativeCore_apply_zero]
  change horizontalDerivative (verticalDerivativeCore f).toFun p +
      horizontalDerivative f.toFun p -
      verticalDerivative (horizontalDerivativeCore f).toFun p = (0 : ℝ)
  have hcomm := frameDerivative_commutator f p
  linarith

/-- The compact-core codifferential squares to zero from top forms to scalars. -/
theorem oneFormCodifferentialCore_twoFormCodifferentialCore
    (f : HyperbolicSmoothCompactScalar) :
    oneFormCodifferentialCore (twoFormCodifferentialCore f) = 0 := by
  apply DFunLike.ext _ _
  intro p
  have hzero : (fun q ↦ twoFormCodifferentialCore f q 0) =
      (verticalDerivativeCore f).toFun := by
    funext q
    exact twoFormCodifferentialCore_apply_zero f q
  have hone : (fun q ↦ twoFormCodifferentialCore f q 1) =
      (-horizontalDerivativeCore f).toFun := by
    funext q
    change twoFormCodifferentialCore f q 1 =
      -horizontalDerivative f.toFun q
    exact twoFormCodifferentialCore_apply_one f q
  rw [oneFormCodifferentialCore_apply, hzero, hone,
    twoFormCodifferentialCore_apply_one]
  have hvneg :
      verticalDerivative (-horizontalDerivativeCore f).toFun p =
        -verticalDerivative (horizontalDerivativeCore f).toFun p := by
    change (verticalDerivativeCoreLinear (-horizontalDerivativeCore f)) p =
      -(verticalDerivativeCoreLinear (horizontalDerivativeCore f)) p
    rw [map_neg]
    rfl
  rw [hvneg]
  change -horizontalDerivative (verticalDerivativeCore f).toFun p +
      -horizontalDerivative f.toFun p -
      -verticalDerivative (horizontalDerivativeCore f).toFun p = (0 : ℝ)
  have hcomm := frameDerivative_commutator f p
  linarith

end RiemannianFluids.HyperbolicPlane
