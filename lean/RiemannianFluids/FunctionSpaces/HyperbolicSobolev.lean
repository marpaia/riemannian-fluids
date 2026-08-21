import RiemannianFluids.FunctionSpaces.HyperbolicIntegrationByParts

/-!
# Closed hyperbolic de Rham operators and the concrete one-form Sobolev carrier

The frame integration-by-parts identities are promoted here to formal-adjoint relations on the
actual scalar and one-form `L²` quotients.  Consequently `d₀`, `d₁`, `δ₁`, `δ₂`, and the combined
Hodge derivative are closable without project assumptions.  Their closures supply the global
Hilbert-complex layer from which the source-matched `H¹` carrier is constructed.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open MeasureTheory
open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem inner_smoothCompact_toL2
    (f g : HyperbolicSmoothCompactSection F) :
    inner ℝ f.toL2 g.toL2 =
      ∫ p, inner ℝ (f p) (g p) ∂hyperbolicVolume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.toL2_coe, g.toL2_coe] with p hfp hgp
  rw [hfp, hgp]
  rfl

theorem integrable_smoothCompact_product
    (f g : HyperbolicSmoothCompactScalar) :
    Integrable (fun p ↦ f p * g p) hyperbolicVolume := by
  change Integrable (scalarProductCore f g).toFun hyperbolicVolume
  exact (scalarProductCore f g).contMDiff_toFun.continuous.integrable_of_hasCompactSupport
    (scalarProductCore f g).hasCompactSupport_toFun

theorem integrable_smoothCompact_inner
    (f g : HyperbolicSmoothCompactSection F) :
    Integrable (fun p ↦ inner ℝ (f p) (g p)) hyperbolicVolume := by
  apply (f.contMDiff_toFun.continuous.inner g.contMDiff_toFun.continuous)
    |>.integrable_of_hasCompactSupport
  exact f.hasCompactSupport_toFun.mono (by
    intro p hp hfp
    apply hp
    simp [hfp])

theorem integral_scalarExteriorDerivative_inner_eq_mul_codifferential
    (f : HyperbolicSmoothCompactScalar)
    (alpha : HyperbolicSmoothCompactOneForm) :
    (∫ p, inner ℝ (scalarExteriorDerivativeCore f p) (alpha p)
      ∂hyperbolicVolume) =
      ∫ p, f p * oneFormCodifferentialCore alpha p ∂hyperbolicVolume := by
  let a := oneFormComponentCore 0 alpha
  let b := oneFormComponentCore 1 alpha
  have hx :
      (∫ p, horizontalDerivative f.toFun p * a p ∂hyperbolicVolume) =
        -(∫ p, f p * horizontalDerivative a.toFun p ∂hyperbolicVolume) := by
    calc
      (∫ p, horizontalDerivative f.toFun p * a p ∂hyperbolicVolume) =
          ∫ p, a p * horizontalDerivative f.toFun p ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = -(∫ p, horizontalDerivative a.toFun p * f p ∂hyperbolicVolume) :=
        integral_mul_horizontalDerivative a f
      _ = -(∫ p, f p * horizontalDerivative a.toFun p ∂hyperbolicVolume) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        ring
  have hy :
      (∫ p, verticalDerivative f.toFun p * b p ∂hyperbolicVolume) =
        ∫ p, f p * (b p - verticalDerivative b.toFun p) ∂hyperbolicVolume := by
    calc
      (∫ p, verticalDerivative f.toFun p * b p ∂hyperbolicVolume) =
          ∫ p, b p * verticalDerivative f.toFun p ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = -(∫ p, (verticalDerivative b.toFun p - b p) * f p
            ∂hyperbolicVolume) := integral_mul_verticalDerivative b f
      _ = ∫ p, f p * (b p - verticalDerivative b.toFun p)
            ∂hyperbolicVolume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with p
        ring
  calc
    (∫ p, inner ℝ (scalarExteriorDerivativeCore f p) (alpha p)
        ∂hyperbolicVolume) =
        ∫ p, horizontalDerivative f.toFun p * a p +
          verticalDerivative f.toFun p * b p ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      rw [PiLp.inner_apply, Fin.sum_univ_two,
        scalarExteriorDerivativeCore_apply_zero,
        scalarExteriorDerivativeCore_apply_one]
      simp only [Real.inner_apply]
      rfl
    _ = (∫ p, horizontalDerivative f.toFun p * a p ∂hyperbolicVolume) +
        ∫ p, verticalDerivative f.toFun p * b p ∂hyperbolicVolume := by
      rw [integral_add]
      · exact integrable_smoothCompact_product (horizontalDerivativeCore f) a
      · exact integrable_smoothCompact_product (verticalDerivativeCore f) b
    _ = -(∫ p, f p * horizontalDerivative a.toFun p ∂hyperbolicVolume) +
        ∫ p, f p * (b p - verticalDerivative b.toFun p) ∂hyperbolicVolume := by
      rw [hx, hy]
    _ = ∫ p, -(f p * horizontalDerivative a.toFun p) +
        f p * (b p - verticalDerivative b.toFun p) ∂hyperbolicVolume := by
      rw [← integral_neg]
      exact (integral_add
        (integrable_smoothCompact_product f (horizontalDerivativeCore a)).neg
        (integrable_smoothCompact_product f (b - verticalDerivativeCore b))).symm
    _ = ∫ p, f p * oneFormCodifferentialCore alpha p ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      rw [oneFormCodifferentialCore_apply]
      change -(f p * horizontalDerivative a.toFun p) +
          f p * (b p - verticalDerivative b.toFun p) =
        f p * (-horizontalDerivative a.toFun p + b p -
          verticalDerivative b.toFun p)
      ring

theorem integral_oneFormExteriorDerivative_mul_eq_inner_twoFormCodifferential
    (alpha : HyperbolicSmoothCompactOneForm)
    (f : HyperbolicSmoothCompactScalar) :
    (∫ p, oneFormExteriorDerivativeCore alpha p * f p
      ∂hyperbolicVolume) =
      ∫ p, inner ℝ (alpha p) (twoFormCodifferentialCore f p)
        ∂hyperbolicVolume := by
  let a := oneFormComponentCore 0 alpha
  let b := oneFormComponentCore 1 alpha
  have hx :
      (∫ p, horizontalDerivative b.toFun p * f p ∂hyperbolicVolume) =
        ∫ p, b p * (-horizontalDerivative f.toFun p)
          ∂hyperbolicVolume := by
    have h := integral_mul_horizontalDerivative b f
    calc
      (∫ p, horizontalDerivative b.toFun p * f p ∂hyperbolicVolume) =
          -(∫ p, b p * horizontalDerivative f.toFun p
            ∂hyperbolicVolume) := by
        linarith only [h]
      _ = ∫ p, b p * (-horizontalDerivative f.toFun p)
          ∂hyperbolicVolume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with p
        ring
  have hy :
      (∫ p, (a p - verticalDerivative a.toFun p) * f p
        ∂hyperbolicVolume) =
        ∫ p, a p * verticalDerivative f.toFun p
          ∂hyperbolicVolume := by
    calc
      (∫ p, (a p - verticalDerivative a.toFun p) * f p
          ∂hyperbolicVolume) =
          -(∫ p, (verticalDerivative a.toFun p - a p) * f p
            ∂hyperbolicVolume) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = ∫ p, a p * verticalDerivative f.toFun p
          ∂hyperbolicVolume :=
        (integral_mul_verticalDerivative a f).symm
  calc
    (∫ p, oneFormExteriorDerivativeCore alpha p * f p
        ∂hyperbolicVolume) =
        ∫ p, horizontalDerivative b.toFun p * f p +
          (a p - verticalDerivative a.toFun p) * f p
          ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      rw [oneFormExteriorDerivativeCore_apply]
      change (horizontalDerivative b.toFun p + a p -
          verticalDerivative a.toFun p) * f p = _
      ring
    _ = (∫ p, horizontalDerivative b.toFun p * f p
          ∂hyperbolicVolume) +
        ∫ p, (a p - verticalDerivative a.toFun p) * f p
          ∂hyperbolicVolume := by
      rw [integral_add]
      · exact integrable_smoothCompact_product (horizontalDerivativeCore b) f
      · exact integrable_smoothCompact_product (a - verticalDerivativeCore a) f
    _ = (∫ p, b p * (-horizontalDerivative f.toFun p)
          ∂hyperbolicVolume) +
        ∫ p, a p * verticalDerivative f.toFun p
          ∂hyperbolicVolume := by
      rw [hx, hy]
    _ = ∫ p, b p * (-horizontalDerivative f.toFun p) +
        a p * verticalDerivative f.toFun p ∂hyperbolicVolume := by
      exact (integral_add
        (integrable_smoothCompact_product b (-horizontalDerivativeCore f))
        (integrable_smoothCompact_product a (verticalDerivativeCore f))).symm
    _ = ∫ p, inner ℝ (alpha p) (twoFormCodifferentialCore f p)
        ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      rw [PiLp.inner_apply, Fin.sum_univ_two,
        twoFormCodifferentialCore_apply_zero,
        twoFormCodifferentialCore_apply_one]
      simp only [Real.inner_apply]
      simp only [a, b, oneFormComponentCore_apply]
      ring

theorem hyperbolicDZero_deltaOne_core_pairing
    (f : HyperbolicSmoothCompactScalar)
    (alpha : HyperbolicSmoothCompactOneForm) :
    inner ℝ (hyperbolicDZeroCoreL2 f)
        (hyperbolicSmoothCompactToL2 alpha) =
      inner ℝ (hyperbolicSmoothCompactToL2 f)
        (hyperbolicDeltaOneCoreL2 alpha) := by
  change inner ℝ (scalarExteriorDerivativeCore f).toL2 alpha.toL2 =
    inner ℝ f.toL2 (oneFormCodifferentialCore alpha).toL2
  rw [inner_smoothCompact_toL2, inner_smoothCompact_toL2]
  simp only [Real.inner_apply]
  exact integral_scalarExteriorDerivative_inner_eq_mul_codifferential f alpha

theorem hyperbolicDOne_deltaTwo_core_pairing
    (alpha : HyperbolicSmoothCompactOneForm)
    (f : HyperbolicSmoothCompactScalar) :
    inner ℝ (hyperbolicDOneCoreL2 alpha)
        (hyperbolicSmoothCompactToL2 f) =
      inner ℝ (hyperbolicSmoothCompactToL2 alpha)
        (hyperbolicDeltaTwoCoreL2 f) := by
  change inner ℝ (oneFormExteriorDerivativeCore alpha).toL2 f.toL2 =
    inner ℝ alpha.toL2 (twoFormCodifferentialCore f).toL2
  rw [inner_smoothCompact_toL2, inner_smoothCompact_toL2]
  simp only [Real.inner_apply]
  exact integral_oneFormExteriorDerivative_mul_eq_inner_twoFormCodifferential alpha f

theorem hyperbolicDZero_isFormalAdjoint_deltaOne :
    hyperbolicDZero.IsFormalAdjoint hyperbolicDeltaOne := by
  intro x y
  rcases x.property with ⟨f, hf⟩
  rcases y.property with ⟨alpha, halpha⟩
  let xCore : hyperbolicDZero.domain :=
    ⟨hyperbolicSmoothCompactToL2 f, ⟨f, rfl⟩⟩
  let yCore : hyperbolicDeltaOne.domain :=
    ⟨hyperbolicSmoothCompactToL2 alpha, ⟨alpha, rfl⟩⟩
  have hx : x = xCore := by
    apply Subtype.ext
    exact hf.symm
  have hy : y = yCore := by
    apply Subtype.ext
    exact halpha.symm
  rw [hx, hy]
  simpa only [xCore, yCore, hyperbolicDZero, hyperbolicDeltaOne,
    linearPMapOfInjectiveCore_apply, Subtype.coe_mk] using
    hyperbolicDZero_deltaOne_core_pairing f alpha

theorem hyperbolicDOne_isFormalAdjoint_deltaTwo :
    hyperbolicDOne.IsFormalAdjoint hyperbolicDeltaTwo := by
  intro x y
  rcases x.property with ⟨alpha, halpha⟩
  rcases y.property with ⟨f, hf⟩
  let xCore : hyperbolicDOne.domain :=
    ⟨hyperbolicSmoothCompactToL2 alpha, ⟨alpha, rfl⟩⟩
  let yCore : hyperbolicDeltaTwo.domain :=
    ⟨hyperbolicSmoothCompactToL2 f, ⟨f, rfl⟩⟩
  have hx : x = xCore := by
    apply Subtype.ext
    exact halpha.symm
  have hy : y = yCore := by
    apply Subtype.ext
    exact hf.symm
  rw [hx, hy]
  simpa only [xCore, yCore, hyperbolicDOne, hyperbolicDeltaTwo,
    linearPMapOfInjectiveCore_apply, Subtype.coe_mk] using
    hyperbolicDOne_deltaTwo_core_pairing alpha f

noncomputable def oneFormHodgeAdjointCore :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicSmoothCompactOneForm :=
  twoFormCodifferentialCore.comp (oneFormComponentCore 0) +
    scalarExteriorDerivativeCore.comp (oneFormComponentCore 1)

noncomputable def hyperbolicHodgeOneAdjointCoreL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2 :=
  (hyperbolicSmoothCompactToL2 :
    HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2).comp
      oneFormHodgeAdjointCore

noncomputable def hyperbolicHodgeOneAdjoint :
    HyperbolicOneFormL2 →ₗ.[ℝ] HyperbolicOneFormL2 :=
  linearPMapOfInjectiveCore
    (hyperbolicSmoothCompactToL2 :
      HyperbolicSmoothCompactOneForm →ₗ[ℝ] HyperbolicOneFormL2)
    hyperbolicSmoothCompactToL2_injective hyperbolicHodgeOneAdjointCoreL2

theorem hyperbolicHodgeOne_core_pairing
    (alpha beta : HyperbolicSmoothCompactOneForm) :
    inner ℝ (hyperbolicHodgeOneCoreL2 alpha)
        (hyperbolicSmoothCompactToL2 beta) =
      inner ℝ (hyperbolicSmoothCompactToL2 alpha)
        (hyperbolicHodgeOneAdjointCoreL2 beta) := by
  let c := oneFormComponentCore 0 beta
  let f := oneFormComponentCore 1 beta
  have hdelta :
      (∫ p, oneFormCodifferentialCore alpha p * f p
        ∂hyperbolicVolume) =
        ∫ p, inner ℝ (alpha p) (scalarExteriorDerivativeCore f p)
          ∂hyperbolicVolume := by
    calc
      (∫ p, oneFormCodifferentialCore alpha p * f p
          ∂hyperbolicVolume) =
          ∫ p, f p * oneFormCodifferentialCore alpha p
            ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = ∫ p, inner ℝ (scalarExteriorDerivativeCore f p) (alpha p)
          ∂hyperbolicVolume := (integral_scalarExteriorDerivative_inner_eq_mul_codifferential f alpha).symm
      _ = ∫ p, inner ℝ (alpha p) (scalarExteriorDerivativeCore f p)
          ∂hyperbolicVolume := by
        apply integral_congr_ae
        filter_upwards with p
        exact real_inner_comm _ _
  change inner ℝ (oneFormHodgeDerivativeCore alpha).toL2 beta.toL2 =
    inner ℝ alpha.toL2 (oneFormHodgeAdjointCore beta).toL2
  rw [inner_smoothCompact_toL2, inner_smoothCompact_toL2]
  calc
    (∫ p, inner ℝ (oneFormHodgeDerivativeCore alpha p) (beta p)
        ∂hyperbolicVolume) =
        ∫ p, oneFormExteriorDerivativeCore alpha p * c p +
          oneFormCodifferentialCore alpha p * f p
          ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      rw [PiLp.inner_apply, Fin.sum_univ_two,
        oneFormHodgeDerivativeCore_apply_zero,
        oneFormHodgeDerivativeCore_apply_one]
      simp only [Real.inner_apply, c, f, oneFormComponentCore_apply]
    _ = (∫ p, oneFormExteriorDerivativeCore alpha p * c p
          ∂hyperbolicVolume) +
        ∫ p, oneFormCodifferentialCore alpha p * f p
          ∂hyperbolicVolume := by
      rw [integral_add]
      · exact integrable_smoothCompact_product (oneFormExteriorDerivativeCore alpha) c
      · exact integrable_smoothCompact_product (oneFormCodifferentialCore alpha) f
    _ = (∫ p, inner ℝ (alpha p) (twoFormCodifferentialCore c p)
          ∂hyperbolicVolume) +
        ∫ p, inner ℝ (alpha p) (scalarExteriorDerivativeCore f p)
          ∂hyperbolicVolume := by
      rw [integral_oneFormExteriorDerivative_mul_eq_inner_twoFormCodifferential alpha c, hdelta]
    _ = ∫ p, inner ℝ (alpha p) (twoFormCodifferentialCore c p) +
        inner ℝ (alpha p) (scalarExteriorDerivativeCore f p)
          ∂hyperbolicVolume := by
      exact (integral_add
        (integrable_smoothCompact_inner alpha (twoFormCodifferentialCore c))
        (integrable_smoothCompact_inner alpha (scalarExteriorDerivativeCore f))).symm
    _ = ∫ p, inner ℝ (alpha p) (oneFormHodgeAdjointCore beta p)
          ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      change inner ℝ (alpha p) (twoFormCodifferentialCore c p) +
          inner ℝ (alpha p) (scalarExteriorDerivativeCore f p) =
        inner ℝ (alpha p)
          (twoFormCodifferentialCore c p + scalarExteriorDerivativeCore f p)
      rw [inner_add_right]

theorem hyperbolicHodgeOne_isFormalAdjoint :
    hyperbolicHodgeOne.IsFormalAdjoint hyperbolicHodgeOneAdjoint := by
  intro x y
  rcases x.property with ⟨alpha, halpha⟩
  rcases y.property with ⟨beta, hbeta⟩
  let xCore : hyperbolicHodgeOne.domain :=
    ⟨hyperbolicSmoothCompactToL2 alpha, ⟨alpha, rfl⟩⟩
  let yCore : hyperbolicHodgeOneAdjoint.domain :=
    ⟨hyperbolicSmoothCompactToL2 beta, ⟨beta, rfl⟩⟩
  have hx : x = xCore := by
    apply Subtype.ext
    exact halpha.symm
  have hy : y = yCore := by
    apply Subtype.ext
    exact hbeta.symm
  rw [hx, hy]
  simpa only [xCore, yCore, hyperbolicHodgeOne,
    hyperbolicHodgeOneAdjoint, linearPMapOfInjectiveCore_apply,
    Subtype.coe_mk] using hyperbolicHodgeOne_core_pairing alpha beta

theorem hyperbolicHodgeOneAdjoint_dense_domain :
    Dense (hyperbolicHodgeOneAdjoint.domain : Set HyperbolicOneFormL2) :=
  linearPMapOfInjectiveCore_dense_domain _ _ _
    hyperbolicSmoothCompactOneForm_dense

theorem hyperbolicDZero_isClosable : hyperbolicDZero.IsClosable :=
  isClosable_of_formalAdjoint hyperbolicDZero_isFormalAdjoint_deltaOne
    hyperbolicDeltaOne_dense_domain

theorem hyperbolicDeltaOne_isClosable : hyperbolicDeltaOne.IsClosable :=
  isClosable_of_formalAdjoint hyperbolicDZero_isFormalAdjoint_deltaOne.symm
    hyperbolicDZero_dense_domain

theorem hyperbolicDOne_isClosable : hyperbolicDOne.IsClosable :=
  isClosable_of_formalAdjoint hyperbolicDOne_isFormalAdjoint_deltaTwo
    hyperbolicDeltaTwo_dense_domain

theorem hyperbolicDeltaTwo_isClosable : hyperbolicDeltaTwo.IsClosable :=
  isClosable_of_formalAdjoint hyperbolicDOne_isFormalAdjoint_deltaTwo.symm
    hyperbolicDOne_dense_domain

theorem hyperbolicHodgeOne_isClosable : hyperbolicHodgeOne.IsClosable :=
  isClosable_of_formalAdjoint hyperbolicHodgeOne_isFormalAdjoint
    hyperbolicHodgeOneAdjoint_dense_domain

/-- The minimal closed scalar exterior derivative on the complete hyperbolic plane. -/
noncomputable def hyperbolicDZeroClosed :
    DenselyDefinedClosedLinearOperator ℝ HyperbolicScalarL2
      HyperbolicOneFormL2 :=
  DenselyDefinedClosedLinearOperator.ofClosable hyperbolicDZero
    hyperbolicDZero_isClosable hyperbolicDZero_dense_domain

/-- The minimal closed exterior derivative from one-forms to top forms. -/
noncomputable def hyperbolicDOneClosed :
    DenselyDefinedClosedLinearOperator ℝ HyperbolicOneFormL2
      HyperbolicScalarL2 :=
  DenselyDefinedClosedLinearOperator.ofClosable hyperbolicDOne
    hyperbolicDOne_isClosable hyperbolicDOne_dense_domain

/-- The minimal closed codifferential from one-forms to scalars. -/
noncomputable def hyperbolicDeltaOneClosed :
    DenselyDefinedClosedLinearOperator ℝ HyperbolicOneFormL2
      HyperbolicScalarL2 :=
  DenselyDefinedClosedLinearOperator.ofClosable hyperbolicDeltaOne
    hyperbolicDeltaOne_isClosable hyperbolicDeltaOne_dense_domain

/-- The minimal closed codifferential from top forms to one-forms. -/
noncomputable def hyperbolicDeltaTwoClosed :
    DenselyDefinedClosedLinearOperator ℝ HyperbolicScalarL2
      HyperbolicOneFormL2 :=
  DenselyDefinedClosedLinearOperator.ofClosable hyperbolicDeltaTwo
    hyperbolicDeltaTwo_isClosable hyperbolicDeltaTwo_dense_domain

/-- The minimal closed Hodge derivative `alpha ↦ (d alpha, delta alpha)`. -/
noncomputable def hyperbolicHodgeOneClosed :
    DenselyDefinedClosedLinearOperator ℝ HyperbolicOneFormL2
      HyperbolicOneFormL2 :=
  DenselyDefinedClosedLinearOperator.ofClosable hyperbolicHodgeOne
    hyperbolicHodgeOne_isClosable hyperbolicHodgeOne_dense_domain

/-- The complete graph Hilbert space of the closed Hodge derivative.  Its norm is
`‖alpha‖₂² + ‖d alpha‖₂² + ‖delta alpha‖₂²`.  The source-normalized covariant `H¹` carrier is
identified from this space by the hyperbolic Bochner--Weitzenbock identity below. -/
abbrev HyperbolicHodgeGraphH1 :=
  hyperbolicHodgeOneClosed.toClosedLinearOperator.GraphSpace

/-- The Hodge graph carrier has the actual `CompleteSpace` instance inherited from its closed
graph in the Hilbert product. -/
noncomputable instance hyperbolicHodgeGraphH1Complete :
    CompleteSpace HyperbolicHodgeGraphH1 := inferInstance

/-- Continuous inclusion of the Hodge graph carrier into one-form `L²`. -/
noncomputable def hyperbolicHodgeGraphH1ToL2 :
    HyperbolicHodgeGraphH1 →L[ℝ] HyperbolicOneFormL2 :=
  hyperbolicHodgeOneClosed.toClosedLinearOperator.base

/-- Continuous Hodge derivative on its complete graph carrier. -/
noncomputable def hyperbolicHodgeGraphDerivative :
    HyperbolicHodgeGraphH1 →L[ℝ] HyperbolicOneFormL2 :=
  hyperbolicHodgeOneClosed.toClosedLinearOperator.value

end RiemannianFluids.HyperbolicPlane
