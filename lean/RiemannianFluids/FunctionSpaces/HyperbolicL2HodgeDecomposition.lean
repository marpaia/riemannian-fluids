import RiemannianFluids.FunctionSpaces.HyperbolicHodgeDecomposition

/-!
# The genuine `L²` Hodge decomposition and Leray projector on `H²`

This module applies Hilbert-space orthogonal-complement theory to the concrete scalar and
one-form `L²` quotients.  The harmonic sector is characterized by the actual distributional
equations `d alpha = 0` and `delta alpha = 0`, tested against the compact smooth cores.  The
orthogonal complement of exact forms is therefore the concrete divergence-free carrier, and its
orthogonal projection is the Leray projector.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Set
open scoped RealInnerProductSpace

/-- Compact exact one-forms in the concrete one-form `L²` quotient. -/
noncomputable def hyperbolicExactCoreL2 : Submodule ℝ HyperbolicOneFormL2 :=
  LinearMap.range hyperbolicDZeroCoreL2

/-- Compact coexact one-forms in the concrete one-form `L²` quotient. -/
noncomputable def hyperbolicCoexactCoreL2 : Submodule ℝ HyperbolicOneFormL2 :=
  LinearMap.range hyperbolicDeltaTwoCoreL2

/-- Closed `L²` exact sector. -/
noncomputable def hyperbolicExactL2 : Submodule ℝ HyperbolicOneFormL2 :=
  hyperbolicExactCoreL2.topologicalClosure

/-- Closed `L²` coexact sector. -/
noncomputable def hyperbolicCoexactL2 : Submodule ℝ HyperbolicOneFormL2 :=
  hyperbolicCoexactCoreL2.topologicalClosure

theorem isClosed_hyperbolicExactL2 :
    IsClosed (hyperbolicExactL2 : Set HyperbolicOneFormL2) := by
  simpa only [hyperbolicExactL2] using
    Submodule.isClosed_topologicalClosure hyperbolicExactCoreL2

theorem isClosed_hyperbolicCoexactL2 :
    IsClosed (hyperbolicCoexactL2 : Set HyperbolicOneFormL2) := by
  simpa only [hyperbolicCoexactL2] using
    Submodule.isClosed_topologicalClosure hyperbolicCoexactCoreL2

noncomputable instance hyperbolicExactL2Complete : CompleteSpace hyperbolicExactL2 :=
  isClosed_hyperbolicExactL2.completeSpace_coe

noncomputable instance hyperbolicCoexactL2Complete : CompleteSpace hyperbolicCoexactL2 :=
  isClosed_hyperbolicCoexactL2.completeSpace_coe

theorem hyperbolicExactCoreL2_isOrtho_hyperbolicCoexactCoreL2 :
    hyperbolicExactCoreL2 ⟂ hyperbolicCoexactCoreL2 := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro alpha halpha beta hbeta
  rcases halpha with ⟨f, rfl⟩
  rcases hbeta with ⟨g, rfl⟩
  exact inner_hyperbolicDZeroCoreL2_hyperbolicDeltaTwoCoreL2 f g

theorem hyperbolicExactL2_isOrtho_hyperbolicCoexactL2 :
    hyperbolicExactL2 ⟂ hyperbolicCoexactL2 := by
  change hyperbolicExactCoreL2.topologicalClosure ≤
    hyperbolicCoexactCoreL2.topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact hyperbolicExactCoreL2.topologicalClosure_minimal
    hyperbolicExactCoreL2_isOrtho_hyperbolicCoexactCoreL2
    hyperbolicCoexactCoreL2.isClosed_orthogonal

/-- Distributional coclosedness, tested against every compact smooth scalar. -/
def IsDistributionallyCoclosed (u : HyperbolicOneFormL2) : Prop :=
  ∀ f : HyperbolicSmoothCompactScalar,
    inner ℝ (hyperbolicDZeroCoreL2 f) u = 0

/-- Distributional closedness, tested against compact smooth top forms through `delta₂`. -/
def IsDistributionallyClosed (u : HyperbolicOneFormL2) : Prop :=
  ∀ f : HyperbolicSmoothCompactScalar,
    inner ℝ (hyperbolicDeltaTwoCoreL2 f) u = 0

/-- The actual `L²` harmonic sector: distributionally closed and coclosed one-forms. -/
noncomputable def hyperbolicHarmonicL2 : Submodule ℝ HyperbolicOneFormL2 :=
  hyperbolicExactL2ᗮ ⊓ hyperbolicCoexactL2ᗮ

theorem mem_hyperbolicExactL2_orthogonal_iff (u : HyperbolicOneFormL2) :
    u ∈ hyperbolicExactL2ᗮ ↔ IsDistributionallyCoclosed u := by
  rw [hyperbolicExactL2, Submodule.orthogonal_closure]
  constructor
  · intro hu f
    exact hu (hyperbolicDZeroCoreL2 f) ⟨f, rfl⟩
  · intro hu v hv
    rcases hv with ⟨f, rfl⟩
    exact hu f

theorem mem_hyperbolicCoexactL2_orthogonal_iff (u : HyperbolicOneFormL2) :
    u ∈ hyperbolicCoexactL2ᗮ ↔ IsDistributionallyClosed u := by
  rw [hyperbolicCoexactL2, Submodule.orthogonal_closure]
  constructor
  · intro hu f
    exact hu (hyperbolicDeltaTwoCoreL2 f) ⟨f, rfl⟩
  · intro hu v hv
    rcases hv with ⟨f, rfl⟩
    exact hu f

theorem mem_hyperbolicHarmonicL2_iff (u : HyperbolicOneFormL2) :
    u ∈ hyperbolicHarmonicL2 ↔
      IsDistributionallyClosed u ∧ IsDistributionallyCoclosed u := by
  rw [hyperbolicHarmonicL2, Submodule.mem_inf,
    mem_hyperbolicExactL2_orthogonal_iff,
    mem_hyperbolicCoexactL2_orthogonal_iff, and_comm]

theorem isClosed_hyperbolicHarmonicL2 :
    IsClosed (hyperbolicHarmonicL2 : Set HyperbolicOneFormL2) := by
  exact hyperbolicExactL2.isClosed_orthogonal.inter
    hyperbolicCoexactL2.isClosed_orthogonal

noncomputable instance hyperbolicHarmonicL2Complete :
    CompleteSpace hyperbolicHarmonicL2 :=
  isClosed_hyperbolicHarmonicL2.completeSpace_coe

/-! ## Weak derivatives of source `H¹` representatives -/

/-- Distributional closedness of an `H¹` representative is equivalent to vanishing of its
continuous weak exterior derivative. -/
theorem isDistributionallyClosed_hyperbolicOneFormH1ToL2_iff
    (u : HyperbolicOneFormH1) :
    IsDistributionallyClosed (hyperbolicOneFormH1ToL2 u) ↔
      hyperbolicOneFormH1DOne u = 0 := by
  constructor
  · intro hu
    apply hyperbolicScalarL2_eq_zero_of_inner_smoothCompact
    intro f
    rw [real_inner_comm, hyperbolicOneFormH1DOne_deltaTwo_pairing]
    have htest := hu f
    rw [real_inner_comm] at htest
    exact htest
  · intro hdu f
    rw [real_inner_comm,
      ← hyperbolicOneFormH1DOne_deltaTwo_pairing, hdu,
      inner_zero_left]

/-- Distributional coclosedness of an `H¹` representative is equivalent to vanishing of its
continuous weak codifferential. -/
theorem isDistributionallyCoclosed_hyperbolicOneFormH1ToL2_iff
    (u : HyperbolicOneFormH1) :
    IsDistributionallyCoclosed (hyperbolicOneFormH1ToL2 u) ↔
      hyperbolicOneFormH1DeltaOne u = 0 := by
  constructor
  · intro hu
    apply hyperbolicScalarL2_eq_zero_of_inner_smoothCompact
    intro f
    rw [← hyperbolicDZero_H1DeltaOne_pairing]
    exact hu f
  · intro hdelta f
    rw [hyperbolicDZero_H1DeltaOne_pairing, hdelta, inner_zero_right]

/-- The concrete `L²` representative of a source `H¹` element is harmonic exactly when its
packed weak Hodge derivative vanishes. -/
theorem hyperbolicOneFormH1ToL2_mem_harmonic_iff
    (u : HyperbolicOneFormH1) :
    hyperbolicOneFormH1ToL2 u ∈ hyperbolicHarmonicL2 ↔
      hyperbolicOneFormH1Hodge u = 0 := by
  rw [mem_hyperbolicHarmonicL2_iff,
    isDistributionallyClosed_hyperbolicOneFormH1ToL2_iff,
    isDistributionallyCoclosed_hyperbolicOneFormH1ToL2_iff,
    hyperbolicOneFormH1Hodge_eq_zero_iff]

/-- The completed source space embeds faithfully into one-form `L²`; its weak derivatives are
uniquely determined distributionally by the `L²` representative. -/
theorem hyperbolicOneFormH1ToL2_injective :
    Function.Injective hyperbolicOneFormH1ToL2 := by
  intro u v huv
  have hclosed : IsDistributionallyClosed
      (hyperbolicOneFormH1ToL2 (u - v)) := by
    rw [map_sub, huv, sub_self]
    intro f
    simp
  have hcoclosed : IsDistributionallyCoclosed
      (hyperbolicOneFormH1ToL2 (u - v)) := by
    rw [map_sub, huv, sub_self]
    intro f
    simp
  have hderivative : hyperbolicOneFormH1Hodge (u - v) = 0 :=
    (hyperbolicOneFormH1Hodge_eq_zero_iff (u - v)).2 ⟨
      (isDistributionallyClosed_hyperbolicOneFormH1ToL2_iff (u - v)).1 hclosed,
      (isDistributionallyCoclosed_hyperbolicOneFormH1ToL2_iff (u - v)).1 hcoclosed⟩
  have hnorm := norm_sq_hyperbolicOneFormH1 (u - v)
  rw [map_sub, huv, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    hderivative, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, add_zero] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))

/-! ## CCP25's shifted elliptic equations -/

/-- In degree zero/top degree on the oriented hyperbolic plane, the two scalar Hodge Laplacian
cores agree: `delta₁ d₀ = d₁ delta₂`. -/
theorem hyperbolicDeltaOne_DZero_eq_DOne_DeltaTwo_core
    (f : HyperbolicSmoothCompactScalar) :
    hyperbolicDeltaOneCoreL2 (scalarExteriorDerivativeCore f) =
      hyperbolicDOneCoreL2 (twoFormCodifferentialCore f) := by
  apply congrArg HyperbolicSmoothCompactSection.toL2
  apply DFunLike.ext _ _
  intro p
  rw [oneFormCodifferentialCore_apply, oneFormExteriorDerivativeCore_apply,
    scalarExteriorDerivativeCore_apply_one,
    twoFormCodifferentialCore_apply_zero]
  have hscalarZero :
      (fun q ↦ scalarExteriorDerivativeCore f q 0) =
        (horizontalDerivativeCore f).toFun := by
    funext q
    exact scalarExteriorDerivativeCore_apply_zero f q
  have hscalarOne :
      (fun q ↦ scalarExteriorDerivativeCore f q 1) =
        (verticalDerivativeCore f).toFun := by
    funext q
    exact scalarExteriorDerivativeCore_apply_one f q
  have htopZero :
      (fun q ↦ twoFormCodifferentialCore f q 0) =
        (verticalDerivativeCore f).toFun := by
    funext q
    exact twoFormCodifferentialCore_apply_zero f q
  have htopOne :
      (fun q ↦ twoFormCodifferentialCore f q 1) =
        (-horizontalDerivativeCore f).toFun := by
    funext q
    change twoFormCodifferentialCore f q 1 =
      -horizontalDerivative f.toFun q
    exact twoFormCodifferentialCore_apply_one f q
  rw [hscalarZero, hscalarOne, htopZero, htopOne]
  have hxneg :
      horizontalDerivative (-horizontalDerivativeCore f).toFun p =
        -horizontalDerivative (horizontalDerivativeCore f).toFun p := by
    change (horizontalDerivativeCoreLinear (-horizontalDerivativeCore f)) p =
      -(horizontalDerivativeCoreLinear (horizontalDerivativeCore f)) p
    rw [map_neg]
    rfl
  rw [hxneg]

/-- The scalar core operator `delta d + 2` occurring in CCP25 Proposition 4.3 after
specializing `N = 2`, `k = 1`, and curvature scale `a = 1`. -/
noncomputable def hyperbolicScalarShiftedHodgeCoreL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2 :=
  hyperbolicDeltaOneCoreL2.comp scalarExteriorDerivativeCore +
    (2 : ℝ) •
      (hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2)

@[simp] theorem hyperbolicScalarShiftedHodgeCoreL2_apply
    (f : HyperbolicSmoothCompactScalar) :
    hyperbolicScalarShiftedHodgeCoreL2 f =
      hyperbolicDeltaOneCoreL2 (scalarExteriorDerivativeCore f) +
        (2 : ℝ) • hyperbolicSmoothCompactToL2 f :=
  by simp [hyperbolicScalarShiftedHodgeCoreL2]

/-- The top-form coefficient core operator `d delta + 2` from the second half of CCP25
Proposition 4.3. -/
noncomputable def hyperbolicTopShiftedHodgeCoreL2 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2 :=
  hyperbolicDOneCoreL2.comp twoFormCodifferentialCore +
    (2 : ℝ) •
      (hyperbolicSmoothCompactToL2 :
        HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicScalarL2)

@[simp] theorem hyperbolicTopShiftedHodgeCoreL2_apply
    (f : HyperbolicSmoothCompactScalar) :
    hyperbolicTopShiftedHodgeCoreL2 f =
      hyperbolicDOneCoreL2 (twoFormCodifferentialCore f) +
        (2 : ℝ) • hyperbolicSmoothCompactToL2 f :=
  by simp [hyperbolicTopShiftedHodgeCoreL2]

/-- The scalar and top-form shifted operators are the same concrete core operator. -/
theorem hyperbolicScalarShiftedHodgeCoreL2_eq_top :
    hyperbolicScalarShiftedHodgeCoreL2 =
      hyperbolicTopShiftedHodgeCoreL2 := by
  ext f
  rw [hyperbolicScalarShiftedHodgeCoreL2_apply,
    hyperbolicTopShiftedHodgeCoreL2_apply,
    hyperbolicDeltaOne_DZero_eq_DOne_DeltaTwo_core]

/-- Orthogonality to the source exact sector produces the precise scalar shifted elliptic
equation in weak form. -/
theorem hyperbolicHarmonicH1_delta_shifted_orthogonal
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicHarmonicH1)
    (f : HyperbolicSmoothCompactScalar) :
    inner ℝ (hyperbolicOneFormH1DeltaOne u)
      (hyperbolicScalarShiftedHodgeCoreL2 f) = 0 := by
  have hexactCore : hyperbolicExactCoreToH1 f ∈ hyperbolicExactCoreH1 :=
    ⟨f, rfl⟩
  have hexact : hyperbolicExactCoreToH1 f ∈ hyperbolicExactH1 :=
    (Submodule.le_topologicalClosure (s := hyperbolicExactCoreH1)) hexactCore
  have hortho : inner ℝ (hyperbolicExactCoreToH1 f) u = 0 :=
    hu.1 _ hexact
  have hdSquared :
      hyperbolicDOneCoreL2 (scalarExteriorDerivativeCore f) = 0 := by
    change (oneFormExteriorDerivativeCore
      (scalarExteriorDerivativeCore f)).toL2 = 0
    rw [oneFormExteriorDerivativeCore_scalarExteriorDerivativeCore]
    rfl
  rw [inner_hyperbolicOneFormH1_expanded] at hortho
  simp only [hyperbolicExactCoreToH1, LinearMap.comp_apply,
    hyperbolicOneFormH1ToL2_core, hyperbolicOneFormH1DOne_core,
    hyperbolicOneFormH1DeltaOne_core] at hortho
  rw [hdSquared, inner_zero_left, add_zero] at hortho
  have hpair := hyperbolicDZero_H1DeltaOne_pairing f u
  change inner ℝ
      (hyperbolicSmoothCompactToL2 (scalarExteriorDerivativeCore f))
      (hyperbolicOneFormH1ToL2 u) =
    inner ℝ (hyperbolicSmoothCompactToL2 f)
      (hyperbolicOneFormH1DeltaOne u) at hpair
  have hpair' :
      inner ℝ (hyperbolicOneFormH1DeltaOne u)
          (hyperbolicSmoothCompactToL2 f) =
        inner ℝ
          (hyperbolicSmoothCompactToL2 (scalarExteriorDerivativeCore f))
          (hyperbolicOneFormH1ToL2 u) := by
    rw [real_inner_comm]
    exact hpair.symm
  rw [hyperbolicScalarShiftedHodgeCoreL2_apply,
    inner_add_right, inner_smul_right, hpair']
  rw [← real_inner_comm
    (hyperbolicOneFormH1DeltaOne u)
    (hyperbolicDeltaOneCoreL2 (scalarExteriorDerivativeCore f))]
  linarith

/-- Orthogonality to the source coexact sector produces the top-form shifted elliptic equation
in weak form. -/
theorem hyperbolicHarmonicH1_d_shifted_orthogonal
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicHarmonicH1)
    (f : HyperbolicSmoothCompactScalar) :
    inner ℝ (hyperbolicOneFormH1DOne u)
      (hyperbolicTopShiftedHodgeCoreL2 f) = 0 := by
  have hcoexactCore : hyperbolicCoexactCoreToH1 f ∈
      hyperbolicCoexactCoreH1 := ⟨f, rfl⟩
  have hcoexact : hyperbolicCoexactCoreToH1 f ∈ hyperbolicCoexactH1 :=
    (Submodule.le_topologicalClosure (s := hyperbolicCoexactCoreH1)) hcoexactCore
  have hortho : inner ℝ (hyperbolicCoexactCoreToH1 f) u = 0 :=
    hu.2 _ hcoexact
  have hdeltaSquared :
      hyperbolicDeltaOneCoreL2 (twoFormCodifferentialCore f) = 0 := by
    change (oneFormCodifferentialCore
      (twoFormCodifferentialCore f)).toL2 = 0
    rw [oneFormCodifferentialCore_twoFormCodifferentialCore]
    rfl
  rw [inner_hyperbolicOneFormH1_expanded] at hortho
  simp only [hyperbolicCoexactCoreToH1, LinearMap.comp_apply,
    hyperbolicOneFormH1ToL2_core, hyperbolicOneFormH1DOne_core,
    hyperbolicOneFormH1DeltaOne_core] at hortho
  rw [hdeltaSquared, inner_zero_left, add_zero] at hortho
  have hpair := hyperbolicOneFormH1DOne_deltaTwo_pairing u f
  change inner ℝ (hyperbolicOneFormH1DOne u)
      (hyperbolicSmoothCompactToL2 f) =
    inner ℝ (hyperbolicOneFormH1ToL2 u)
      (hyperbolicSmoothCompactToL2 (twoFormCodifferentialCore f)) at hpair
  rw [hyperbolicTopShiftedHodgeCoreL2_apply,
    inner_add_right, inner_smul_right]
  rw [hpair]
  rw [← real_inner_comm
    (hyperbolicOneFormH1DOne u)
    (hyperbolicDOneCoreL2 (twoFormCodifferentialCore f))]
  rw [← real_inner_comm
    (hyperbolicOneFormH1ToL2 u)
    (hyperbolicSmoothCompactToL2 (twoFormCodifferentialCore f))]
  linarith

/-- CCP25 Proposition 4.3 reduced to its single completeness/coercivity input: density of the
two positive shifted core operators. -/
theorem hyperbolicHarmonicH1_toL2_mem_harmonic_of_shifted_denseRange
    (hscalar : DenseRange hyperbolicScalarShiftedHodgeCoreL2)
    (htop : DenseRange hyperbolicTopShiftedHodgeCoreL2)
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicHarmonicH1) :
    hyperbolicOneFormH1ToL2 u ∈ hyperbolicHarmonicL2 := by
  have hdeltaFun :
      (fun v : HyperbolicScalarL2 ↦
          inner ℝ (hyperbolicOneFormH1DeltaOne u) v) =
        fun _ : HyperbolicScalarL2 ↦ (0 : ℝ) :=
    hscalar.equalizer
      (continuous_const.inner continuous_id) continuous_const (by
        funext f
        exact hyperbolicHarmonicH1_delta_shifted_orthogonal u hu f)
  have hdelta : hyperbolicOneFormH1DeltaOne u = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact congrFun hdeltaFun (hyperbolicOneFormH1DeltaOne u)
  have hdFun :
      (fun v : HyperbolicScalarL2 ↦
          inner ℝ (hyperbolicOneFormH1DOne u) v) =
        fun _ : HyperbolicScalarL2 ↦ (0 : ℝ) :=
    htop.equalizer
      (continuous_const.inner continuous_id) continuous_const (by
        funext f
        exact hyperbolicHarmonicH1_d_shifted_orthogonal u hu f)
  have hd : hyperbolicOneFormH1DOne u = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact congrFun hdFun (hyperbolicOneFormH1DOne u)
  exact (hyperbolicOneFormH1ToL2_mem_harmonic_iff u).2
    ((hyperbolicOneFormH1Hodge_eq_zero_iff u).2 ⟨hd, hdelta⟩)

/-- Single-input form of CCP25 Proposition 4.3: on `H²`, scalar and top-degree shifted
operators coincide, so one dense-range theorem discharges both elliptic equations. -/
theorem hyperbolicHarmonicH1_toL2_mem_harmonic_of_shifted_denseRange'
    (hshifted : DenseRange hyperbolicScalarShiftedHodgeCoreL2)
    (u : HyperbolicOneFormH1) (hu : u ∈ hyperbolicHarmonicH1) :
    hyperbolicOneFormH1ToL2 u ∈ hyperbolicHarmonicL2 := by
  apply hyperbolicHarmonicH1_toL2_mem_harmonic_of_shifted_denseRange
    hshifted
  rw [← hyperbolicScalarShiftedHodgeCoreL2_eq_top]
  exact hshifted
  exact hu

/-- The easy inclusion in CCP25 Lemma 4.2, now stated without assuming a separate harmonic
regularity theorem: any source `H¹` representative whose `L²` value is harmonic lies in the
source harmonic orthogonal remainder. -/
theorem hyperbolicHarmonicL2_preimage_mem_harmonicH1
    (u : HyperbolicOneFormH1)
    (hu : hyperbolicOneFormH1ToL2 u ∈ hyperbolicHarmonicL2) :
    u ∈ hyperbolicHarmonicH1 := by
  have hdistribution := (mem_hyperbolicHarmonicL2_iff _).1 hu
  have hhodge := (hyperbolicOneFormH1ToL2_mem_harmonic_iff u).1 hu
  rw [mem_hyperbolicHarmonicH1_iff]
  constructor
  · rw [hyperbolicExactH1, Submodule.orthogonal_closure]
    intro v hv
    rcases hv with ⟨f, rfl⟩
    rw [inner_hyperbolicOneFormH1, hhodge, inner_zero_right, add_zero]
    have htest := hdistribution.2 f
    change inner ℝ
      (hyperbolicSmoothCompactToL2 (scalarExteriorDerivativeCore f))
      (hyperbolicOneFormH1ToL2 u) = 0 at htest
    change 2 * inner ℝ
      (hyperbolicSmoothCompactToL2 (scalarExteriorDerivativeCore f))
      (hyperbolicOneFormH1ToL2 u) = 0
    rw [htest, mul_zero]
  · rw [hyperbolicCoexactH1, Submodule.orthogonal_closure]
    intro v hv
    rcases hv with ⟨f, rfl⟩
    rw [inner_hyperbolicOneFormH1, hhodge, inner_zero_right, add_zero]
    have htest := hdistribution.1 f
    change inner ℝ
      (hyperbolicSmoothCompactToL2 (twoFormCodifferentialCore f))
      (hyperbolicOneFormH1ToL2 u) = 0 at htest
    change 2 * inner ℝ
      (hyperbolicSmoothCompactToL2 (twoFormCodifferentialCore f))
      (hyperbolicOneFormH1ToL2 u) = 0
    rw [htest, mul_zero]

/-! ## Orthogonal projectors and the `L²` direct sum -/

noncomputable def hyperbolicExactL2Projector :
    HyperbolicOneFormL2 →L[ℝ] HyperbolicOneFormL2 :=
  hyperbolicExactL2.starProjection

noncomputable def hyperbolicExactL2Remainder :
    HyperbolicOneFormL2 →L[ℝ] HyperbolicOneFormL2 :=
  ContinuousLinearMap.id ℝ HyperbolicOneFormL2 - hyperbolicExactL2Projector

noncomputable def hyperbolicCoexactL2Projector :
    HyperbolicOneFormL2 →L[ℝ] HyperbolicOneFormL2 :=
  hyperbolicCoexactL2.starProjection.comp hyperbolicExactL2Remainder

noncomputable def hyperbolicHarmonicL2Projector :
    HyperbolicOneFormL2 →L[ℝ] HyperbolicOneFormL2 :=
  ContinuousLinearMap.id ℝ HyperbolicOneFormL2 -
    hyperbolicExactL2Projector - hyperbolicCoexactL2Projector

theorem hyperbolicExactL2Projector_mem (u : HyperbolicOneFormL2) :
    hyperbolicExactL2Projector u ∈ hyperbolicExactL2 :=
  hyperbolicExactL2.starProjection_apply_mem u

theorem hyperbolicExactL2Remainder_mem_orthogonal (u : HyperbolicOneFormL2) :
    hyperbolicExactL2Remainder u ∈ hyperbolicExactL2ᗮ := by
  change u - hyperbolicExactL2.starProjection u ∈ hyperbolicExactL2ᗮ
  exact hyperbolicExactL2.sub_starProjection_mem_orthogonal u

theorem hyperbolicCoexactL2Projector_mem (u : HyperbolicOneFormL2) :
    hyperbolicCoexactL2Projector u ∈ hyperbolicCoexactL2 :=
  hyperbolicCoexactL2.starProjection_apply_mem _

theorem hyperbolicHarmonicL2Projector_mem (u : HyperbolicOneFormL2) :
    hyperbolicHarmonicL2Projector u ∈ hyperbolicHarmonicL2 := by
  change hyperbolicExactL2Remainder u - hyperbolicCoexactL2Projector u ∈
    hyperbolicExactL2ᗮ ⊓ hyperbolicCoexactL2ᗮ
  constructor
  · exact hyperbolicExactL2ᗮ.sub_mem
      (hyperbolicExactL2Remainder_mem_orthogonal u)
      (hyperbolicExactL2_isOrtho_hyperbolicCoexactL2.ge
        (hyperbolicCoexactL2Projector_mem u))
  · change hyperbolicExactL2Remainder u -
      hyperbolicCoexactL2.starProjection (hyperbolicExactL2Remainder u) ∈
        hyperbolicCoexactL2ᗮ
    exact hyperbolicCoexactL2.sub_starProjection_mem_orthogonal _

/-- Genuine `L²` Hodge decomposition on the complete hyperbolic plane. -/
theorem hyperbolicL2_exact_add_coexact_add_harmonic (u : HyperbolicOneFormL2) :
    u = hyperbolicExactL2Projector u + hyperbolicCoexactL2Projector u +
      hyperbolicHarmonicL2Projector u := by
  simp only [hyperbolicHarmonicL2Projector, sub_apply,
    ContinuousLinearMap.id_apply]
  abel

/-! ## Leray projection -/

/-- The concrete divergence-free `L²` carrier. -/
noncomputable def HyperbolicDivergenceFreeL2 : Submodule ℝ HyperbolicOneFormL2 :=
  hyperbolicExactL2ᗮ

noncomputable instance hyperbolicDivergenceFreeL2HasOrthogonalProjection :
    HyperbolicDivergenceFreeL2.HasOrthogonalProjection := by
  rw [HyperbolicDivergenceFreeL2]
  infer_instance

/-- The genuine `L²` Leray projector onto distributionally coclosed one-forms. -/
noncomputable def hyperbolicLerayProjector :
    HyperbolicOneFormL2 →L[ℝ] HyperbolicOneFormL2 :=
  HyperbolicDivergenceFreeL2.starProjection

theorem hyperbolicLerayProjector_mem (u : HyperbolicOneFormL2) :
    hyperbolicLerayProjector u ∈ HyperbolicDivergenceFreeL2 :=
  HyperbolicDivergenceFreeL2.starProjection_apply_mem u

theorem hyperbolicLerayProjector_isDistributionallyCoclosed
    (u : HyperbolicOneFormL2) :
    IsDistributionallyCoclosed (hyperbolicLerayProjector u) :=
  (mem_hyperbolicExactL2_orthogonal_iff _).mp
    (hyperbolicLerayProjector_mem u)

theorem hyperbolicLerayProjector_eq_self_iff (u : HyperbolicOneFormL2) :
    hyperbolicLerayProjector u = u ↔ IsDistributionallyCoclosed u := by
  rw [hyperbolicLerayProjector,
    Submodule.starProjection_eq_self_iff,
    HyperbolicDivergenceFreeL2,
    mem_hyperbolicExactL2_orthogonal_iff]

theorem hyperbolicLerayProjector_idempotent :
    IsIdempotentElem hyperbolicLerayProjector :=
  HyperbolicDivergenceFreeL2.isIdempotentElem_starProjection

theorem norm_hyperbolicLerayProjector_le (u : HyperbolicOneFormL2) :
    ‖hyperbolicLerayProjector u‖ ≤ ‖u‖ :=
  HyperbolicDivergenceFreeL2.norm_starProjection_apply_le u

theorem hyperbolicLerayProjector_eq_coexact_add_harmonic
    (u : HyperbolicOneFormL2) :
    hyperbolicLerayProjector u =
      hyperbolicCoexactL2Projector u + hyperbolicHarmonicL2Projector u := by
  have horth := hyperbolicExactL2.starProjection_orthogonal_val u
  rw [hyperbolicLerayProjector]
  change hyperbolicExactL2ᗮ.starProjection u = _
  rw [horth]
  have hsum := hyperbolicL2_exact_add_coexact_add_harmonic u
  change u - hyperbolicExactL2Projector u = _
  nth_rw 1 [hsum]
  abel

end RiemannianFluids.HyperbolicPlane
