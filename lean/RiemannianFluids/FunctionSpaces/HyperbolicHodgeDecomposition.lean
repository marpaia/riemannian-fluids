import RiemannianFluids.FunctionSpaces.HyperbolicH1
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Exact, coexact, and harmonic `H¹` sectors on the hyperbolic plane

The exact and coexact sectors are the source-prescribed `H¹` closures of `d C_c^∞` and
`delta C_c^∞`.  Their orthogonality is proved from the concrete de Rham complex, formal-adjoint
relations, and the hyperbolic Bochner--Weitzenbock identity.  Orthogonal projections then give a
canonical three-term decomposition of every one-form in the complete `H¹` carrier.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! ## Core orthogonality -/

theorem inner_hyperbolicDZeroCoreL2_hyperbolicDeltaTwoCoreL2
    (f g : HyperbolicSmoothCompactScalar) :
    inner ℝ (hyperbolicDZeroCoreL2 f) (hyperbolicDeltaTwoCoreL2 g) = 0 := by
  have hpair := hyperbolicDZero_deltaOne_core_pairing f
    (twoFormCodifferentialCore g)
  have hdelta : hyperbolicDeltaOneCoreL2 (twoFormCodifferentialCore g) = 0 := by
    change (oneFormCodifferentialCore (twoFormCodifferentialCore g)).toL2 = 0
    rw [oneFormCodifferentialCore_twoFormCodifferentialCore]
    rfl
  rw [hdelta, inner_zero_right] at hpair
  exact hpair

theorem inner_hyperbolicHodge_exact_coexact_core
    (f g : HyperbolicSmoothCompactScalar) :
    inner ℝ
        (hyperbolicHodgeOneCoreL2 (scalarExteriorDerivativeCore f))
        (hyperbolicHodgeOneCoreL2 (twoFormCodifferentialCore g)) = 0 := by
  change inner ℝ
      (oneFormHodgeDerivativeCore (scalarExteriorDerivativeCore f)).toL2
      (oneFormHodgeDerivativeCore (twoFormCodifferentialCore g)).toL2 = 0
  rw [inner_smoothCompact_toL2]
  calc
    (∫ p, inner ℝ
        (oneFormHodgeDerivativeCore (scalarExteriorDerivativeCore f) p)
        (oneFormHodgeDerivativeCore (twoFormCodifferentialCore g) p)
        ∂hyperbolicVolume) = ∫ _p, (0 : ℝ) ∂hyperbolicVolume := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [PiLp.inner_apply, Fin.sum_univ_two,
        oneFormHodgeDerivativeCore_apply_zero,
        oneFormHodgeDerivativeCore_apply_one, Real.inner_apply]
      have hd : oneFormExteriorDerivativeCore (scalarExteriorDerivativeCore f) p = 0 := by
        rw [oneFormExteriorDerivativeCore_scalarExteriorDerivativeCore]
        rfl
      have hdelta : oneFormCodifferentialCore (twoFormCodifferentialCore g) p = 0 := by
        rw [oneFormCodifferentialCore_twoFormCodifferentialCore]
        rfl
      rw [hd, hdelta]
      simp
    _ = 0 := by simp

/-- Exact and coexact compact-core one-forms are orthogonal in CCP25's source `H¹` inner
product, not merely in `L²`. -/
theorem inner_hyperbolicExactCoexact_core
    (f g : HyperbolicSmoothCompactScalar) :
    inner ℝ
        (hyperbolicSmoothCompactOneFormToH1 (scalarExteriorDerivativeCore f))
        (hyperbolicSmoothCompactOneFormToH1 (twoFormCodifferentialCore g)) = 0 := by
  have hl2 : inner ℝ
      (hyperbolicSmoothCompactToL2 (scalarExteriorDerivativeCore f))
      (hyperbolicSmoothCompactToL2 (twoFormCodifferentialCore g)) = 0 := by
    change inner ℝ (hyperbolicDZeroCoreL2 f) (hyperbolicDeltaTwoCoreL2 g) = 0
    exact inner_hyperbolicDZeroCoreL2_hyperbolicDeltaTwoCoreL2 f g
  have hhodge : inner ℝ
      (hyperbolicHodgeOneCoreL2 (scalarExteriorDerivativeCore f))
      (hyperbolicHodgeOneCoreL2 (twoFormCodifferentialCore g)) = 0 :=
    inner_hyperbolicHodge_exact_coexact_core f g
  rw [inner_hyperbolicSmoothCompactOneFormToH1,
    inner_hyperbolicNablaOneCoreL2, hl2, hhodge]
  simp

/-! ## Closed source sectors -/

/-- Compact exact one-forms included into source-normalized `H¹`. -/
noncomputable def hyperbolicExactCoreToH1 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicOneFormH1 :=
  hyperbolicSmoothCompactOneFormToH1.comp scalarExteriorDerivativeCore

/-- Compact coexact one-forms included into source-normalized `H¹`. -/
noncomputable def hyperbolicCoexactCoreToH1 :
    HyperbolicSmoothCompactScalar →ₗ[ℝ] HyperbolicOneFormH1 :=
  hyperbolicSmoothCompactOneFormToH1.comp twoFormCodifferentialCore

/-- Algebraic compact exact core. -/
noncomputable def hyperbolicExactCoreH1 : Submodule ℝ HyperbolicOneFormH1 :=
  LinearMap.range hyperbolicExactCoreToH1

/-- Algebraic compact coexact core. -/
noncomputable def hyperbolicCoexactCoreH1 : Submodule ℝ HyperbolicOneFormH1 :=
  LinearMap.range hyperbolicCoexactCoreToH1

/-- CCP25's exact sector: the `H¹` closure of compact exact forms. -/
noncomputable def hyperbolicExactH1 : Submodule ℝ HyperbolicOneFormH1 :=
  hyperbolicExactCoreH1.topologicalClosure

/-- CCP25's coexact sector: the `H¹` closure of compact coexact forms. -/
noncomputable def hyperbolicCoexactH1 : Submodule ℝ HyperbolicOneFormH1 :=
  hyperbolicCoexactCoreH1.topologicalClosure

theorem isClosed_hyperbolicExactH1 :
    IsClosed (hyperbolicExactH1 : Set HyperbolicOneFormH1) :=
  by
    simpa only [hyperbolicExactH1] using
      Submodule.isClosed_topologicalClosure hyperbolicExactCoreH1

theorem isClosed_hyperbolicCoexactH1 :
    IsClosed (hyperbolicCoexactH1 : Set HyperbolicOneFormH1) :=
  by
    simpa only [hyperbolicCoexactH1] using
      Submodule.isClosed_topologicalClosure hyperbolicCoexactCoreH1

/-- The exact sector carries the inner product induced from the source `H¹` completion.
Naming the instance keeps its scalar-module hierarchy coherent in later Hilbert sums. -/
noncomputable instance (priority := 2000) hyperbolicExactH1InnerProductSpace :
    InnerProductSpace ℝ hyperbolicExactH1 :=
  Submodule.innerProductSpace hyperbolicExactH1

noncomputable instance (priority := 2000) hyperbolicExactH1Module :
    Module ℝ hyperbolicExactH1 :=
  hyperbolicExactH1InnerProductSpace.toNormedSpace.toModule

/-- The coexact sector carries the inner product induced from the source `H¹` completion.
Naming the instance keeps its scalar-module hierarchy coherent in later Hilbert sums. -/
noncomputable instance (priority := 2000) hyperbolicCoexactH1InnerProductSpace :
    InnerProductSpace ℝ hyperbolicCoexactH1 :=
  Submodule.innerProductSpace hyperbolicCoexactH1

noncomputable instance (priority := 2000) hyperbolicCoexactH1Module :
    Module ℝ hyperbolicCoexactH1 :=
  hyperbolicCoexactH1InnerProductSpace.toNormedSpace.toModule

noncomputable instance hyperbolicExactH1Complete : CompleteSpace hyperbolicExactH1 :=
  isClosed_hyperbolicExactH1.completeSpace_coe

noncomputable instance hyperbolicCoexactH1Complete : CompleteSpace hyperbolicCoexactH1 :=
  isClosed_hyperbolicCoexactH1.completeSpace_coe

theorem hyperbolicExactCoreH1_isOrtho_hyperbolicCoexactCoreH1 :
    hyperbolicExactCoreH1 ⟂ hyperbolicCoexactCoreH1 := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro alpha halpha beta hbeta
  rcases halpha with ⟨f, rfl⟩
  rcases hbeta with ⟨g, rfl⟩
  exact inner_hyperbolicExactCoexact_core f g

/-- The source-prescribed closed exact and coexact sectors are mutually `H¹`-orthogonal. -/
theorem hyperbolicExactH1_isOrtho_hyperbolicCoexactH1 :
    hyperbolicExactH1 ⟂ hyperbolicCoexactH1 := by
  change hyperbolicExactCoreH1.topologicalClosure ≤
    hyperbolicCoexactCoreH1.topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact hyperbolicExactCoreH1.topologicalClosure_minimal
    hyperbolicExactCoreH1_isOrtho_hyperbolicCoexactCoreH1
    hyperbolicCoexactCoreH1.isClosed_orthogonal

/-- The harmonic remainder of the closed exact and coexact sectors.  Its identification with the
distributional `L²` kernel of `(d,delta)` is the global elliptic-regularity theorem proved below. -/
noncomputable def hyperbolicHarmonicH1 : Submodule ℝ HyperbolicOneFormH1 :=
  hyperbolicExactH1ᗮ ⊓ hyperbolicCoexactH1ᗮ

theorem mem_hyperbolicHarmonicH1_iff (u : HyperbolicOneFormH1) :
    u ∈ hyperbolicHarmonicH1 ↔
      u ∈ hyperbolicExactH1ᗮ ∧ u ∈ hyperbolicCoexactH1ᗮ :=
  Iff.rfl

theorem isClosed_hyperbolicHarmonicH1 :
    IsClosed (hyperbolicHarmonicH1 : Set HyperbolicOneFormH1) := by
  exact hyperbolicExactH1.isClosed_orthogonal.inter
    hyperbolicCoexactH1.isClosed_orthogonal

noncomputable instance hyperbolicHarmonicH1Complete :
    CompleteSpace hyperbolicHarmonicH1 :=
  isClosed_hyperbolicHarmonicH1.completeSpace_coe

/-! ## Canonical orthogonal decomposition -/

/-- Orthogonal projection onto the closed exact `H¹` sector. -/
noncomputable def hyperbolicExactH1Projector :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormH1 :=
  hyperbolicExactH1.starProjection

/-- Remove the exact component. -/
noncomputable def hyperbolicExactH1Remainder :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormH1 :=
  ContinuousLinearMap.id ℝ HyperbolicOneFormH1 - hyperbolicExactH1Projector

/-- Orthogonal projection of the exact-free remainder onto the closed coexact sector. -/
noncomputable def hyperbolicCoexactH1Projector :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormH1 :=
  hyperbolicCoexactH1.starProjection.comp hyperbolicExactH1Remainder

/-- The residual projector after removing the exact and coexact components. -/
noncomputable def hyperbolicHarmonicH1Projector :
    HyperbolicOneFormH1 →L[ℝ] HyperbolicOneFormH1 :=
  ContinuousLinearMap.id ℝ HyperbolicOneFormH1 -
    hyperbolicExactH1Projector - hyperbolicCoexactH1Projector

theorem hyperbolicExactH1Projector_mem (u : HyperbolicOneFormH1) :
    hyperbolicExactH1Projector u ∈ hyperbolicExactH1 :=
  hyperbolicExactH1.starProjection_apply_mem u

theorem hyperbolicExactH1Remainder_mem_orthogonal (u : HyperbolicOneFormH1) :
    hyperbolicExactH1Remainder u ∈ hyperbolicExactH1ᗮ := by
  change u - hyperbolicExactH1.starProjection u ∈ hyperbolicExactH1ᗮ
  exact hyperbolicExactH1.sub_starProjection_mem_orthogonal u

theorem hyperbolicCoexactH1Projector_mem (u : HyperbolicOneFormH1) :
    hyperbolicCoexactH1Projector u ∈ hyperbolicCoexactH1 := by
  change hyperbolicCoexactH1.starProjection (hyperbolicExactH1Remainder u) ∈
    hyperbolicCoexactH1
  exact hyperbolicCoexactH1.starProjection_apply_mem _

theorem hyperbolicCoexactH1Projector_mem_exactOrthogonal
    (u : HyperbolicOneFormH1) :
    hyperbolicCoexactH1Projector u ∈ hyperbolicExactH1ᗮ :=
  hyperbolicExactH1_isOrtho_hyperbolicCoexactH1.ge
    (hyperbolicCoexactH1Projector_mem u)

theorem hyperbolicHarmonicH1Projector_mem (u : HyperbolicOneFormH1) :
    hyperbolicHarmonicH1Projector u ∈ hyperbolicHarmonicH1 := by
  rw [mem_hyperbolicHarmonicH1_iff]
  constructor
  · change hyperbolicExactH1Remainder u -
        hyperbolicCoexactH1Projector u ∈ hyperbolicExactH1ᗮ
    exact hyperbolicExactH1ᗮ.sub_mem
      (hyperbolicExactH1Remainder_mem_orthogonal u)
      (hyperbolicCoexactH1Projector_mem_exactOrthogonal u)
  · change hyperbolicExactH1Remainder u -
        hyperbolicCoexactH1.starProjection (hyperbolicExactH1Remainder u) ∈
          hyperbolicCoexactH1ᗮ
    exact hyperbolicCoexactH1.sub_starProjection_mem_orthogonal _

/-- Every source-normalized `H¹` one-form is the sum of its exact, coexact, and harmonic
components. -/
theorem hyperbolicH1_exact_add_coexact_add_harmonic (u : HyperbolicOneFormH1) :
    u = hyperbolicExactH1Projector u + hyperbolicCoexactH1Projector u +
      hyperbolicHarmonicH1Projector u := by
  simp only [hyperbolicHarmonicH1Projector, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  abel

theorem hyperbolicExactH1_isOrtho_hyperbolicHarmonicH1 :
    hyperbolicExactH1 ⟂ hyperbolicHarmonicH1 :=
  (Submodule.isOrtho_orthogonal_right hyperbolicExactH1).mono_right inf_le_left

theorem hyperbolicCoexactH1_isOrtho_hyperbolicHarmonicH1 :
    hyperbolicCoexactH1 ⟂ hyperbolicHarmonicH1 :=
  (Submodule.isOrtho_orthogonal_right hyperbolicCoexactH1).mono_right inf_le_right

/-- Uniqueness of the three closed-sector components. -/
theorem hyperbolicH1_decomposition_unique
    (u exact coexact harmonic : HyperbolicOneFormH1)
    (hexact : exact ∈ hyperbolicExactH1)
    (hcoexact : coexact ∈ hyperbolicCoexactH1)
    (hharmonic : harmonic ∈ hyperbolicHarmonicH1)
    (hsum : u = exact + coexact + harmonic) :
    exact = hyperbolicExactH1Projector u ∧
      coexact = hyperbolicCoexactH1Projector u ∧
      harmonic = hyperbolicHarmonicH1Projector u := by
  have hcoexactExactOrth : coexact ∈ hyperbolicExactH1ᗮ :=
    hyperbolicExactH1_isOrtho_hyperbolicCoexactH1.ge hcoexact
  have hharmonicExactOrth : harmonic ∈ hyperbolicExactH1ᗮ :=
    hharmonic.1
  have hrestExactOrth : u - exact ∈ hyperbolicExactH1ᗮ := by
    have hadd : coexact + harmonic ∈ hyperbolicExactH1ᗮ :=
      hyperbolicExactH1ᗮ.add_mem hcoexactExactOrth hharmonicExactOrth
    simpa [hsum, add_assoc] using hadd
  have hexactProjection : hyperbolicExactH1.starProjection u = exact :=
    hyperbolicExactH1.eq_starProjection_of_mem_orthogonal hexact hrestExactOrth
  have hharmonicCoexactOrth : harmonic ∈ hyperbolicCoexactH1ᗮ :=
    hharmonic.2
  have hcoexactRest :
      (u - hyperbolicExactH1.starProjection u) - coexact ∈
        hyperbolicCoexactH1ᗮ := by
    have heq : (u - hyperbolicExactH1.starProjection u) - coexact = harmonic := by
      rw [hexactProjection, hsum]
      abel
    rw [heq]
    exact hharmonicCoexactOrth
  have hcoexactProjection :
      hyperbolicCoexactH1.starProjection
          (u - hyperbolicExactH1.starProjection u) = coexact :=
    hyperbolicCoexactH1.eq_starProjection_of_mem_orthogonal
      hcoexact hcoexactRest
  constructor
  · exact hexactProjection.symm
  constructor
  · exact hcoexactProjection.symm
  · change harmonic = u - hyperbolicExactH1.starProjection u -
      hyperbolicCoexactH1.starProjection
        (u - hyperbolicExactH1.starProjection u)
    have hcoexactProjection' :
        hyperbolicCoexactH1.starProjection (u - exact) = coexact := by
      rw [← hexactProjection]
      exact hcoexactProjection
    rw [hexactProjection, hcoexactProjection', hsum]
    abel

end RiemannianFluids.HyperbolicPlane
