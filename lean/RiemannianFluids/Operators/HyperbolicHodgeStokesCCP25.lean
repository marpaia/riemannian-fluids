import RiemannianFluids.FunctionSpaces.HyperbolicCCP25
import RiemannianFluids.Operators.HyperbolicHodgeStokes

/-!
# Source-domain identification for the hyperbolic Hodge--Stokes operator

The Hodge--Stokes operator is constructed without assuming global harmonic regularity, so its
form domain uses a coexact source `H¹` coordinate and an actual harmonic `L²` coordinate.  The
completed CCP25 theorem supplies the missing canonical `H¹` representative of the latter.  This
module proves that the independently constructed form domain is continuously linearly equivalent
to the full source divergence-free `H¹` space, and that this equivalence intertwines both the
`L²` embedding and the weak Hodge derivative.
-/

noncomputable section

namespace RiemannianFluids.HyperbolicPlane

open Set
open scoped RealInnerProductSpace

/-- The complete source `H¹` divergence-free carrier: the orthogonal complement of exact forms. -/
abbrev HyperbolicDivergenceFreeH1 : Submodule ℝ HyperbolicOneFormH1 :=
  hyperbolicExactH1ᗮ

theorem isClosed_hyperbolicDivergenceFreeH1 :
    IsClosed (HyperbolicDivergenceFreeH1 : Set HyperbolicOneFormH1) :=
  hyperbolicExactH1.isClosed_orthogonal

noncomputable instance hyperbolicDivergenceFreeH1Complete :
    CompleteSpace HyperbolicDivergenceFreeH1 :=
  isClosed_hyperbolicDivergenceFreeH1.completeSpace_coe

theorem norm_hyperbolicHarmonicL2ToH1_le_two
    (h : hyperbolicHarmonicL2) :
    ‖hyperbolicHarmonicL2ToH1 h‖ ≤ 2 * ‖h‖ := by
  have hsq := norm_sq_hyperbolicHarmonicL2ToH1 h
  have hx : 0 ≤ ‖hyperbolicHarmonicL2ToH1 h‖ := norm_nonneg _
  have hy : 0 ≤ ‖h‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖h‖)]

/-- The CCP25 harmonic recovery as a bounded linear map. -/
noncomputable def hyperbolicHarmonicL2ToH1Continuous :
    hyperbolicHarmonicL2 →L[ℝ] HyperbolicOneFormH1 :=
  hyperbolicHarmonicL2ToH1.mkContinuous 2
    norm_hyperbolicHarmonicL2ToH1_le_two

@[simp] theorem hyperbolicHarmonicL2ToH1Continuous_apply
    (h : hyperbolicHarmonicL2) :
    hyperbolicHarmonicL2ToH1Continuous h = hyperbolicHarmonicL2ToH1 h :=
  rfl

/-- Add the coexact source coordinate to the recovered harmonic source coordinate. -/
noncomputable def hyperbolicHodgeStokesToH1Ambient :
    HyperbolicHodgeStokesFormDomain →L[ℝ] HyperbolicOneFormH1 :=
  ((Submodule.subtypeL hyperbolicCoexactH1).comp
      hyperbolicHodgeStokesCoexact) +
    (hyperbolicHarmonicL2ToH1Continuous.comp
      hyperbolicHodgeStokesHarmonic)

@[simp] theorem hyperbolicHodgeStokesToH1Ambient_apply
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicHodgeStokesToH1Ambient u =
      (u.ofLp.1 : HyperbolicOneFormH1) +
        hyperbolicHarmonicL2ToH1 u.ofLp.2 :=
  rfl

/-- The independently constructed form domain, now viewed as full divergence-free source `H¹`. -/
noncomputable def hyperbolicHodgeStokesToDivergenceFreeH1 :
    HyperbolicHodgeStokesFormDomain →L[ℝ] HyperbolicDivergenceFreeH1 :=
  ContinuousLinearMap.codRestrict hyperbolicHodgeStokesToH1Ambient
    HyperbolicDivergenceFreeH1 (fun u ↦
      HyperbolicDivergenceFreeH1.add_mem
        (hyperbolicExactH1_isOrtho_hyperbolicCoexactH1.ge u.ofLp.1.property)
        (hyperbolicHarmonicL2ToH1_mem_harmonic u.ofLp.2).1)

@[simp] theorem hyperbolicHodgeStokesToDivergenceFreeH1_coe
    (u : HyperbolicHodgeStokesFormDomain) :
    (hyperbolicHodgeStokesToDivergenceFreeH1 u : HyperbolicOneFormH1) =
      (u.ofLp.1 : HyperbolicOneFormH1) +
        hyperbolicHarmonicL2ToH1 u.ofLp.2 :=
  rfl

/-- The source-domain identification intertwines the concrete `L²` embeddings. -/
theorem hyperbolicHodgeStokesToDivergenceFreeH1_toL2
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicOneFormH1ToL2 (hyperbolicHodgeStokesToDivergenceFreeH1 u) =
      (hyperbolicHodgeStokesEmbedding u : HyperbolicOneFormL2) := by
  change hyperbolicOneFormH1ToL2
      ((u.ofLp.1 : HyperbolicOneFormH1) +
        hyperbolicHarmonicL2ToH1 u.ofLp.2) = _
  calc
    _ = hyperbolicOneFormH1ToL2 (u.ofLp.1 : HyperbolicOneFormH1) +
          hyperbolicOneFormH1ToL2 (hyperbolicHarmonicL2ToH1 u.ofLp.2) :=
      map_add _ _ _
    _ = hyperbolicOneFormH1ToL2 (u.ofLp.1 : HyperbolicOneFormH1) +
          (u.ofLp.2 : HyperbolicOneFormL2) := by
      rw [hyperbolicOneFormH1ToL2_harmonicL2ToH1]
    _ = _ := rfl

/-- The source-domain identification also intertwines the weak Hodge derivative. -/
theorem hyperbolicHodgeStokesToDivergenceFreeH1_hodge
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicOneFormH1Hodge (hyperbolicHodgeStokesToDivergenceFreeH1 u) =
      hyperbolicHodgeStokesDerivative u := by
  change hyperbolicOneFormH1Hodge
      ((u.ofLp.1 : HyperbolicOneFormH1) +
        hyperbolicHarmonicL2ToH1 u.ofLp.2) = _
  calc
    _ = hyperbolicOneFormH1Hodge (u.ofLp.1 : HyperbolicOneFormH1) +
          hyperbolicOneFormH1Hodge (hyperbolicHarmonicL2ToH1 u.ofLp.2) :=
      map_add _ _ _
    _ = hyperbolicOneFormH1Hodge (u.ofLp.1 : HyperbolicOneFormH1) := by
      rw [hyperbolicHarmonicL2ToH1_hodge_eq_zero, add_zero]
    _ = _ := rfl

theorem hyperbolicHodgeStokesToDivergenceFreeH1_injective :
    Function.Injective hyperbolicHodgeStokesToDivergenceFreeH1 := by
  intro u v huv
  apply hyperbolicHodgeStokesEmbedding_injective
  apply Subtype.ext
  have hsource :
      (hyperbolicHodgeStokesToDivergenceFreeH1 u : HyperbolicOneFormH1) =
        hyperbolicHodgeStokesToDivergenceFreeH1 v :=
    congrArg Subtype.val huv
  have himage := congrArg hyperbolicOneFormH1ToL2 hsource
  simpa only [hyperbolicHodgeStokesToDivergenceFreeH1_toL2] using himage

/-- Coexact coordinate of a source divergence-free `H¹` form. -/
noncomputable def hyperbolicDivergenceFreeH1Coexact :
    HyperbolicDivergenceFreeH1 →L[ℝ] hyperbolicCoexactH1 :=
  ContinuousLinearMap.codRestrict
    (hyperbolicCoexactH1Projector.comp
      (Submodule.subtypeL HyperbolicDivergenceFreeH1))
    hyperbolicCoexactH1
    (fun u ↦ hyperbolicCoexactH1Projector_mem u)

/-- Source harmonic coordinate of a source divergence-free `H¹` form. -/
noncomputable def hyperbolicDivergenceFreeH1Harmonic :
    HyperbolicDivergenceFreeH1 →L[ℝ] hyperbolicHarmonicH1 :=
  ContinuousLinearMap.codRestrict
    (hyperbolicHarmonicH1Projector.comp
      (Submodule.subtypeL HyperbolicDivergenceFreeH1))
    hyperbolicHarmonicH1
    (fun u ↦ hyperbolicHarmonicH1Projector_mem u)

/-- Convert the source harmonic coordinate to the actual harmonic `L²` coordinate. -/
noncomputable def hyperbolicDivergenceFreeH1HarmonicL2 :
    HyperbolicDivergenceFreeH1 →L[ℝ] hyperbolicHarmonicL2 :=
  hyperbolicHarmonicH1ToHarmonicL2.comp
    hyperbolicDivergenceFreeH1Harmonic

/-- Canonical inverse coordinates from full divergence-free source `H¹` to the constructed
Hodge--Stokes form domain. -/
noncomputable def hyperbolicDivergenceFreeH1ToHodgeStokes :
    HyperbolicDivergenceFreeH1 →L[ℝ] HyperbolicHodgeStokesFormDomain :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
      hyperbolicCoexactH1 hyperbolicHarmonicL2).symm.toContinuousLinearMap.comp
    (hyperbolicDivergenceFreeH1Coexact.prod
      hyperbolicDivergenceFreeH1HarmonicL2)

theorem hyperbolicHodgeStokesToDivergenceFreeH1_rightInverse
    (u : HyperbolicDivergenceFreeH1) :
    hyperbolicHodgeStokesToDivergenceFreeH1
        (hyperbolicDivergenceFreeH1ToHodgeStokes u) = u := by
  apply Subtype.ext
  change hyperbolicCoexactH1Projector (u : HyperbolicOneFormH1) +
      hyperbolicHarmonicL2ToH1
        (hyperbolicHarmonicH1ToHarmonicL2
          ⟨hyperbolicHarmonicH1Projector (u : HyperbolicOneFormH1),
            hyperbolicHarmonicH1Projector_mem (u : HyperbolicOneFormH1)⟩) =
    (u : HyperbolicOneFormH1)
  have hexact : hyperbolicExactH1Projector (u : HyperbolicOneFormH1) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff hyperbolicExactH1).2 u.property
  have hsum := hyperbolicH1_exact_add_coexact_add_harmonic
    (u : HyperbolicOneFormH1)
  rw [hexact, zero_add] at hsum
  rw [hyperbolicHarmonicL2ToH1_toHarmonicL2]
  exact hsum.symm

theorem hyperbolicHodgeStokesToDivergenceFreeH1_surjective :
    Function.Surjective hyperbolicHodgeStokesToDivergenceFreeH1 := by
  intro u
  exact ⟨hyperbolicDivergenceFreeH1ToHodgeStokes u,
    hyperbolicHodgeStokesToDivergenceFreeH1_rightInverse u⟩

theorem hyperbolicHodgeStokesToDivergenceFreeH1_leftInverse
    (u : HyperbolicHodgeStokesFormDomain) :
    hyperbolicDivergenceFreeH1ToHodgeStokes
        (hyperbolicHodgeStokesToDivergenceFreeH1 u) = u := by
  apply hyperbolicHodgeStokesToDivergenceFreeH1_injective
  exact hyperbolicHodgeStokesToDivergenceFreeH1_rightInverse
    (hyperbolicHodgeStokesToDivergenceFreeH1 u)

/-- Exact continuous linear identification of the constructed form domain with the full source
divergence-free `H¹` carrier. -/
noncomputable def hyperbolicHodgeStokesFormDomainEquivDivergenceFreeH1 :
    HyperbolicHodgeStokesFormDomain ≃L[ℝ] HyperbolicDivergenceFreeH1 where
  toFun := hyperbolicHodgeStokesToDivergenceFreeH1
  invFun := hyperbolicDivergenceFreeH1ToHodgeStokes
  left_inv := hyperbolicHodgeStokesToDivergenceFreeH1_leftInverse
  right_inv := hyperbolicHodgeStokesToDivergenceFreeH1_rightInverse
  map_add' := hyperbolicHodgeStokesToDivergenceFreeH1.map_add
  map_smul' := hyperbolicHodgeStokesToDivergenceFreeH1.map_smul
  continuous_toFun := hyperbolicHodgeStokesToDivergenceFreeH1.continuous
  continuous_invFun := hyperbolicDivergenceFreeH1ToHodgeStokes.continuous

end RiemannianFluids.HyperbolicPlane
