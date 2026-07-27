import RiemannianFluids.Reproductions.CCP25.Section4

/-! # CCP25 Section 5: the hyperbolic-plane decomposition -/

namespace RiemannianFluids

/-- Section 5, Lemma 5.1: on the simply connected hyperbolic plane, every compactly supported solenoidal one-form is the codifferential of a compactly supported two-form, and conversely after `H¹` closure. -/
@[proof_obligation]
theorem ccp25_lemma_5_1_solenoidal_closure_eq_coexact_closure
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25HelmholtzData Form)
    (hDimension : data.h1.dimension = 2)
    (hDegree : data.h1.degree = 1)
    (ha : 0 ≤ data.h1.curvatureScale)
    (hGeometry : data.h1.isHyperbolicSpaceForm) :
    ∀ form,
      data.isCompactSolenoidalH1Closure form ↔
        data.h1.hodge.isCoexactClosure form := by
  sorry

/-- Restrict Theorem 1.3 to weakly co-closed one-forms; its exact component vanishes and leaves the solenoidal plus harmonic sum. -/
@[proof_obligation]
theorem ccp25_theorem_1_4_divergence_free_restriction
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25HelmholtzData Form)
    (hDimension : data.h1.dimension = 2)
    (hDegree : data.h1.degree = 1)
    (ha : 0 ≤ data.h1.curvatureScale)
    (hGeometry : data.h1.isHyperbolicSpaceForm)
    (hHodge : HasH1HodgeDecomposition data.h1.hodge) :
    HasUniqueBinaryDecomposition
      data.isWeaklyDivergenceFree
      data.isCompactSolenoidalH1Closure
      data.h1.hodge.isL2Harmonic := by
  sorry

/-- Theorem 1.4 assembled in the source order: Theorem 1.3, divergence-free restriction, then Lemma 5.1. -/
@[literature_terminal]
theorem ccp25_theorem_1_4
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25HelmholtzData Form) :
    ccp25H1HelmholtzDecompositionStatement data := by
  intro hDimension hDegree ha hGeometry
  have hDegreeBound : data.h1.degree ≤ data.h1.dimension := by omega
  have hHodge :=
    (ccp25_theorem_1_3_assembly data.h1 ha hDegreeBound hGeometry).1
  have hCompact :=
    ccp25_theorem_1_4_divergence_free_restriction data hDimension hDegree ha
      hGeometry hHodge
  have hEquality :=
    ccp25_lemma_5_1_solenoidal_closure_eq_coexact_closure data hDimension
      hDegree ha hGeometry
  have hCoexact : HasUniqueBinaryDecomposition
      data.isWeaklyDivergenceFree
      data.h1.hodge.isCoexactClosure
      data.h1.hodge.isL2Harmonic := by
    intro form hWhole
    obtain ⟨left, right, hLeft, hRight, hSum, hUnique⟩ := hCompact form hWhole
    refine ⟨left, right, (hEquality left).mp hLeft, hRight, hSum, ?_⟩
    intro otherLeft otherRight hOtherLeft hOtherRight hOtherSum
    exact hUnique otherLeft otherRight ((hEquality otherLeft).mpr hOtherLeft)
      hOtherRight hOtherSum
  exact ⟨hCompact, hEquality, hCoexact⟩


end RiemannianFluids
