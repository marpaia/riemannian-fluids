import RiemannianFluids.Reproductions.CCP25.Section3

/-! # CCP25 Section 4: Hodge decomposition -/

namespace RiemannianFluids

/-- CCP25 Lemma 4.1: the exact and coexact `H¹` closures are orthogonal. -/
@[proof_obligation]
theorem ccp25_lemma_4_1_exact_coexact_orthogonal
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ exact coexact,
      data.hodge.isExactClosure exact →
        data.hodge.isCoexactClosure coexact →
          data.hodge.h1Orthogonal exact coexact := by
  have hWeitzenbock :=
    ccp25_lemma_2_1_constant_curvature_weizenbock data ha hDegree hGeometry
  sorry

/-- CCP25 Lemma 4.2: every `L²` harmonic form belongs to `X⊥`. -/
@[proof_obligation]
theorem ccp25_lemma_4_2_harmonic_in_orthogonal_complement
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ harmonic,
      data.hodge.isL2Harmonic harmonic →
        (∀ exact,
          data.hodge.isExactClosure exact →
            data.hodge.h1Orthogonal exact harmonic) ∧
        ∀ coexact,
          data.hodge.isCoexactClosure coexact →
          data.hodge.h1Orthogonal coexact harmonic := by
  have hHarmonicH1 :=
    ccp25_theorem_3_2_l2_harmonic_is_h1 data ha hDegree hGeometry
  sorry

/-- Proposition 4.3, equations (4.10)--(4.18): the exact-orthogonal current has zero weak codifferential. -/
@[proof_obligation]
theorem ccp25_proposition_4_3_coclosed_half
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ form,
      data.isSobolevH1 form →
      (∀ exact, data.hodge.isExactClosure exact → data.hodge.h1Orthogonal exact form) →
        data.isWeaklyCoClosed form := by
  have hWeakDerivatives := ccp25_lemma_2_7_h1_has_weak_d_and_dstar data
  have hWeitzenbock :=
    ccp25_lemma_2_1_constant_curvature_weizenbock data ha hDegree hGeometry
  sorry

/-- Proposition 4.3, equations (4.19)--(4.25): the coexact-orthogonal current has zero weak exterior derivative. -/
@[proof_obligation]
theorem ccp25_proposition_4_3_closed_half
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ form,
      data.isSobolevH1 form →
      (∀ coexact, data.hodge.isCoexactClosure coexact → data.hodge.h1Orthogonal coexact form) →
        data.isWeaklyClosed form := by
  have hWeakDerivatives := ccp25_lemma_2_7_h1_has_weak_d_and_dstar data
  have hWeitzenbock :=
    ccp25_lemma_2_1_constant_curvature_weizenbock data ha hDegree hGeometry
  sorry

/-- CCP25 Proposition 4.3, assembled in its two source halves: first `d*u = 0`, then `du = 0`. -/
@[proof_assembly]
theorem ccp25_proposition_4_3_orthogonal_complement_is_harmonic
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ form,
      data.isSobolevH1 form →
      (∀ exact,
        data.hodge.isExactClosure exact →
          data.hodge.h1Orthogonal exact form) →
      (∀ coexact,
        data.hodge.isCoexactClosure coexact →
          data.hodge.h1Orthogonal coexact form) →
      data.hodge.isL2Harmonic form := by
  intro form hH1 hExact hCoexact
  have hClosed := ccp25_proposition_4_3_closed_half data ha hDegree hGeometry
    form hH1 hCoexact
  have hCoClosed := ccp25_proposition_4_3_coclosed_half data ha hDegree hGeometry
    form hH1 hExact
  exact (ccp25_theorem_3_1_harmonic_iff_closed_coclosed data form).2 ⟨hClosed, hCoClosed⟩

/-- CCP25 Lemma 4.4: every element of the `H1` exact closure has a current primitive. -/
@[proof_obligation]
theorem ccp25_lemma_4_4_exact_current_representation
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (hCurrentCriterion : data.hasCurrentDeRhamCriterion) :
    ∀ exact, data.hodge.isExactClosure exact → data.hasCurrentPrimitive exact := by
  sorry

/-- CCP25 Lemma 4.5: every element of the `H1` coexact closure has a current coprimitive. -/
@[proof_obligation]
theorem ccp25_lemma_4_5_coexact_current_representation
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (hCurrentCriterion : data.hasCurrentDeRhamCriterion) :
    ∀ coexact, data.hodge.isCoexactClosure coexact → data.hasCurrentCoprimitive coexact := by
  sorry

/-- Section 4.2, equation (4.3) and the Hilbert projection step: Lemmas 4.1--4.2 and Proposition 4.3 identify `X⊥` with the harmonic forms. -/
@[proof_obligation]
theorem ccp25_section_4_2_hilbert_projection
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    HasH1HodgeDecomposition data.hodge := by
  have hExactCoexact :=
    ccp25_lemma_4_1_exact_coexact_orthogonal data ha hDegree hGeometry
  have hHarmonic :=
    ccp25_lemma_4_2_harmonic_in_orthogonal_complement data ha hDegree hGeometry
  have hComplement :=
    ccp25_proposition_4_3_orthogonal_complement_is_harmonic data ha hDegree hGeometry
  sorry

/-- Theorem 1.3, assembled from the Hilbert projection and current-representation halves. -/
@[proof_assembly]
theorem ccp25_theorem_1_3_assembly
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    HasH1HodgeDecomposition data.hodge ∧
      (∀ exact, data.hodge.isExactClosure exact → data.hasCurrentPrimitive exact) ∧
      ∀ coexact, data.hodge.isCoexactClosure coexact → data.hasCurrentCoprimitive coexact := by
  have hDeRham := ccp25_theorem_2_10_current_de_rham data
  exact ⟨ccp25_section_4_2_hilbert_projection data ha hDegree hGeometry,
    ccp25_lemma_4_4_exact_current_representation data hDeRham,
    ccp25_lemma_4_5_coexact_current_representation data hDeRham⟩

@[literature_terminal]
theorem ccp25_theorem_1_3
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form) :
    ccp25H1NoncompactDecompositionStatement data := by
  intro hDimension ha hDegree hGeometry
  exact ccp25_theorem_1_3_assembly data ha hDegree hGeometry


end RiemannianFluids
