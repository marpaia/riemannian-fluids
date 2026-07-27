import RiemannianFluids.Reproductions.CCP25.Section2

/-! # CCP25 Section 3: harmonic L2 forms -/

namespace RiemannianFluids

/-- CCP25 Theorem 3.1: an `L2` form is harmonic exactly when it is weakly closed and co-closed. -/
@[proof_obligation]
theorem ccp25_theorem_3_1_harmonic_iff_closed_coclosed
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form) :
    ∀ form,
      data.hodge.isL2Harmonic form ↔
        data.isWeaklyClosed form ∧ data.isWeaklyCoClosed form := by
  sorry

/-- CCP25 Theorem 3.2: every `L2` harmonic form lies in `H1`, with the explicit curvature estimate represented by the integrated identity. -/
@[proof_obligation]
theorem ccp25_theorem_3_2_l2_harmonic_is_h1
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ form, data.hodge.isL2Harmonic form →
      data.isSobolevH1 form ∧ data.hasIntegratedWeitzenbockIdentity form := by
  have hWeitzenbock :=
    ccp25_lemma_2_1_constant_curvature_weizenbock data ha hDegree hGeometry
  have hIntegrated :=
    ccp25_corollary_2_2_integrated_weizenbock data ha hDegree hGeometry
  have hNorm := ccp25_equation_2_11_bochner_norm data ha hDegree hGeometry
    hWeitzenbock hIntegrated
  sorry


end RiemannianFluids
