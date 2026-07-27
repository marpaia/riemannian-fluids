import RiemannianFluids.Reproductions.CCF25.ScalingDirection

/-! # CCF25 Sections 5--6: normal-direction formulas -/

namespace RiemannianFluids

/-- Theorem 1.6: normal-coordinate Hodge expansion. -/
@[proof_obligation]
theorem ccf25_theorem_1_6_normal_hodge
    {Field : Type*}
    (data : CCF25NormalFormulaData Field) :
    data.hasTubularNormalCoordinates → data.hasNormalPowerSeries →
      ∀ field, data.hodgeBoundaryCandidate field = data.hodgeLaplacian field := by
  sorry

/-- Remark 1.8 and Section 6: the normal-coordinate Navier expansion. -/
@[proof_obligation]
theorem ccf25_section_6_normal_navier
    {Field : Type*}
    (data : CCF25NormalFormulaData Field) :
    data.hasTubularNormalCoordinates → data.hasNormalPowerSeries →
      ∀ field, data.navierBoundaryCandidate field = data.deformationLaplacian field := by
  sorry

@[literature_terminal]
theorem ccf25_theorem_1_6_and_remark_1_8
    {Field : Type*}
    (data : CCF25NormalFormulaData Field)
    (hCoordinates : data.hasTubularNormalCoordinates)
    (hSeries : data.hasNormalPowerSeries) :
    ccf25NormalDirectionStatement data := by
  intro ha hε
  exact ⟨ccf25_theorem_1_6_normal_hodge data hCoordinates hSeries,
    ccf25_section_6_normal_navier data hCoordinates hSeries⟩

/-- Remark 1.5: the ellipsoidal coefficient `c_13^3` vanishes in the round case. -/
@[proof_obligation]
theorem ccf25_remark_1_5_round_coefficient_vanishes
    {Field : Type*} (data : CCF25CandidateData Field)
    (hSphere : data.isRoundSphere) :
    data.scalingCoefficientVanishes := by
  sorry

/-- Substitution of `c_13^3 = 0` into formulas (1.4)--(1.7). -/
@[proof_obligation]
theorem ccf25_round_candidate_reductions
    {Field : Type*} (data : CCF25CandidateData Field)
    (hSphere : data.isRoundSphere)
    (hCoefficient : data.scalingCoefficientVanishes) :
    (∀ field, data.candidate 0 field = data.deformationEndpoint field) ∧
    (∀ field, data.candidate 1 field = data.hodgeEndpoint field) ∧
    (∀ field, data.candidate 2 field = data.deformationEndpoint field) ∧
    (∀ field, data.candidate 3 field = data.hodgeEndpoint field) := by
  sorry

@[literature_terminal]
theorem ccf25_remark_1_5_four_candidates_on_sphere
    {Field : Type*} (data : CCF25CandidateData Field) :
    ccf25FourCandidatesSphereStatement data := by
  intro hSphere
  exact ccf25_round_candidate_reductions data hSphere
    (ccf25_remark_1_5_round_coefficient_vanishes data hSphere)

/-- The nonspherical coefficient is nonzero and admits a field on which the scaling and normal formulas differ. -/
@[proof_obligation]
theorem ccf25_nonspherical_averaging_witness
    {Field : Type*} (data : CCF25AveragingData Field)
    (hEllipsoid : data.isGenuinelyNonsphericalAxisymmetricEllipsoid) :
    ∃ field, data.scalingDirectionAverage field ≠ data.normalDirectionAverage field := by
  sorry

@[literature_terminal]
theorem ccf25_averaging_direction_dependence
    {Field : Type*} (data : CCF25AveragingData Field) :
    ccf25AveragingDependenceStatement data := by
  exact ccf25_nonspherical_averaging_witness data


end RiemannianFluids
