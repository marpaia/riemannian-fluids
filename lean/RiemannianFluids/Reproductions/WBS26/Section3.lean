import RiemannianFluids.Reproductions.WBS26.Statements

/-! # WBS26 Section 3: formal hypersurface decomposition -/

namespace RiemannianFluids

/-- Fermi-coordinate metric evolution and the parallel-surface shape operator. -/
@[proof_obligation]
theorem wbs26_fermi_coordinate_geometry
    {Field : Type*} [AddCommGroup Field] [Module ℝ Field]
    (data : WBS26InterpolatingData Field)
    (hGeometry : data.isSmoothClosedOrientableHypersurface) :
    data.hasFermiMetricEvolution := by
  sorry

/-- Lemma 3.1, equation (13): reduce each wall law to conditions on the first normal coefficient. -/
@[proof_obligation]
theorem wbs26_lemma_3_1_wall_reduction
    {Field : Type*} [AddCommGroup Field] [Module ℝ Field]
    (data : WBS26InterpolatingData Field)
    (hFermi : data.hasFermiMetricEvolution) :
    data.hasWallReduction13 := by
  sorry

/-- Proposition 3.2, equation (14): solve the two wall equations for the quadratic normal profile. -/
@[proof_obligation]
theorem wbs26_proposition_3_2_two_wall_profile
    {SurfaceField Profile : Type*}
    (data : WBS26WallProfileData SurfaceField Profile)
    (hGeometry : data.isSmoothClosedOrientableHypersurface) :
    ∀ wall thickness field,
      0 < thickness →
        data.hasQuadraticNormalExpansion wall thickness field := by
  sorry

/-- Equation (19): the per-condition normal corrector cancels the solenoidal defect. -/
@[proof_obligation]
theorem wbs26_equation_19_solenoidal_corrector
    {SurfaceField Profile : Type*}
    (data : WBS26WallProfileData SurfaceField Profile) :
    ∀ wall thickness field,
      0 < thickness →
      data.hasQuadraticNormalExpansion wall thickness field →
        data.hasSolenoidalCorrector19 wall thickness field := by
  sorry

/-- Proposition 3.2 after the equation (19) correction: both walls, trace, and exact solenoidality. -/
@[proof_obligation]
theorem wbs26_corrected_profile_properties
    {SurfaceField Profile : Type*}
    (data : WBS26WallProfileData SurfaceField Profile) :
    ∀ wall thickness field,
      0 < thickness →
      data.hasQuadraticNormalExpansion wall thickness field →
      data.hasSolenoidalCorrector19 wall thickness field →
        let profile := data.profile wall thickness field
        data.matchesSurfaceField profile field ∧
          data.isSolenoidal profile ∧
          data.satisfiesLowerWall wall profile ∧
          data.satisfiesUpperWall wall profile := by
  sorry

@[literature_terminal]
theorem wbs26_proposition_3_2_profile_terminal
    {SurfaceField Profile : Type*}
    (data : WBS26WallProfileData SurfaceField Profile) :
    wbs26TwoWallProfileStatement data := by
  intro hGeometry
  intro wall thickness field hThickness
  have hExpansion := wbs26_proposition_3_2_two_wall_profile data hGeometry wall thickness field hThickness
  have hCorrector := wbs26_equation_19_solenoidal_corrector data wall thickness field
    hThickness hExpansion
  exact wbs26_corrected_profile_properties data wall thickness field hThickness
    hExpansion hCorrector

/-- Theorem 3.3, equations (16)--(18): wall reduction and the matched profile give the interpolation coefficients. -/
@[proof_obligation]
theorem wbs26_theorem_3_3_coefficient_identification
    {Field : Type*} [AddCommGroup Field] [Module ℝ Field]
    (data : WBS26InterpolatingData Field)
    (hFermi : data.hasFermiMetricEvolution)
    (hWall : data.hasWallReduction13) :
    data.hasFormalCoefficientIdentities16To18 ∧
      ∀ a field,
        data.tangentialAmbientOperator a field =
          data.deformationLaplacian field +
            (2 * a) • data.ricciTerm field +
            (4 * a * (1 - a)) • data.shapeSquareTerm field := by
  sorry

@[literature_terminal]
theorem wbs26_theorem_3_3_formal_selection
    {Field : Type*} [AddCommGroup Field] [Module ℝ Field]
    (data : WBS26InterpolatingData Field) :
    wbs26LocalInterpolatingFamilyStatement data := by
  intro hGeometry
  have hFermi := wbs26_fermi_coordinate_geometry data hGeometry
  have hWall := wbs26_lemma_3_1_wall_reduction data hFermi
  exact (wbs26_theorem_3_3_coefficient_identification data hFermi hWall).2


end RiemannianFluids
