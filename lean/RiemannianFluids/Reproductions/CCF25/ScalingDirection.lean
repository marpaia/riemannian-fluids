import RiemannianFluids.Reproductions.CCF25.BoundaryConditions

/-! # CCF25 Sections 2 and 4: scaling-direction formulas -/

namespace RiemannianFluids

/-- Section 2: ellipsoidal orthonormal-frame, bracket-coefficient, and curvature identities. -/
@[proof_obligation]
theorem ccf25_ellipsoid_frame_and_scaling_geometry
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field)
    (ha : 0 < data.axisScale) (hε : 0 < data.thickness) :
    data.hasEllipsoidFrameIdentities ∧ data.hasScalingAsymptoticExpansion := by
  sorry

/-- Theorem 4.1 imported from CCG25: the tangential ambient Laplacian Gauss formula. -/
@[proof_obligation]
theorem ccf25_theorem_4_1_gauss_laplacian
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) :
    data.hasGaussLaplacianFormula := by
  sorry

/-- Lemma 4.2: the ellipsoid coefficient identity that converts the extrinsic remainder to `c_13^3`. -/
@[proof_obligation]
theorem ccf25_lemma_4_2_coefficient_identity
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field)
    (hFrame : data.hasEllipsoidFrameIdentities) :
    data.hasCoefficientIdentityLemma4_2 := by
  sorry

/-- Theorem 1.1, formula (1.4), Navier condition under tangency to every scaled ellipsoid. -/
@[proof_obligation]
theorem ccf25_theorem_1_1_navier_formula_1_4
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field)
    (hGeometry : data.hasEllipsoidFrameIdentities)
    (hExpansion : data.hasScalingAsymptoticExpansion)
    (hGauss : data.hasGaussLaplacianFormula)
    (hCoefficient : data.hasCoefficientIdentityLemma4_2) :
    ∀ field,
      data.navierAlwaysTangentialCandidate field =
        data.deformationLaplacian field + data.bracketCorrection field +
          (2 : ℤ) • data.squareCorrection field := by
  sorry

/-- Theorem 1.1, formula (1.5), Hodge condition under the same tangency hypothesis. -/
@[proof_obligation]
theorem ccf25_theorem_1_1_hodge_formula_1_5
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field)
    (hGeometry : data.hasEllipsoidFrameIdentities)
    (hExpansion : data.hasScalingAsymptoticExpansion)
    (hGauss : data.hasGaussLaplacianFormula)
    (hCoefficient : data.hasCoefficientIdentityLemma4_2) :
    ∀ field,
      data.hodgeAlwaysTangentialCandidate field =
        data.hodgeLaplacian field + data.lieDerivativeCorrection field := by
  sorry

/-- Theorem 1.3, formula (1.6), the ambient/intrinsic divergence-free Navier branch. -/
@[proof_obligation]
theorem ccf25_theorem_1_3_navier_formula_1_6
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field)
    (hGeometry : data.hasEllipsoidFrameIdentities)
    (hExpansion : data.hasScalingAsymptoticExpansion)
    (hGauss : data.hasGaussLaplacianFormula)
    (hCoefficient : data.hasCoefficientIdentityLemma4_2) :
    ∀ field,
      data.navierDoubleDivergenceFreeCandidate field =
        data.deformationLaplacian field + data.bracketCorrection field := by
  sorry

/-- Theorem 1.3, formula (1.7), the ambient/intrinsic divergence-free Hodge branch. -/
@[proof_obligation]
theorem ccf25_theorem_1_3_hodge_formula_1_7
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field)
    (hGeometry : data.hasEllipsoidFrameIdentities)
    (hExpansion : data.hasScalingAsymptoticExpansion)
    (hGauss : data.hasGaussLaplacianFormula)
    (hCoefficient : data.hasCoefficientIdentityLemma4_2) :
    ∀ field,
      data.hodgeDoubleDivergenceFreeCandidate field =
      data.hodgeLaplacian field + data.lieDerivativeCorrection field -
        (2 : ℤ) • data.squareCorrection field := by
  sorry

/-- CCF25 Theorem 1.1 assembled from its separately stated Navier and Hodge formulas. -/
@[proof_assembly]
theorem ccf25_theorem_1_1
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) :
    ccf25Theorem1_1Statement data := by
  intro ha hε
  have hGeometry := ccf25_ellipsoid_frame_and_scaling_geometry data ha hε
  have hGauss := ccf25_theorem_4_1_gauss_laplacian data
  have hCoefficient := ccf25_lemma_4_2_coefficient_identity data hGeometry.1
  exact
    ⟨ccf25_theorem_1_1_navier_formula_1_4 data hGeometry.1 hGeometry.2 hGauss hCoefficient,
      ccf25_theorem_1_1_hodge_formula_1_5 data hGeometry.1 hGeometry.2 hGauss hCoefficient⟩

/-- CCF25 Theorem 1.3 assembled from its separately stated Navier and Hodge formulas. -/
@[proof_assembly]
theorem ccf25_theorem_1_3
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) :
    ccf25Theorem1_3Statement data := by
  intro ha hε
  have hGeometry := ccf25_ellipsoid_frame_and_scaling_geometry data ha hε
  have hGauss := ccf25_theorem_4_1_gauss_laplacian data
  have hCoefficient := ccf25_lemma_4_2_coefficient_identity data hGeometry.1
  exact
    ⟨ccf25_theorem_1_3_navier_formula_1_6 data hGeometry.1 hGeometry.2 hGauss hCoefficient,
      ccf25_theorem_1_3_hodge_formula_1_7 data hGeometry.1 hGeometry.2 hGauss hCoefficient⟩

@[literature_terminal]
theorem ccf25_theorems_1_1_and_1_3
    {Field : Type*} [AddCommGroup Field]
    (data : CCF25ScalingFormulaData Field) :
    ccf25ScalingFormulaStatement data := by
  intro ha hε
  have hTheorem1_1 := ccf25_theorem_1_1 data ha hε
  have hTheorem1_3 := ccf25_theorem_1_3 data ha hε
  exact ⟨hTheorem1_1.1, hTheorem1_1.2, hTheorem1_3.1, hTheorem1_3.2⟩


end RiemannianFluids
