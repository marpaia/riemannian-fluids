import RiemannianFluids.Reproductions.CCY23.Statements

/-! # CCY23 Section 2: restriction to the ellipsoid -/

namespace RiemannianFluids

/-- Equations (2.1)--(2.4): metric, inverse metric, volume form, and `grad rho` in ellipsoidal coordinates. -/
@[proof_obligation]
theorem ccy23_ellipsoid_coordinate_geometry
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form)
    (ha : 0 < data.axisScale) :
    data.hasEllipsoidMetricAndVolumeIdentities := by
  sorry

/-- Equations (2.5)--(2.9): the ambient Hodge Laplacian restricted to the ellipsoid. -/
@[proof_obligation]
theorem ccy23_ambient_hodge_components
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form)
    (hCoordinates : data.hasEllipsoidMetricAndVolumeIdentities) :
    ∀ field, data.hasAmbientHodgeComponentFormula field := by
  sorry

/-- Section 2.1: the intrinsic Hodge Laplacian's `dphi` and `dtheta` components. -/
@[proof_obligation]
theorem ccy23_intrinsic_hodge_components
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form)
    (hCoordinates : data.hasEllipsoidMetricAndVolumeIdentities) :
    ∀ field, data.hasIntrinsicHodgeComponentFormula field := by
  sorry

/-- Equations (2.16)--(2.21): components of the extension operator `E` from equation (1.5). -/
@[proof_obligation]
theorem ccy23_extension_operator_components
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form)
    (hCoordinates : data.hasEllipsoidMetricAndVolumeIdentities) :
    ∀ field, data.hasExtensionOperatorComponents field := by
  sorry

/-- Equation (2.22): Cartan's formula for `L_Y v`. -/
@[proof_obligation]
theorem ccy23_equation_2_22_radial_lie_derivative
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form) :
    ∀ field, data.hasRadialLieDerivativeComponents field := by
  sorry

/-- Equation (2.23): the remaining latitude-direction correction. -/
@[proof_obligation]
theorem ccy23_equation_2_23_latitude_correction
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form)
    (hCoordinates : data.hasEllipsoidMetricAndVolumeIdentities) :
    ∀ field, data.hasLatitudeCorrectionComponent field := by
  sorry

/-- Section 2.5, equations (2.24)--(2.27): equality of the `dphi` coefficients. -/
@[proof_obligation]
theorem ccy23_dphi_component_comparison
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form) :
    ∀ field,
      data.hasAmbientHodgeComponentFormula field →
      data.hasIntrinsicHodgeComponentFormula field →
      data.hasExtensionOperatorComponents field →
      data.hasRadialLieDerivativeComponents field →
      data.hasLatitudeCorrectionComponent field →
        data.dPhiComponentsAgree field := by
  sorry

/-- Section 2.5: the analogous `dtheta` coefficient calculation. -/
@[proof_obligation]
theorem ccy23_dtheta_component_comparison
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form) :
    ∀ field,
      data.hasAmbientHodgeComponentFormula field →
      data.hasIntrinsicHodgeComponentFormula field →
      data.hasExtensionOperatorComponents field →
      data.hasRadialLieDerivativeComponents field →
        data.dThetaComponentsAgree field := by
  sorry

/-- Recombining the two coordinate coefficients gives the invariant formula (1.4). -/
@[proof_obligation]
theorem ccy23_recombine_components_as_invariant_formula
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form) :
    0 < data.axisScale →
    (∀ field, data.dPhiComponentsAgree field) →
    (∀ field, data.dThetaComponentsAgree field) →
      ccy23InvariantRestrictionStatement data := by
  sorry

/-- CCY23 Theorem 1.1, assembled in the coordinate-comparison order of Section 2. -/
@[literature_terminal]
theorem ccy23_theorem_1_1
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form) :
    ccy23InvariantRestrictionStatement data := by
  intro ha
  have hCoordinates := ccy23_ellipsoid_coordinate_geometry data ha
  have hAmbient := ccy23_ambient_hodge_components data hCoordinates
  have hIntrinsic := ccy23_intrinsic_hodge_components data hCoordinates
  have hExtension := ccy23_extension_operator_components data hCoordinates
  have hLie := ccy23_equation_2_22_radial_lie_derivative data
  have hLatitude := ccy23_equation_2_23_latitude_correction data hCoordinates
  have hPhi := fun field => ccy23_dphi_component_comparison data field
    (hAmbient field) (hIntrinsic field) (hExtension field) (hLie field) (hLatitude field)
  have hTheta := fun field => ccy23_dtheta_component_comparison data field
    (hAmbient field) (hIntrinsic field) (hExtension field) (hLie field)
  exact (ccy23_recombine_components_as_invariant_formula data ha hPhi hTheta) ha


end RiemannianFluids
