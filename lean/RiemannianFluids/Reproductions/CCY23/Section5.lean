import RiemannianFluids.Reproductions.CCY23.Section4

/-! # CCY23 Section 5: eccentricity expansion -/

namespace RiemannianFluids

/-- Equation (5.2): rewrite `a` and `lambda` in terms of the eccentricity `mu`. -/
@[proof_obligation]
theorem ccy23_equation_5_2_eccentricity_identities
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form) :
    data.hasEccentricityIdentities5_2 := by
  sorry

/-- Equation (5.3): the uniform geometric series for `(1 - mu² sin² phi)⁻¹`. -/
@[proof_obligation]
theorem ccy23_equation_5_3_geometric_series
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form)
    (hEccentricity : data.hasEccentricityIdentities5_2) :
    data.hasGeometricSeries5_3 := by
  sorry

/-- Equation (5.4): differentiate the geometric series to obtain the squared-denominator series. -/
@[proof_obligation]
theorem ccy23_equation_5_4_squared_denominator_series
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form)
    (hGeometric : data.hasGeometricSeries5_3) :
    data.hasSquaredDenominatorSeries5_4 := by
  sorry

/-- Equation (5.5): substitute the ellipsoidal data into the two components of the extension operator. -/
@[proof_obligation]
theorem ccy23_equation_5_5_extension_formula
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form)
    (hEccentricity : data.hasEccentricityIdentities5_2) :
    ∀ field, data.hasExtensionFormula5_5 field := by
  sorry

/-- Equation (5.6): expansion of the `dphi` component of `E(v)`. -/
@[proof_obligation]
theorem ccy23_equation_5_6_extension_phi_component
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form)
    (hEccentricity : data.hasEccentricityIdentities5_2)
    (hGeometric : data.hasGeometricSeries5_3)
    (hSquared : data.hasSquaredDenominatorSeries5_4)
    (hFormula : ∀ field, data.hasExtensionFormula5_5 field) :
    ∀ field, data.hasExtensionPhiExpansion5_6 field := by
  sorry

/-- Equation (5.7): expansion of the `dtheta` component of `E(v)`. -/
@[proof_obligation]
theorem ccy23_equation_5_7_extension_theta_component
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form)
    (hEccentricity : data.hasEccentricityIdentities5_2)
    (hGeometric : data.hasGeometricSeries5_3)
    (hSquared : data.hasSquaredDenominatorSeries5_4)
    (hFormula : ∀ field, data.hasExtensionFormula5_5 field) :
    ∀ field, data.hasExtensionThetaExpansion5_7 field := by
  sorry

/-- Equation (5.8): the differential-form eccentricity coefficient. -/
@[proof_obligation]
theorem ccy23_equation_5_8_form_coefficient
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form) :
    ∀ field,
      data.hasExtensionPhiExpansion5_6 field →
      data.hasExtensionThetaExpansion5_7 field →
        data.hasFormCoefficient5_8 field := by
  sorry

/-- Equation (5.9): substitute the two divergence constraints to obtain the vector-component coefficient. -/
@[proof_obligation]
theorem ccy23_equation_5_9_vector_coefficient
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form) :
    ∀ field, data.hasFormCoefficient5_8 field → data.hasVectorCoefficient5_9 field := by
  sorry

/-- Equations (5.8)--(5.9), including the uniform `O(mu^4)` remainder. -/
@[proof_obligation]
theorem ccy23_section_5_exact_eccentricity_expansion
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form)
    (hForm : ∀ field, data.hasFormCoefficient5_8 field)
    (hVector : ∀ field, data.hasVectorCoefficient5_9 field) :
    ccy23EccentricityExpansionStatement data := by
  sorry

@[literature_terminal]
theorem ccy23_equations_5_8_and_5_9
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form) :
    ccy23EccentricityExpansionStatement data := by
  have hEccentricity := ccy23_equation_5_2_eccentricity_identities data
  have hGeometric := ccy23_equation_5_3_geometric_series data hEccentricity
  have hSquared := ccy23_equation_5_4_squared_denominator_series data hGeometric
  have hFormula := ccy23_equation_5_5_extension_formula data hEccentricity
  have hPhiExpansion := ccy23_equation_5_6_extension_phi_component data
    hEccentricity hGeometric hSquared hFormula
  have hThetaExpansion := ccy23_equation_5_7_extension_theta_component data
    hEccentricity hGeometric hSquared hFormula
  have hForm := fun field => ccy23_equation_5_8_form_coefficient data field
    (hPhiExpansion field) (hThetaExpansion field)
  have hVector := fun field => ccy23_equation_5_9_vector_coefficient data field (hForm field)
  exact ccy23_section_5_exact_eccentricity_expansion data hForm hVector


end RiemannianFluids
