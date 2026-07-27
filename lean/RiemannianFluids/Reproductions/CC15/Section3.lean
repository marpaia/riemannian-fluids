import RiemannianFluids.Reproductions.CC15.Section2

/-! # CC15 Section 3: proof of the Liouville theorem -/

namespace RiemannianFluids

/-- CC15 equation (3.3): Theorem 2.5 supplies compactly supported solenoidal `H¹` approximants when `N ≥ 3`. -/
@[proof_assembly]
theorem cc15_equation_3_3_solenoidal_approximation
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hH10 : data.liesInH10 velocity)
    (hCurrentCriterion : data.hasCurrentCriterion)
    (hDimension : 3 ≤ N) :
    data.liesInSolenoidalH1Closure velocity := by
  exact (cc15_theorem_2_5_solenoidal_h1_decomposition data N a velocity hN ha
    hGeometry hDivergenceFree hH10 hCurrentCriterion).1 hDimension

/-- CC15 equation (3.4): every compactly supported co-closed approximant kills the pressure term. -/
@[proof_obligation]
theorem cc15_equation_3_4_pressure_cancellation
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (pressure : Pressure)
    (hSmoothPressure : data.isSmoothPressure pressure) :
    data.pressureCancelsAgainstSolenoidalCore pressure := by
  sorry

/-- CC15 equation (3.5): test the stationary equation against the source's sequence from (3.3). -/
@[proof_obligation]
theorem cc15_equation_3_5_tested_momentum
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity) (pressure : Pressure)
    (hN : 3 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hEquation : data.satisfiesStationaryDeformationNS N a velocity pressure)
    (hSolenoidalClosure : data.liesInSolenoidalH1Closure velocity)
    (hPressure : data.pressureCancelsAgainstSolenoidalCore pressure)
    (hDivergenceFree : data.isDivergenceFree velocity) :
    data.hasTestedMomentumEquation velocity := by
  sorry

/-- CC15 equation (3.6): interpolation bounds the nonlinear error along the `H¹` approximants. -/
@[proof_obligation]
theorem cc15_equation_3_6_nonlinear_estimate
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (velocity : Velocity)
    (hN : 3 ≤ N)
    (hSolenoidalClosure : data.liesInSolenoidalH1Closure velocity)
    (hInterpolation : data.hasDimensionInterpolation N velocity) :
    data.hasNonlinearEstimateEquation3_6 velocity := by
  sorry

/-- CC15 equation (3.7): the estimate (3.6) and `H¹` convergence make the nonlinear error vanish. -/
@[proof_obligation]
theorem cc15_equation_3_7_nonlinear_limit
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (velocity : Velocity)
    (hEstimate : data.hasNonlinearEstimateEquation3_6 velocity) :
    data.nonlinearTermPassesToVelocityTest velocity := by
  sorry

/-- CC15 equation (3.8): pass (3.5) to the velocity limit. -/
@[proof_obligation]
theorem cc15_equation_3_8_velocity_test_identity
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (velocity : Velocity)
    (hMomentum : data.hasTestedMomentumEquation velocity)
    (hNonlinearLimit : data.nonlinearTermPassesToVelocityTest velocity) :
    data.hasVelocityTestEnergyIdentity velocity := by
  sorry

/-- CC15 equation (3.9): divergence-free integration by parts cancels the velocity cubic term. -/
@[proof_obligation]
theorem cc15_equation_3_9_convection_cancellation
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (velocity : Velocity)
    (hInterpolation : data.hasDimensionInterpolation N velocity)
    (hDivergenceFree : data.isDivergenceFree velocity) :
    data.hasConvectionCancellation velocity := by
  sorry

/-- CC15 equation (3.10): equations (3.8)--(3.9) leave zero deformation energy. -/
@[proof_obligation]
theorem cc15_equation_3_10_zero_deformation_energy
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (velocity : Velocity)
    (hEnergyIdentity : data.hasVelocityTestEnergyIdentity velocity)
    (hCancellation : data.hasConvectionCancellation velocity) :
    data.hasZeroDeformationEnergy velocity := by
  sorry

/-- CC15 equation (3.11): Lemma 2.2 turns zero deformation energy into vanishing. -/
@[proof_obligation]
theorem cc15_equation_3_11_deformation_gap_forces_zero
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 3 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hIdentity : data.hasDeformationIdentity N a velocity)
    (hZeroEnergy : data.hasZeroDeformationEnergy velocity) :
    data.isZero velocity := by
  sorry

/-- CC15 equation (3.12): exterior differentiation of momentum gives the scalar vorticity equation. -/
@[proof_obligation]
theorem cc15_equation_3_12_vorticity
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (a : ℝ) (velocity : Velocity) (pressure : Pressure)
    (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace 2 a)
    (hEquation : data.satisfiesStationaryDeformationNS 2 a velocity pressure)
    (hDivergenceFree : data.isDivergenceFree velocity) :
    data.hasVorticityEquation a velocity := by
  sorry

/-- CC15 equation (3.13): cutoff testing and the `L-infinity` bound force zero vorticity. -/
@[proof_obligation]
theorem cc15_equation_3_13_zero_vorticity
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (a : ℝ) (velocity : Velocity)
    (ha : 0 < a)
    (hVorticity : data.hasVorticityEquation a velocity)
    (hL2 : data.exteriorDerivativeIsL2 velocity)
    (hBounded : data.isEssentiallyBounded velocity) :
    data.hasZeroVorticity velocity := by
  sorry

/-- CC15 Section 3, Case 2 after (3.13): on the simply connected plane, closed and co-closed gives a harmonic gradient. -/
@[proof_obligation]
theorem cc15_section_3_case_2_harmonic_gradient
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (a : ℝ) (velocity : Velocity)
    (hGeometry : data.isHyperbolicSpace 2 a)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hZeroVorticity : data.hasZeroVorticity velocity)
    (hL2 : data.isSquareIntegrable velocity) :
    ∃ potential,
      data.isHarmonicPotential 2 a potential ∧
        data.isGradientOf velocity potential ∧
        data.isSquareIntegrable velocity := by
  sorry

/-- CC15 Theorem 1.1, dimensions three and four, assembled from paper Lemmas 2.1--2.3 and Theorem 2.5. -/
@[proof_assembly]
theorem cc15_vanishing_in_dimensions_three_and_four
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity) (pressure : Pressure)
    (hDimension : N = 3 ∨ N = 4) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hSmoothVelocity : data.isSmoothVelocity velocity)
    (hSmoothPressure : data.isSmoothPressure pressure)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hEquation : data.satisfiesStationaryDeformationNS N a velocity pressure)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity) :
    data.isZero velocity := by
  have hN : 2 ≤ N := by omega
  obtain ⟨_, _, hL2, hH10⟩ :=
    cc15_lemma_2_1_from_dirichlet_to_l2 data N a velocity hN ha hGeometry
      hSmoothVelocity hDirichlet
  have hIdentity :=
    cc15_lemma_2_2_deformation_identity data N a velocity hN ha hGeometry
      hSmoothVelocity hDirichlet
  have hInterpolation :=
    cc15_lemma_2_3_interpolation data N velocity hN hL2 hDirichlet (by omega)
  have hCurrentCriterion := cc15_lemma_2_4_current_criterion data
  have hClosure :=
    cc15_equation_3_3_solenoidal_approximation data N a velocity hN ha hGeometry
      hDivergenceFree hH10 hCurrentCriterion (by omega)
  have hPressure :=
    cc15_equation_3_4_pressure_cancellation data pressure hSmoothPressure
  have hMomentum :=
    cc15_equation_3_5_tested_momentum data N a velocity pressure
      (by omega) ha hGeometry hEquation hClosure hPressure hDivergenceFree
  have hNonlinearEstimate :=
    cc15_equation_3_6_nonlinear_estimate data N velocity (by omega) hClosure hInterpolation
  have hNonlinear := cc15_equation_3_7_nonlinear_limit data velocity hNonlinearEstimate
  have hEnergyIdentity :=
    cc15_equation_3_8_velocity_test_identity data velocity hMomentum hNonlinear
  have hCancellation :=
    cc15_equation_3_9_convection_cancellation data N velocity hInterpolation hDivergenceFree
  have hZeroEnergy :=
    cc15_equation_3_10_zero_deformation_energy data velocity hEnergyIdentity hCancellation
  exact cc15_equation_3_11_deformation_gap_forces_zero data N a velocity (by omega) ha
    hGeometry hIdentity hZeroEnergy

/-- CC15 Theorem 1.1, dimension two, assembled from Lemma 2.1 and equations (3.12)--(3.13). -/
@[proof_assembly]
theorem cc15_harmonic_gradient_in_dimension_two
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (a : ℝ) (velocity : Velocity) (pressure : Pressure)
    (ha : 0 < a) (hGeometry : data.isHyperbolicSpace 2 a)
    (hSmoothVelocity : data.isSmoothVelocity velocity)
    (_hSmoothPressure : data.isSmoothPressure pressure)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hEquation : data.satisfiesStationaryDeformationNS 2 a velocity pressure)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity)
    (hBounded : data.isEssentiallyBounded velocity) :
    ∃ potential,
      data.isHarmonicPotential 2 a potential ∧
        data.isGradientOf velocity potential ∧
        data.isSquareIntegrable velocity := by
  obtain ⟨hExterior, _, hL2, _⟩ :=
    cc15_lemma_2_1_from_dirichlet_to_l2 data 2 a velocity (by omega) ha hGeometry
      hSmoothVelocity hDirichlet
  have hVorticity :=
    cc15_equation_3_12_vorticity data a velocity pressure ha hGeometry hEquation
      hDivergenceFree
  have hZero :=
    cc15_equation_3_13_zero_vorticity data a velocity ha hVorticity hExterior hBounded
  exact cc15_section_3_case_2_harmonic_gradient data a velocity hGeometry
    hDivergenceFree hZero hL2

/-- CC15 Theorem 1.1, dimensions at least five, using the bounded interpolation branch. -/
@[proof_assembly]
theorem cc15_vanishing_in_dimensions_at_least_five
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity) (pressure : Pressure)
    (hDimension : 5 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hSmoothVelocity : data.isSmoothVelocity velocity)
    (hSmoothPressure : data.isSmoothPressure pressure)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hEquation : data.satisfiesStationaryDeformationNS N a velocity pressure)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity)
    (hBounded : data.isEssentiallyBounded velocity) :
    data.isZero velocity := by
  have hN : 2 ≤ N := by omega
  obtain ⟨_, _, hL2, hH10⟩ :=
    cc15_lemma_2_1_from_dirichlet_to_l2 data N a velocity hN ha hGeometry
      hSmoothVelocity hDirichlet
  have hIdentity :=
    cc15_lemma_2_2_deformation_identity data N a velocity hN ha hGeometry
      hSmoothVelocity hDirichlet
  have hInterpolation :=
    cc15_lemma_2_3_interpolation data N velocity hN hL2 hDirichlet (fun _ => hBounded)
  have hCurrentCriterion := cc15_lemma_2_4_current_criterion data
  have hClosure :=
    cc15_equation_3_3_solenoidal_approximation data N a velocity hN ha hGeometry
      hDivergenceFree hH10 hCurrentCriterion (by omega)
  have hPressure :=
    cc15_equation_3_4_pressure_cancellation data pressure hSmoothPressure
  have hMomentum :=
    cc15_equation_3_5_tested_momentum data N a velocity pressure
      (by omega) ha hGeometry hEquation hClosure hPressure hDivergenceFree
  have hNonlinearEstimate :=
    cc15_equation_3_6_nonlinear_estimate data N velocity (by omega) hClosure hInterpolation
  have hNonlinear := cc15_equation_3_7_nonlinear_limit data velocity hNonlinearEstimate
  have hEnergyIdentity :=
    cc15_equation_3_8_velocity_test_identity data velocity hMomentum hNonlinear
  have hCancellation :=
    cc15_equation_3_9_convection_cancellation data N velocity hInterpolation hDivergenceFree
  have hZeroEnergy :=
    cc15_equation_3_10_zero_deformation_energy data velocity hEnergyIdentity hCancellation
  exact cc15_equation_3_11_deformation_gap_forces_zero data N a velocity (by omega) ha
    hGeometry hIdentity hZeroEnergy


end RiemannianFluids
