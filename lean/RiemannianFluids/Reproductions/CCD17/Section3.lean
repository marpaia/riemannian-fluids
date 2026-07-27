import RiemannianFluids.Reproductions.CCD17.Statements

/-! # CCD17 Section 3: energy counterexamples -/

namespace RiemannianFluids

/-- The hyperbolic plane has a nonzero square-integrable harmonic gradient used in all three counterexamples. -/
@[proof_obligation]
theorem ccd17_nonzero_l2_harmonic_gradient
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.isNonzeroL2HarmonicGradient a (data.witnessVelocity 1) := by
  sorry

/-- Equation (3.12): the explicit time-power velocity built from a harmonic gradient. -/
@[proof_obligation]
theorem ccd17_equation_3_12_velocity_witness
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a) :
    data.hasWitnessFormula3_12 T := by
  have hHarmonic := ccd17_nonzero_l2_harmonic_gradient data a ha hGeometry
  sorry

/-- Equation (3.13): choose the external force so the time-power field solves Hodge--Stokes. -/
@[proof_obligation]
theorem ccd17_equation_3_13_forcing_witness
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a)
    (hVelocity : data.hasWitnessFormula3_12 T) :
    data.hasForcingFormula3_13 T ∧
      data.satisfiesHodgeStokes T (data.witnessVelocity T) (data.witnessForce T) := by
  sorry

/-- Equation (3.14): exact scaling of the witness velocity norm. -/
@[proof_obligation]
theorem ccd17_equation_3_14_velocity_norm
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a) :
    data.hasVelocityNormFormula3_14 T := by
  sorry

/-- Equation (3.15): exact scaling of the dissipation integral. -/
@[proof_obligation]
theorem ccd17_equation_3_15_dissipation
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a)
    (hNorm : data.hasVelocityNormFormula3_14 T) :
    data.hasDissipationFormula3_15 a T := by
  sorry

/-- Equation (3.16): the dual norm of the chosen force has the stated time scaling. -/
@[proof_obligation]
theorem ccd17_equation_3_16_forcing_bound
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a) :
    data.hasForcingBound3_16 T := by
  sorry

/-- Equation (3.17): the different powers of `T` contradict every positive absolute constant. -/
@[proof_obligation]
theorem ccd17_equation_3_17_large_time_contradiction
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a constant : ℝ) (ha : 0 < a) (hConstant : 0 < constant)
    (hGeometry : data.isHyperbolicPlane a) :
    ∃ T : ℝ, 0 < T ∧ data.hasContradiction3_17 constant T ∧
      constant * data.dataRightHandSide T
          (data.witnessVelocity T) (data.witnessForce T) <
        data.energyLeftHandSide T (data.witnessVelocity T) := by
  have hScalings : ∀ T, 0 < T →
      data.hasVelocityNormFormula3_14 T ∧
        data.hasDissipationFormula3_15 a T ∧ data.hasForcingBound3_16 T := by
    intro T hT
    have hNorm := ccd17_equation_3_14_velocity_norm data a T ha hT hGeometry
    exact ⟨hNorm,
      ccd17_equation_3_15_dissipation data a T ha hT hGeometry hNorm,
      ccd17_equation_3_16_forcing_bound data a T ha hT hGeometry⟩
  sorry

/-- CCD17 Theorem 3.2, assembled from the explicit witness and its large-time scalings. -/
@[literature_terminal]
theorem ccd17_theorem_3_2
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force) :
    ccd17HyperbolicEnergyObstructionStatement data := by
  intro a ha hGeometry constant hConstant
  obtain ⟨T, hT, hContradiction, hFailure⟩ :=
    ccd17_equation_3_17_large_time_contradiction data a constant ha hConstant hGeometry
  have hVelocity := ccd17_equation_3_12_velocity_witness data a T ha hT hGeometry
  have hForce := ccd17_equation_3_13_forcing_witness data a T ha hT hGeometry hVelocity
  exact ⟨T, hT, hForce.2, hFailure⟩

/-- Equation (3.19): the convective term of the harmonic-gradient witness is absorbed into pressure. -/
@[proof_obligation]
theorem ccd17_equation_3_19_nonlinear_pressure
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a)
    (hStokes : data.satisfiesHodgeStokes T (data.witnessVelocity T) (data.witnessForce T)) :
    data.pressureFormula3_19 T ∧
      data.satisfiesClassicalHodgeNavierStokes T
        (data.witnessVelocity T) (data.witnessForce T) := by
  sorry

@[literature_terminal]
theorem ccd17_theorem_3_3
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force) :
    ccd17HyperbolicNavierStokesEnergyObstructionStatement data := by
  intro a ha hGeometry constant hConstant
  obtain ⟨T, hT, hContradiction, hFailure⟩ :=
    ccd17_equation_3_17_large_time_contradiction data a constant ha hConstant hGeometry
  have hVelocity := ccd17_equation_3_12_velocity_witness data a T ha hT hGeometry
  have hStokes :=
    (ccd17_equation_3_13_forcing_witness data a T ha hT hGeometry hVelocity).2
  have hPressure := ccd17_equation_3_19_nonlinear_pressure data a T ha hT hGeometry hStokes
  exact ⟨T, hT, hPressure.2, hFailure⟩

/-- Theorem 3.6: substituting (3.12)--(3.13) into (3.23) forces a nonzero velocity to vanish. -/
@[proof_obligation]
theorem ccd17_equation_3_23_energy_equality_contradiction
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force)
    (a T : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hGeometry : data.isHyperbolicPlane a) :
    data.energyEquality3_23WouldForceZero T := by
  sorry

@[literature_terminal]
theorem ccd17_theorem_3_6
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force) :
    ccd17HyperbolicEnergyEqualityObstructionStatement data := by
  intro a ha hGeometry
  have hVelocity :=
    ccd17_equation_3_12_velocity_witness data a 1 ha (by norm_num) hGeometry
  have hStokes :=
    (ccd17_equation_3_13_forcing_witness data a 1 ha (by norm_num) hGeometry hVelocity).2
  exact ⟨1, by norm_num, hStokes,
    ccd17_equation_3_23_energy_equality_contradiction data a 1 ha (by norm_num) hGeometry⟩


end RiemannianFluids
