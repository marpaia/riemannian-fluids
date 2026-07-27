import RiemannianFluids.Reproductions.CC13.Section5

/-! # CC13 Section 6: construction of the nonunique solutions -/

namespace RiemannianFluids

/-- Lemma 6.1: `nabla_(nabla F) dF = (1/2) d |dF|^2`. -/
@[proof_obligation]
theorem cc13_lemma_6_1_convective_gradient_identity
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (potential : Potential) :
    data.hasConvectiveGradientIdentity a potential := by
  sorry

/-- Equation (6.5): the harmonic-gradient ansatz and its explicit pressure satisfy the weak momentum equation. -/
@[proof_obligation]
theorem cc13_equation_6_5_weak_momentum
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (potential : Potential)
    (hPotential : data.isBoundedNonconstantHarmonic a potential)
    (hConvective : data.hasConvectiveGradientIdentity a potential) :
    ∀ parameter,
      (data.lerayHopf a).satisfiesWeakEquation
        (data.solutionFromPotential a potential parameter) := by
  sorry

/-- Equation (6.6): the scalar amplitude family satisfies the admissibility inequality used by the energy estimate. -/
@[proof_obligation]
theorem cc13_equation_6_6_amplitude_family
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) :
    ∀ parameter, data.amplitudeSolvesEquation6_6 a parameter := by
  sorry

/-- Section 6.1: equation (6.6) and Corollary 5.3 give the Leray--Hopf energy inequality. -/
@[proof_obligation]
theorem cc13_section_6_1_energy_inequality
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (potential : Potential)
    (hFiniteEnergy : data.harmonicGradientHasFiniteEnergy a potential)
    (hDeformation : data.deformationControlledByCovariantDerivative a potential)
    (hDissipation : data.hasExactHyperbolicDissipationIdentity a potential) :
    ∀ parameter,
      data.amplitudeSolvesEquation6_6 a parameter →
        (data.lerayHopf a).satisfiesEnergyInequality
          (data.solutionFromPotential a potential parameter) := by
  sorry

/-- Section 6.1: the harmonic gradient is admissible as the common initial datum. -/
@[proof_obligation]
theorem cc13_harmonic_gradient_initial_is_admissible
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (potential : Potential)
    (hFiniteEnergy : data.harmonicGradientHasFiniteEnergy a potential) :
    (data.lerayHopf a).isAdmissibleInitial (data.initialFromPotential a potential) := by
  sorry

/-- Section 6.1: every amplitude in the family has the same initial trace. -/
@[proof_obligation]
theorem cc13_parametrized_ansatz_has_initial_trace
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (potential : Potential) :
    ∀ parameter,
      (data.lerayHopf a).hasInitialTrace
        (data.solutionFromPotential a potential parameter)
        (data.initialFromPotential a potential) := by
  sorry

/-- The harmonic seed and its dissipation identity, assembled through the source chain in Sections 3--5. -/
@[proof_assembly]
theorem cc13_harmonic_seed_exists
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    ∃ potential,
      data.isBoundedNonconstantHarmonic a potential ∧
        data.harmonicGradientHasFiniteEnergy a potential ∧
        data.hasExactHyperbolicDissipationIdentity a potential := by
  have hDecay := cc13_proposition_3_1_gradient_decay data a ha hGeometry
    (cc13_theorem_2_5_gradient_estimate data a ha hGeometry)
    (cc13_theorem_2_7_jacobi_comparison data a ha hGeometry)
  have hGradientL2 := cc13_corollary_3_3_l2_gradient data a ha hGeometry hDecay.2
  have hCover := cc13_lemma_4_1_covering data a ha hGeometry
  have hL1 := cc13_proposition_4_3_gradient_energy_derivative_l1 data a ha hGeometry
    hCover hGradientL2
  have hBochner := cc13_proposition_5_2_bochner_dissipation data a ha hGeometry hL1
  have hDissipation :=
    cc13_corollary_5_3_exact_hyperbolic_dissipation data a ha hGeometry hBochner.1
  exact ⟨data.seedPotential a, hDecay.1, hGradientL2, hDissipation⟩

/-- Theorem 1.2's one-parameter family, assembled from the estimates and equations in Sections 4--6. -/
@[proof_assembly]
theorem cc13_parametrized_solution_is_leray_hopf
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (potential : Potential)
    (hPotential : data.isBoundedNonconstantHarmonic a potential)
    (hFiniteEnergy : data.harmonicGradientHasFiniteEnergy a potential)
    (hDissipation : data.hasExactHyperbolicDissipationIdentity a potential) :
    ∀ parameter : ℝ,
      IsLerayHopfSolution
        (data.lerayHopf a)
        (data.initialFromPotential a potential)
        (data.solutionFromPotential a potential parameter) := by
  have hConvective := cc13_lemma_6_1_convective_gradient_identity data a potential
  have hMomentum := cc13_equation_6_5_weak_momentum data a ha hGeometry potential
    hPotential hConvective
  have hAmplitude := cc13_equation_6_6_amplitude_family data a ha
  have hDeformation := cc13_lemma_5_1_deformation_bound data a potential
  have hEnergy := cc13_section_6_1_energy_inequality data a ha hGeometry potential
    hFiniteEnergy hDeformation hDissipation
  have hInitial := cc13_harmonic_gradient_initial_is_admissible data a potential hFiniteEnergy
  have hTrace := cc13_parametrized_ansatz_has_initial_trace data a potential
  intro parameter
  exact ⟨hInitial, hTrace parameter, hMomentum parameter,
    hEnergy parameter (hAmplitude parameter)⟩

/-- Distinct admissible amplitudes produce different velocity trajectories because the seed is nonconstant. -/
@[proof_obligation]
theorem cc13_two_parameters_give_distinct_solutions
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (potential : Potential)
    (hPotential : data.isBoundedNonconstantHarmonic a potential) :
    data.solutionFromPotential a potential 0 ≠
      data.solutionFromPotential a potential 1 := by
  sorry


end RiemannianFluids
