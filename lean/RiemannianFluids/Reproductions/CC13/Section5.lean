import RiemannianFluids.Reproductions.CC13.Section4

/-! # CC13 Section 5: finite dissipation -/

namespace RiemannianFluids


/-- Lemma 5.1: pointwise deformation energy is controlled by the full covariant derivative. -/
@[proof_obligation]
theorem cc13_lemma_5_1_deformation_bound
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (potential : Potential) :
    data.deformationControlledByCovariantDerivative a potential := by
  sorry

/-- Proposition 5.2: cutoff integration gives the Bochner/deformation dissipation relation. -/
@[proof_obligation]
theorem cc13_proposition_5_2_bochner_dissipation
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (hL1 : data.gradientEnergyDerivativeIsL1 a (data.seedPotential a)) :
    data.hasBochnerDissipationIdentity a (data.seedPotential a) ∧
      data.hessianHasFiniteEnergy a (data.seedPotential a) := by
  have hBochner := cc13_lemma_2_6_bochner_formula data a ha hGeometry
  sorry

/-- Corollary 5.3: the constant-curvature specialization gives the exact `H2` dissipation identity. -/
@[proof_obligation]
theorem cc13_corollary_5_3_exact_hyperbolic_dissipation
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (hBochner : data.hasBochnerDissipationIdentity a (data.seedPotential a)) :
    data.hasExactHyperbolicDissipationIdentity a (data.seedPotential a) := by
  sorry


end RiemannianFluids
