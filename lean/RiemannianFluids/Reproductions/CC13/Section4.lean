import RiemannianFluids.Reproductions.CC13.Section3

/-! # CC13 Section 4: global integrability -/

namespace RiemannianFluids

/-- Section 4, Lemma 4.1: the bounded-overlap geodesic-ball covering used in the global integral estimates. -/
@[proof_obligation]
theorem cc13_lemma_4_1_covering
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a) :
    data.admitsUniformGeodesicCover a := by
  have hDistance := cc13_lemma_2_2_distance_function data a ha hGeometry
  have hTriangle := cc13_lemma_2_3_triangle_comparison data a ha hGeometry
  sorry

/-- Proposition 4.3: `nabla |nabla F|^2` is globally integrable. -/
@[proof_obligation]
theorem cc13_proposition_4_3_gradient_energy_derivative_l1
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (hCover : data.admitsUniformGeodesicCover a)
    (hGradientL2 : data.harmonicGradientHasFiniteEnergy a (data.seedPotential a)) :
    data.gradientEnergyDerivativeIsL1 a (data.seedPotential a) := by
  have hCaccioppoli := cc13_lemma_2_4_caccioppoli data a ha hGeometry
  have hBochner := cc13_lemma_2_6_bochner_formula data a ha hGeometry
  sorry

end RiemannianFluids
