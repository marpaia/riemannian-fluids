import RiemannianFluids.Reproductions.CC13.Section2

/-! # CC13 Section 3: exponential gradient decay -/

namespace RiemannianFluids

/-- Proposition 3.1: the harmonic extension of nonconstant `C1` boundary data has exponential gradient decay. -/
@[proof_obligation]
theorem cc13_proposition_3_1_gradient_decay
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (hGradientEstimate : data.hasChengYauGradientEstimate a)
    (hJacobiComparison : data.hasJacobiFieldComparison a) :
    data.isBoundedNonconstantHarmonic a (data.seedPotential a) ∧
      data.hasExponentialGradientDecay a (data.seedPotential a) := by
  sorry

/-- Corollary 3.3: on the hyperbolic plane, sufficiently fast gradient decay gives an `L²` harmonic gradient. -/
@[proof_obligation]
theorem cc13_corollary_3_3_l2_gradient
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential)
    (a : ℝ) (ha : 0 < a) (hGeometry : data.isHyperbolicPlane a)
    (hDecay : data.hasExponentialGradientDecay a (data.seedPotential a)) :
    data.harmonicGradientHasFiniteEnergy a (data.seedPotential a) := by
  sorry


end RiemannianFluids
