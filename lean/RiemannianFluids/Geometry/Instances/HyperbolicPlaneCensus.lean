import RiemannianFluids.Geometry.Instances.HyperbolicPlane
import RiemannianFluids.Viscosity.CurvatureComparison

/-!
# The intrinsic viscosity census on the hyperbolic plane

The horizontal coordinate field on the Poincaré half-plane is divergence-free, while its
Ricci pairing with the horizontal test vector is nonzero. The constructed comparison identities
therefore distinguish the rough, Hodge, and deformation operator tests at every point.
-/

namespace RiemannianFluids.HyperbolicPlane

open scoped ContDiff Manifold

/-- At every point of the Poincaré half-plane, the constructed rough, Hodge, and deformation
operator tests on the horizontal field are pairwise distinct. -/
theorem cz24_census_hyperbolic_tested (p : HyperbolicPlane) :
    ConstructedCandidateTestsPairwiseDistinct 𝓘(ℝ, ℂ)
      hyperbolicLeviCivitaConnection p (hyperbolic_hasCurvatureRegularity p)
      (horizontalField 2) (horizontalField 2).contMDiff.contMDiffAt
      (constantField 1 p) := by
  apply constructedCandidateTests_pairwiseDistinct_of_ricciWitness
  · intro q
    change tangentTrace 𝓘(ℝ, ℂ) q
      (hyperbolicCovariantDerivative (constantField 1) q) = 0
    exact horizontalField_divergence_pointwise q
  · change connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) (constantField 1 p) (constantField 1 p) ≠ 0
    rw [ricciForm_horizontal]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (im_ne_zero p)))

/-- At every point of the Poincaré half-plane, the actual tangent-vector outputs of the
constructed rough, Hodge, and deformation operators on the horizontal field are pairwise
distinct.  No geometric or comparison hypotheses are supplied by the caller. -/
theorem cz24_census_hyperbolic (p : HyperbolicPlane) :
    ConstructedCandidateOutputsPairwiseDistinct 𝓘(ℝ, ℂ)
      hyperbolicLeviCivitaConnection p (hyperbolic_hasCurvatureRegularity p)
      (horizontalField 2) (horizontalField 2).contMDiff.contMDiffAt := by
  apply constructedCandidateOutputs_pairwiseDistinct_of_ricciWitness
  · intro q
    change tangentTrace 𝓘(ℝ, ℂ) q
      (hyperbolicCovariantDerivative (constantField 1) q) = 0
    exact horizontalField_divergence_pointwise q
  · change connectionRicciFormAt 𝓘(ℝ, ℂ) hyperbolicCovariantDerivative p
      (hyperbolic_hasCurvatureRegularity p) (constantField 1 p) (constantField 1 p) ≠ 0
    rw [ricciForm_horizontal]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (im_ne_zero p)))

end RiemannianFluids.HyperbolicPlane
