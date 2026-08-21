import RiemannianFluids.Geometry.Instances.HyperbolicPlane
import RiemannianFluids.Geometry.Manifolds
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The complete measured hyperbolic plane

This module packages the global analytic geometry underlying the hyperbolic examples.  The carrier
is Mathlib's upper half-plane, its base metric is the genuine Poincaré distance, and its measure is

    dvol = dx dy / y².

The Riemannian fiber metric and Levi--Civita connection were constructed in
`HyperbolicPlane`; the definitions below add the complete metric-measure structure needed by
global `L²` analysis.  No completeness or measurability predicate is introduced: the relevant
Mathlib instances are present on the carrier itself.
-/

namespace RiemannianFluids
namespace HyperbolicPlane

open MeasureTheory
open scoped ENNReal NNReal

/-- The Poincaré volume measure `dx dy / y²` on the upper half-plane. -/
noncomputable abbrev hyperbolicVolume : Measure HyperbolicPlane := volume

/-- The base metric is the genuine hyperbolic distance, not the Euclidean subspace distance. -/
theorem hyperbolic_dist_eq (p q : HyperbolicPlane) :
    dist p q =
      2 * Real.arsinh (dist (p : ℂ) q / (2 * √(p.im * q.im))) :=
  UpperHalfPlane.dist_eq p q

/-- The project-level name unfolds to Mathlib's invariant density `dx dy / y²`. -/
theorem hyperbolicVolume_def :
    (hyperbolicVolume : Measure HyperbolicPlane) =
      (volume.comap ((↑) : HyperbolicPlane → ℂ)).withDensity fun p ↦
        ↑((1 / NNReal.mk p.im p.im_pos.le : ℝ≥0) ^ 2) :=
  UpperHalfPlane.volume_def

/-- A measurable-set formula exposing the weighted Lebesgue measure in the global chart. -/
theorem hyperbolicVolume_eq_lintegral (s : Set HyperbolicPlane) :
    hyperbolicVolume s =
      ∫⁻ z : ℂ in ((↑) : HyperbolicPlane → ℂ) '' s,
        ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) :=
  UpperHalfPlane.volume_eq_lintegral s

/-- Hyperbolic volume has full topological support: every nonempty open subset of the upper
half-plane has positive volume.  This is the measure-theoretic fact that makes the inclusion of
continuous compactly supported fields into `L²` injective, so a smooth core element can be
recovered uniquely from its almost-everywhere equivalence class. -/
noncomputable instance hyperbolicVolume_isOpenPosMeasure :
    (hyperbolicVolume : Measure HyperbolicPlane).IsOpenPosMeasure := by
  rw [hyperbolicVolume_def]
  letI : (volume.comap ((↑) : HyperbolicPlane → ℂ)).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume UpperHalfPlane.isOpenEmbedding_coe
  have hdensity : Continuous (fun z : HyperbolicPlane ↦
      (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
    refine .pow (.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z ↦ NNReal.ne_iff.mp z.im_ne_zero
  exact (withDensity_absolutelyContinuous'
    ((ENNReal.continuous_coe.comp hdensity).aemeasurable)
    (by
      filter_upwards with z
      change (↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) : ℝ≥0∞) ≠ 0
      apply ENNReal.coe_ne_zero.mpr
      apply pow_ne_zero
      apply div_ne_zero one_ne_zero
      exact (show (0 : ℝ≥0) < NNReal.mk z.im z.im_pos.le by exact z.im_pos).ne')
    ).isOpenPosMeasure

/-- The existing Poincaré Riemannian geometry together with the complete hyperbolic base metric.

The `CompleteSpace` field is synthesized from Mathlib's `ProperSpace HyperbolicPlane` theorem;
the Riemannian-bundle field is the explicit Poincaré metric constructed by this project. -/
noncomputable def completeRiemannianManifold :
    CompleteBoundarylessRiemannianManifoldData where
  E := ℂ
  H := ℂ
  I := modelWithCornersSelf ℝ ℂ
  M := HyperbolicPlane

/-- The complete Riemannian package really has the canonical upper half-plane as its carrier. -/
@[simp] theorem completeRiemannianManifold_M :
    completeRiemannianManifold.M = HyperbolicPlane :=
  rfl

end HyperbolicPlane
end RiemannianFluids
