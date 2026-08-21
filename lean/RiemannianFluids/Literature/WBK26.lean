import RiemannianFluids.PDE.EnergyDecay
import RiemannianFluids.Viscosity.IntrinsicStrain

/-!
# WBK26: intrinsic strain and negatively curved fluids

This module separates the proved kinematic identity from the conditional Gronwall fragment of the
paper's global weak-solution theorem.  The latter is deliberately named for its hypotheses rather
than for the full source claim.
-/

namespace RiemannianFluids.Literature.WBK26

open Bundle Set
open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The metric Lie derivative is twice the intrinsic deformation tensor. -/
abbrev metric_rate_eq_twice_deformation
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    {X Y : (y : M) → TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :=
  _root_.RiemannianFluids.infinitesimalMetricRate_eq_metricLieDerivativeAt I
    regularity connection smooth field hX hY

/-- Exponential decay from an assumed energy identity and coercive dissipation estimate. -/
abbrev exponential_decay_of_energy_identity_and_coercivity
    {energy dissipation : ℝ → ℝ} {μ κ T : ℝ} :=
  _root_.RiemannianFluids.energy_exponential_decay_of_coercive_dissipation
    (energy := energy) (dissipation := dissipation) (μ := μ) (κ := κ) (T := T)

end RiemannianFluids.Literature.WBK26
