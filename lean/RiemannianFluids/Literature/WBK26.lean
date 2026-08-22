import RiemannianFluids.PDE.EnergyDecay
import RiemannianFluids.PDE.WeakNavierStokes
import RiemannianFluids.Geometry.BoundedGeometry
import RiemannianFluids.Operators.Viscosity
import RiemannianFluids.Viscosity.IntrinsicStrain

/-!
# WBK26: intrinsic strain and negatively curved fluids

This module separates the proved kinematic identity and conditional Gronwall fragment from the
four proposition-valued source signatures of the paper's global weak-solution theorem.  The
signatures fix the target without postulating any of the open PDE conclusions.
-/

namespace RiemannianFluids.Literature.WBK26

open Bundle Set
open scoped ContDiff Manifold

/-- Shared source data for the four conclusions of WBK26 Theorem 6.1.  `H` and `V` are forced
to be closures of the same smooth compactly supported solenoidal core, while the weak framework
keeps the equation, trace, incompressibility, and Bochner memberships separately visible. -/
structure NegativeCurvatureWeakData
    (Point SmoothField H V Pressure Trajectory : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  geometry : CompleteBoundedSurfaceProfile Point
  solenoidalClosures : SolenoidalClosureData SmoothField H V
  framework : WeakNavierStokesFramework H V Pressure Trajectory
  viscosityModel : ViscosityModel
  isSpaceTimePressureDistribution : ℝ → Pressure → Prop

/-- Source signature for the global weak-existence conclusion of WBK26 Theorem 6.1. -/
def negative_curvature_global_weak_existence_statement
    {Point SmoothField H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (data : NegativeCurvatureWeakData Point SmoothField H V Pressure Trajectory)
    (μ κ : ℝ) : Prop :=
  SatisfiesWBK26Geometry data.geometry κ →
    data.viscosityModel = ViscosityModel.deformation →
      0 < μ → ∀ initial terminalTime, 0 < terminalTime →
        ∃ velocity,
          IsWeakNavierStokesSolutionOn data.framework μ terminalTime initial velocity

/-- Source signature for velocity uniqueness in the weak class of Theorem 6.1. -/
def negative_curvature_weak_uniqueness_statement
    {Point SmoothField H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (data : NegativeCurvatureWeakData Point SmoothField H V Pressure Trajectory)
    (μ κ : ℝ) : Prop :=
  SatisfiesWBK26Geometry data.geometry κ →
    data.viscosityModel = ViscosityModel.deformation →
      0 < μ → ∀ initial terminalTime velocity, 0 < terminalTime →
        IsWeakNavierStokesSolutionOn data.framework μ terminalTime initial velocity →
          IsUniqueWeakNavierStokesSolutionOn
            data.framework μ terminalTime initial velocity

/-- Source signature for recovery of a spacetime pressure distribution in Theorem 6.1. -/
def negative_curvature_pressure_recovery_statement
    {Point SmoothField H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (data : NegativeCurvatureWeakData Point SmoothField H V Pressure Trajectory)
    (μ κ : ℝ) : Prop :=
  SatisfiesWBK26Geometry data.geometry κ →
    data.viscosityModel = ViscosityModel.deformation →
      0 < μ → ∀ initial terminalTime velocity, 0 < terminalTime →
        IsWeakNavierStokesSolutionOn data.framework μ terminalTime initial velocity →
          ∃ pressure,
            data.isSpaceTimePressureDistribution terminalTime pressure ∧
              data.framework.pressureRecoversMomentumOn
                μ terminalTime velocity pressure

/-- Full source signature for equation (40), attached to every weak solution from the theorem. -/
def negative_curvature_exponential_decay_statement
    {Point SmoothField H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (data : NegativeCurvatureWeakData Point SmoothField H V Pressure Trajectory)
    (μ κ : ℝ) : Prop :=
  SatisfiesWBK26Geometry data.geometry κ →
    data.viscosityModel = ViscosityModel.deformation →
      0 < μ → ∀ initial terminalTime velocity, 0 < terminalTime →
        IsWeakNavierStokesSolutionOn data.framework μ terminalTime initial velocity →
          ∀ time ∈ Set.Icc (0 : ℝ) terminalTime,
            ‖data.framework.velocityAt velocity time‖ ^ 2 ≤
              Real.exp (-2 * μ * κ ^ 2 * time) * ‖initial‖ ^ 2

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

/-- WBK26 equations (20)--(24) on an actual material trajectory.  The first conjunct proves the
manifold differential of the inner product along the integral curve; the second identifies its
directional material rate with twice the deformation tensor using the Lie-drag conditions. -/
theorem material_inner_product_rate_eq_twice_deformation
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    {x : M} (data : MaterialConnectingPairJetAt I field x) :
    HasMFDerivAt%
        (materialInnerProduct I data.trajectory data.first data.second) (0 : ℝ)
        ((mfderiv I (modelWithCornersSelf ℝ ℝ)
            (fun y ↦ inner ℝ (data.first y) (data.second y)) x).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (field x))) ∧
      materialMetricRateAt I field data.first data.second x =
        2 * deformationTensor I regularity connection smooth field x
          (data.first x) (data.second x) := by
  exact ⟨data.hasMFDerivAt_materialInnerProduct,
    MaterialConnectingPairJetAt.materialMetricRate_eq_two_deformationTensor
      I regularity connection smooth field data⟩

/-- Exponential decay from an assumed energy identity and coercive dissipation estimate. -/
abbrev exponential_decay_of_energy_identity_and_coercivity
    {energy dissipation : ℝ → ℝ} {μ κ T : ℝ} :=
  _root_.RiemannianFluids.energy_exponential_decay_of_coercive_dissipation
    (energy := energy) (dissipation := dissipation) (μ := μ) (κ := κ) (T := T)

end RiemannianFluids.Literature.WBK26
