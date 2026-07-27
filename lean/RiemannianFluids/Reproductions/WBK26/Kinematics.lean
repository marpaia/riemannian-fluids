import Mathlib.Analysis.SpecialFunctions.Exp
import RiemannianFluids.ProofStatus
import RiemannianFluids.Analysis.ExhaustionCompactness
import RiemannianFluids.Geometry.BoundedGeometry
import RiemannianFluids.PDE.WeakNavierStokes

/-!
# WBK26 Theorem 6.1 blueprint

Source: Wang--Braunstein, *Resolving the viscosity operator ambiguity on Riemannian manifolds via a kinematic selection principle*,
arXiv:2605.17502v2, Theorem 6.1 and equations (39)--(40), with the uniqueness argument continued in Remark 6.2.

The setting is a complete noncompact two-dimensional Riemannian manifold of bounded geometry with `K <= -kappa^2 < 0`. If `H` and `V` are the `L^2`
and `H^1` closures of compactly supported smooth divergence-free fields, then for every `mu > 0`, initial datum `u0 : H`, and finite horizon `T > 0`,
the deformation-viscosity equation has a unique weak velocity in `L^infty(0,T;H) intersection L^2(0,T;V)`. A scalar distribution recovers pressure,
and

    ||u(t)||_L2^2 <= exp (-2 mu kappa^2 t) ||u0||_L2^2.

The declarations below split the paper theorem into proof-sized units: curvature coercivity, the global Ladyzhenskaya estimate, existence by exhaustion
and compactness, pressure recovery, uniqueness, and decay. The final theorem merely assembles those results, so its transitive `sorryAx` dependencies
are an exact progress signal.
-/

namespace RiemannianFluids

/-- Metric-rate and deformation-tensor observables for the kinematic selection principle. -/
structure WBK26LieStrainData (Velocity SymmetricTensor : Type*) where
  metricLieDerivative : Velocity → SymmetricTensor
  deformationTensor : Velocity → SymmetricTensor

/-- The metric rate under the flow is twice the deformation tensor. -/
def wbk26LieStrainStatement
    {Velocity SymmetricTensor : Type*}
    [AddCommGroup SymmetricTensor] [Module ℝ SymmetricTensor]
    (data : WBK26LieStrainData Velocity SymmetricTensor) : Prop :=
  ∀ velocity,
    data.metricLieDerivative velocity = (2 : ℝ) • data.deformationTensor velocity

/-- Section 2, kinematic identity: the material metric rate is the Lie derivative of the metric and equals twice the rate-of-deformation tensor. -/
@[proof_obligation]
theorem wbk26_metric_rate_is_twice_deformation
    {Velocity SymmetricTensor : Type*}
    [AddCommGroup SymmetricTensor] [Module ℝ SymmetricTensor]
    (data : WBK26LieStrainData Velocity SymmetricTensor) :
    ∀ velocity,
      data.metricLieDerivative velocity =
        (2 : ℝ) • data.deformationTensor velocity := by
  sorry

/-- The source-facing kinematic-selection contract, routed through its geometric identity rather than left as an isolated claim definition. -/
@[literature_terminal]
theorem wbk26_lie_strain_selection
    {Velocity SymmetricTensor : Type*}
    [AddCommGroup SymmetricTensor] [Module ℝ SymmetricTensor]
    (data : WBK26LieStrainData Velocity SymmetricTensor) :
    wbk26LieStrainStatement data := by
  exact wbk26_metric_rate_is_twice_deformation data

/-- The concrete objects varied in WBK26 Steps 2--4 for fixed viscosity, horizon, and initial data. -/
structure WBK26ExistenceRoute (Initial Trajectory : Type*) where
  Point : Type
  Domain : Type
  Approximation : Type
  compactness : ExhaustionCompactnessData Point Domain Initial Approximation Trajectory

/--
All semantic data consumed by the WBK26 source statement. This structure contains definitions and observables, never an existence, uniqueness, or
decay conclusion.
-/
structure WBK26Data
    (M H V Pressure Trajectory : Type*)
    [NormedAddCommGroup H] [NormedAddCommGroup V] where
  /-- Complete/bounded/negative surface observables. -/
  geometry : CompleteBoundedSurfaceProfile M
  /-- Weak equation, evolution-space, trace, and pressure semantics. -/
  equation : WeakNavierStokesFramework H V Pressure Trajectory
  /-- The continuous inclusion of an `H^1` velocity into the `L^2` energy space. -/
  toEnergy : V → H
  /-- Continuity of the `H^1 -> L^2` inclusion. -/
  toEnergyContinuous : Continuous toEnergy
  /-- The dense smooth compactly supported divergence-free core represented inside `V`. -/
  isTestVelocity : V → Prop
  /-- The test core is dense in the source's `H^1` closure `V`. -/
  testVelocitiesDenseInV : Dense {v : V | isTestVelocity v}
  /-- The image of the same core is dense in the source's `L^2` closure `H`. -/
  testVelocitiesDenseInH : Dense (toEnergy '' {v : V | isTestVelocity v})
  /-- The quadratic form `2 ||Def v||_L2^2 = <-Delta_Def v,v>`. -/
  deformationDissipation : V → ℝ
  /-- The two right-hand terms in the exact identity (41). -/
  covariantDerivativeEnergy : V → ℝ
  ricciEnergy : V → ℝ
  /-- The `L^4` norm used in the global two-dimensional Ladyzhenskaya estimate. -/
  l4Norm : V → ℝ
  /-- Steps 2--4, instantiated separately for each source quantifier triple. -/
  existenceRoute : ℝ → ℝ → H → WBK26ExistenceRoute H Trajectory
  /-- Source-level observables for equations (43)--(44). -/
  hasSteklovEnergyEquality : ℝ → ℝ → H → Trajectory → Prop
  hasDifferentialEnergyInequality : ℝ → ℝ → ℝ → H → Trajectory → Prop
  /-- Remark 6.2's difference estimate. -/
  hasDifferenceEnergyEstimate : ℝ → ℝ → H → Trajectory → Trajectory → Prop
  /-- Step 4's residual-annihilation premise for de Rham pressure recovery. -/
  residualAnnihilatesSolenoidalTests : ℝ → ℝ → Trajectory → Prop

/-- Equation (41): the deformation form is the rough energy minus the Ricci pairing. -/
def wbk26ExactDeformationIdentityStatement
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) : Prop :=
  ∀ v, data.isTestVelocity v →
    data.deformationDissipation v =
      data.covariantDerivativeEnergy v - data.ricciEnergy v

/-- Equation (42)'s spectral-gap component: deformation dissipation controls `kappa^2` times the `L^2` energy. -/
def wbk26DeformationCoercivityStatement
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ : ℝ) : Prop :=
  ∀ v, data.isTestVelocity v → κ ^ 2 * ‖data.toEnergy v‖ ^ 2 ≤ data.deformationDissipation v

/-- The global bounded-geometry Ladyzhenskaya inequality used to control the nonlinear term and prove uniqueness. -/
def wbk26LadyzhenskayaStatement
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    ∀ v, data.isTestVelocity v → data.l4Norm v ^ 2 ≤ constant * ‖data.toEnergy v‖ * ‖v‖

/--
The exact content of WBK26 Theorem 6.1 on each positive finite horizon. `H` already denotes the closure of compactly supported smooth
divergence-free fields, so the source quantifier `u0 in H` needs no redundant divergence-free premise.
-/
def wbk26Theorem6_1Statement
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ : ℝ) : Prop :=
  SatisfiesWBK26Geometry data.geometry κ →
    ∀ μ : ℝ, 0 < μ →
      ∀ u0 : H,
        ∀ T : ℝ, 0 < T →
          ∃ u : Trajectory,
            IsWeakNavierStokesSolutionOn data.equation μ T u0 u ∧
              (∃ pressure : Pressure, data.equation.pressureRecoversMomentumOn μ T u pressure) ∧
              IsUniqueWeakNavierStokesSolutionOn data.equation μ T u0 u ∧
              ∀ t : ℝ, 0 ≤ t → t ≤ T →
                ‖data.equation.velocityAt u t‖ ^ 2 ≤
                  Real.exp (-2 * μ * κ ^ 2 * t) * ‖u0‖ ^ 2


end RiemannianFluids
