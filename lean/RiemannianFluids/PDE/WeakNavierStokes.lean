import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannianFluids.FunctionSpaces.Evolution

/-!
# Weak Navier--Stokes evolution contract

A weak-solution theorem contains more information than the distributional momentum equation. It fixes an initial trace, incompressibility, the two
Bochner-space memberships used by the energy method, and the sense in which a pressure distribution recovers the full equation from its
divergence-free testing form.

`WeakNavierStokesFramework` names those atomic predicates without claiming they have already been instantiated by Riemannian Sobolev spaces. The
definition `IsWeakNavierStokesSolutionOn` then assembles them in one fixed way. This prevents a reproduction theorem from hiding regularity or initial
data inside an opaque predicate while allowing the geometry, integration, and distribution theories to be implemented in separate modules.
-/

namespace RiemannianFluids

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- Concrete functional-analytic data for a weak Navier--Stokes trajectory.  `V` is intended
to be the solenoidal energy space, so the test functions below already encode the divergence
constraint rather than hiding it in the momentum predicate. -/
structure HilbertWeakNavierStokesData
    (H V VDual : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual] where
  inclusion : V →L[ℝ] H
  velocityH : ℝ → H
  velocityV : ℝ → V
  representativesAgree : ∀ time, inclusion (velocityV time) = velocityH time
  timeDerivative : ℝ → VDual
  dualPairing : VDual →L[ℝ] V →L[ℝ] ℝ
  viscousForm : V →L[ℝ] V →L[ℝ] ℝ
  convectionForm : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ
  forcing : ℝ → V →L[ℝ] ℝ

/-- The distributional-in-time momentum equation, represented by its almost-everywhere
evolution-space form against every solenoidal test vector. -/
def SatisfiesHilbertWeakMomentumBalance
    {H V VDual : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (data : HilbertWeakNavierStokesData H V VDual)
    (timeMeasure : Measure ℝ) (viscosity : ℝ) : Prop :=
  ∀ᵐ time ∂timeMeasure, ∀ test : V,
    data.dualPairing (data.timeDerivative time) test +
        viscosity * data.viscousForm (data.velocityV time) test +
        data.convectionForm (data.velocityV time) (data.velocityV time) test =
      data.forcing time test

/-- Weak continuity of the energy representative on `[0,T]`, stated through every element
of Mathlib's continuous dual. -/
def IsWeaklyContinuousEnergyRepresentative
    {H V VDual : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (data : HilbertWeakNavierStokesData H V VDual) (T : ℝ) : Prop :=
  ∀ functional : H →L[ℝ] ℝ,
    ContinuousOn (fun time => functional (data.velocityH time)) (Icc 0 T)

/-- Attainment of the initial datum in the weak `H` topology. -/
def HasWeakHilbertInitialTrace
    {H V VDual : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (data : HilbertWeakNavierStokesData H V VDual) (initial : H) : Prop :=
  ∀ functional : H →L[ℝ] ℝ,
    Tendsto (fun time => functional (data.velocityH time))
      (nhdsWithin 0 (Ioi 0)) (nhds (functional initial))

/-- The standard Leray--Hopf energy inequality with the forcing paired against the velocity.
The paper-specific realization chooses the measure and viscous form. -/
def SatisfiesHilbertEnergyInequality
    {H V VDual : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (data : HilbertWeakNavierStokesData H V VDual)
    (timeMeasure : Measure ℝ) (viscosity T : ℝ) (initial : H) : Prop :=
  ∀ time ∈ Icc (0 : ℝ) T,
    ‖data.velocityH time‖ ^ 2 +
        2 * viscosity * (∫ s in Icc (0 : ℝ) time, data.viscousForm (data.velocityV s) (data.velocityV s) ∂timeMeasure) ≤
      ‖initial‖ ^ 2 +
        2 * (∫ s in Icc (0 : ℝ) time, data.forcing s (data.velocityV s) ∂timeMeasure)

/-- Complete concrete Leray--Hopf architecture: Bochner regularity, weak continuity and
initial trace, the weak momentum equation, and the energy inequality are separate graph nodes. -/
def IsHilbertLerayHopfSolution
    {H V VDual : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (data : HilbertWeakNavierStokesData H V VDual)
    (timeMeasure : Measure ℝ) (viscosity T : ℝ) (initial : H) : Prop :=
  IsBochnerEnergyTrajectory timeMeasure
      { inclusion := data.inclusion
        energyRepresentative := data.velocityH
        dissipationRepresentative := data.velocityV
        representativesAgree := data.representativesAgree } ∧
    IsWeaklyContinuousEnergyRepresentative data T ∧
    HasWeakHilbertInitialTrace data initial ∧
    SatisfiesHilbertWeakMomentumBalance data timeMeasure viscosity ∧
    SatisfiesHilbertEnergyInequality data timeMeasure viscosity T initial

/--
The semantic operations needed to state a weak Navier--Stokes theorem on a finite time horizon.

`H` is the energy space, `V` the energy-dissipation space, `Pressure` the scalar-distribution space, and `Trajectory` the common representation of a
velocity through time. The concrete WBK26 realization must take `H` and `V` to be the `L^2` and `H^1` closures of compactly supported smooth
divergence-free vector fields.
-/
structure WeakNavierStokesFramework
    (H V Pressure Trajectory : Type*) [NormedAddCommGroup H] where
  /-- The `H`-valued velocity representative at time `t`, used by the energy inequality. -/
  velocityAt : Trajectory → ℝ → H
  /-- Distributional momentum balance against compactly supported divergence-free tests. Arguments are viscosity and terminal time. -/
  weakMomentumOn : ℝ → ℝ → Trajectory → Prop
  /-- Spatial incompressibility on the indicated time interval. -/
  divergenceFreeOn : ℝ → Trajectory → Prop
  /-- Attainment of the prescribed initial datum in the weak-solution trace sense. -/
  hasInitialTrace : H → Trajectory → Prop
  /-- Membership in `L^infty(0,T; H)`. -/
  inLInftyHOn : ℝ → Trajectory → Prop
  /-- Membership in `L^2(0,T; V)`. -/
  inL2VOn : ℝ → Trajectory → Prop
  /-- A scalar distribution recovers the full momentum equation. Arguments are viscosity, terminal time, velocity, and pressure. -/
  pressureRecoversMomentumOn : ℝ → ℝ → Trajectory → Pressure → Prop

/--
The source-level weak-solution predicate: momentum balance, incompressibility, initial trace, and both stated evolution-space memberships.
-/
def IsWeakNavierStokesSolutionOn
    {H V Pressure Trajectory : Type*} [NormedAddCommGroup H]
    (framework : WeakNavierStokesFramework H V Pressure Trajectory)
    (μ T : ℝ) (u0 : H) (u : Trajectory) : Prop :=
  framework.weakMomentumOn μ T u ∧
    framework.divergenceFreeOn T u ∧
    framework.hasInitialTrace u0 u ∧
    framework.inLInftyHOn T u ∧
    framework.inL2VOn T u

/-- Uniqueness of the velocity trajectory in the exact weak-solution class stated above. Pressure is intentionally not asserted unique. -/
def IsUniqueWeakNavierStokesSolutionOn
    {H V Pressure Trajectory : Type*} [NormedAddCommGroup H]
    (framework : WeakNavierStokesFramework H V Pressure Trajectory)
    (μ T : ℝ) (u0 : H) (u : Trajectory) : Prop :=
  ∀ candidate,
    IsWeakNavierStokesSolutionOn framework μ T u0 candidate →
      candidate = u

end RiemannianFluids
