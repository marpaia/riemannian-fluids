import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Solenoidal closures and evolution-space memberships -/

namespace RiemannianFluids

open MeasureTheory
open scoped ENNReal

/-- A trajectory represented simultaneously in the dissipation space `V` and the energy space
`H`, with a continuous inclusion identifying the two representatives. -/
structure BochnerEvolutionTrajectory
    (H V : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  inclusion : V →L[ℝ] H
  energyRepresentative : ℝ → H
  dissipationRepresentative : ℝ → V
  representativesAgree : ∀ time,
    inclusion (dissipationRepresentative time) = energyRepresentative time

/-- The concrete Bochner part of the Leray class, using Mathlib's `MemLp` at exponents `∞` and
`2`.  Weak continuity and the initial trace remain separate because they are not consequences of
these two memberships alone. -/
def IsBochnerEnergyTrajectory
    {H V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (timeMeasure : Measure ℝ) (trajectory : BochnerEvolutionTrajectory H V) : Prop :=
  MemLp trajectory.energyRepresentative ∞ timeMeasure ∧
    MemLp trajectory.dissipationRepresentative 2 timeMeasure

/-- The common smooth compactly supported solenoidal core represented in the energy and
dissipation spaces.  Density is Mathlib's topological `Dense`, not an opaque certificate. -/
structure SolenoidalClosureData (SmoothField H V : Type*)
    [TopologicalSpace H] [TopologicalSpace V] where
  isSmoothCompactlySupported : SmoothField → Prop
  isDivergenceFree : SmoothField → Prop
  toEnergy : SmoothField → H
  toDissipation : SmoothField → V
  energyCoreDense :
    Dense (toEnergy '' {field | isSmoothCompactlySupported field ∧ isDivergenceFree field})
  dissipationCoreDense :
    Dense (toDissipation '' {field | isSmoothCompactlySupported field ∧ isDivergenceFree field})

/-- Membership in the `L²` closure of the common solenoidal test core. -/
def SolenoidalClosureData.isL2ClosureElement
    {SmoothField H V : Type*} [TopologicalSpace H] [TopologicalSpace V]
    (data : SolenoidalClosureData SmoothField H V) (field : H) : Prop :=
  field ∈ closure
    (data.toEnergy ''
      {smooth | data.isSmoothCompactlySupported smooth ∧ data.isDivergenceFree smooth})

/-- Membership in the `H¹` closure of the common solenoidal test core. -/
def SolenoidalClosureData.isH1ClosureElement
    {SmoothField H V : Type*} [TopologicalSpace H] [TopologicalSpace V]
    (data : SolenoidalClosureData SmoothField H V) (field : V) : Prop :=
  field ∈ closure
    (data.toDissipation ''
      {smooth | data.isSmoothCompactlySupported smooth ∧ data.isDivergenceFree smooth})

/-- Bochner-space, trace, weak-time-derivative, and local convergence observables. -/
structure EvolutionSpaceData (H V VDual Trajectory : Type*) where
  inLInftyH : ℝ → Trajectory → Prop
  inL2V : ℝ → Trajectory → Prop
  timeDerivativeInL2VDual : ℝ → Trajectory → Prop
  weaklyContinuousInH : ℝ → Trajectory → Prop
  hasInitialTrace : H → Trajectory → Prop
  locallyStrongInL2 : (ℕ → Trajectory) → Trajectory → Prop

/-- The full Leray energy class on `[0,T]`, before imposing an equation. -/
def IsLerayEnergyTrajectory
    {H V VDual Trajectory : Type*}
    (data : EvolutionSpaceData H V VDual Trajectory)
    (T : ℝ) (u0 : H) (u : Trajectory) : Prop :=
  data.inLInftyH T u ∧ data.inL2V T u ∧
    data.weaklyContinuousInH T u ∧ data.hasInitialTrace u0 u

end RiemannianFluids
