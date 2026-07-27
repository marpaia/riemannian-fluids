import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-! # Solenoidal closures and evolution-space memberships -/

namespace RiemannianFluids

/-- The common smooth compactly supported solenoidal core and its `L2`/`H1` closures. -/
structure SolenoidalClosureData (SmoothField H V : Type*) where
  isSmoothCompactlySupported : SmoothField → Prop
  isDivergenceFree : SmoothField → Prop
  toEnergy : SmoothField → H
  toDissipation : SmoothField → V
  isL2ClosureElement : H → Prop
  isH1ClosureElement : V → Prop
  energyCoreDense : Prop
  dissipationCoreDense : Prop

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
