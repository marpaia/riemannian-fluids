import Mathlib.Data.Real.Basic

/-! # Abstract stationary Stokes and Navier--Stokes contracts -/

namespace RiemannianFluids

/-- Observable weak-equation and exterior-domain semantics. -/
structure StationaryFlowFramework (Velocity Pressure : Type*) where
  isDivergenceFree : Velocity → Prop
  hasZeroBoundaryTrace : Velocity → Prop
  hasFiniteDirichletIntegral : Velocity → Prop
  isNontrivial : Velocity → Prop
  isPotentialFlow : Velocity → Prop
  isLocallySquareIntegrablePressure : Pressure → Prop
  satisfiesStokesMomentum : Velocity → Pressure → Prop
  satisfiesNavierStokesMomentum : Velocity → Pressure → Prop

/-- The source-level steady Stokes solution predicate. -/
def IsStationaryStokesSolution
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  framework.isDivergenceFree velocity ∧
    framework.hasZeroBoundaryTrace velocity ∧
    framework.hasFiniteDirichletIntegral velocity ∧
    framework.isLocallySquareIntegrablePressure pressure ∧
    framework.satisfiesStokesMomentum velocity pressure

/-- The source-level steady Navier--Stokes solution predicate. -/
def IsStationaryNavierStokesSolution
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  framework.isDivergenceFree velocity ∧
    framework.hasZeroBoundaryTrace velocity ∧
    framework.hasFiniteDirichletIntegral velocity ∧
    framework.isLocallySquareIntegrablePressure pressure ∧
    framework.satisfiesNavierStokesMomentum velocity pressure

end RiemannianFluids
