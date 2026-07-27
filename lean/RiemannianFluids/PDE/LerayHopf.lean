import Mathlib.Data.Real.Basic

/-! # Abstract Leray--Hopf contracts -/

namespace RiemannianFluids

/-- Observable semantics for initial data, weak equations, and the energy inequality. -/
structure LerayHopfFramework (Initial Solution : Type*) where
  isAdmissibleInitial : Initial → Prop
  hasInitialTrace : Solution → Initial → Prop
  satisfiesWeakEquation : Solution → Prop
  satisfiesEnergyInequality : Solution → Prop

/-- The complete Leray--Hopf predicate, with every constituent visible. -/
def IsLerayHopfSolution
    {Initial Solution : Type*}
    (framework : LerayHopfFramework Initial Solution)
    (initial : Initial) (solution : Solution) : Prop :=
  framework.isAdmissibleInitial initial ∧
    framework.hasInitialTrace solution initial ∧
    framework.satisfiesWeakEquation solution ∧
    framework.satisfiesEnergyInequality solution

end RiemannianFluids
