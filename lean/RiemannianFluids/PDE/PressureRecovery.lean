import Mathlib.Data.Real.Basic

/-!
# De Rham pressure recovery

CCD17, CC15, CC21, and WBK26 all use the same logical principle at different regularities:
a residual distribution that annihilates compactly supported divergence-free tests is a scalar
gradient.  This module separates the distributional statement from any one PDE.
-/

namespace RiemannianFluids

/-- Distributional observables for pressure recovery. -/
structure PressureRecoveryData (Residual Test Pressure : Type*) where
  isCompactlySupportedTest : Test → Prop
  isDivergenceFreeTest : Test → Prop
  residualPairing : Residual → Test → ℝ
  pressureGradient : Pressure → Residual

/-- A residual annihilates all compactly supported solenoidal tests. -/
def AnnihilatesSolenoidalTests
    {Residual Test Pressure : Type*}
    (data : PressureRecoveryData Residual Test Pressure)
    (residual : Residual) : Prop :=
  ∀ test,
    data.isCompactlySupportedTest test →
      data.isDivergenceFreeTest test →
        data.residualPairing residual test = 0

/-- The de Rham conclusion used to recover a pressure distribution. -/
def HasRecoveredPressure
    {Residual Test Pressure : Type*}
    (data : PressureRecoveryData Residual Test Pressure)
    (residual : Residual) : Prop :=
  ∃ pressure, data.pressureGradient pressure = residual

/-- The exact implication that a concrete manifold/distribution theory must realize. -/
def DeRhamPressureRecovery
    {Residual Test Pressure : Type*}
    (data : PressureRecoveryData Residual Test Pressure) : Prop :=
  ∀ residual,
    AnnihilatesSolenoidalTests data residual →
      HasRecoveredPressure data residual

end RiemannianFluids
