import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.ENNReal.Basic

/-! # Abstract stationary Stokes and Navier--Stokes contracts -/

namespace RiemannianFluids

/-- Typed variational data for stationary Stokes and Navier--Stokes problems.

`Velocity` and `Test` are intended to be concrete normed Sobolev spaces.  Keeping the
bilinear and trilinear forms separate makes the literal weak equation inspectable and lets
paper packages reuse one contract while their manifold integration realizations are built. -/
structure HilbertStationaryFlowData
    (Velocity Test Pressure : Type*)
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test] where
  viscousPairing : Velocity → Test → ℝ
  convectionPairing : Velocity → Velocity → Test → ℝ
  pressurePairing : Pressure → Test → ℝ
  forcingPairing : Test → ℝ
  isSolenoidalTest : Test → Prop
  isEnergyVelocity : Velocity → Prop
  isDivergenceFree : Velocity → Prop
  hasZeroBoundaryTrace : Velocity → Prop

/-- The stationary Stokes variational identity against every energy-space test. -/
def SatisfiesHilbertStationaryStokesBalance
    {Velocity Test Pressure : Type*}
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (data : HilbertStationaryFlowData Velocity Test Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  ∀ test,
    data.viscousPairing velocity test + data.pressurePairing pressure test =
      data.forcingPairing test

/-- The stationary Navier--Stokes variational identity, with the quadratic term visible. -/
def SatisfiesHilbertStationaryNavierStokesBalance
    {Velocity Test Pressure : Type*}
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (data : HilbertStationaryFlowData Velocity Test Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  ∀ test,
    data.viscousPairing velocity test +
        data.convectionPairing velocity velocity test +
        data.pressurePairing pressure test =
      data.forcingPairing test

/-- Full zero-trace finite-energy stationary Stokes solution architecture. -/
def IsHilbertStationaryStokesSolution
    {Velocity Test Pressure : Type*}
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (data : HilbertStationaryFlowData Velocity Test Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  data.isEnergyVelocity velocity ∧ data.isDivergenceFree velocity ∧
    data.hasZeroBoundaryTrace velocity ∧
    SatisfiesHilbertStationaryStokesBalance data velocity pressure

/-- Full zero-trace finite-energy stationary Navier--Stokes solution architecture. -/
def IsHilbertStationaryNavierStokesSolution
    {Velocity Test Pressure : Type*}
    [NormedAddCommGroup Velocity] [NormedSpace ℝ Velocity]
    [NormedAddCommGroup Test] [NormedSpace ℝ Test]
    (data : HilbertStationaryFlowData Velocity Test Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  data.isEnergyVelocity velocity ∧ data.isDivergenceFree velocity ∧
    data.hasZeroBoundaryTrace velocity ∧
    SatisfiesHilbertStationaryNavierStokesBalance data velocity pressure

/-- Observable weak-equation and exterior-domain semantics.

The framework stores quantities rather than conclusion-shaped predicates.  The source notions
of solenoidality, zero trace, finite Dirichlet energy, nontriviality, potential flow, local
pressure integrability, and vanishing PDE residual are the inspectable definitions below. -/
structure StationaryFlowFramework (Velocity Pressure : Type*) where
  divergenceResidualNormSq : Velocity → ℝ
  boundaryTraceNormSq : Velocity → ℝ
  dirichletIntegral : Velocity → ENNReal
  velocityNormSq : Velocity → ℝ
  potentialGradient : Pressure → Velocity
  localPressureNormSq : ℝ → Pressure → ENNReal
  stokesMomentumResidualNormSq : Velocity → Pressure → ℝ
  navierStokesMomentumResidualNormSq : Velocity → Pressure → ℝ

def StationaryFlowFramework.isDivergenceFree
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure) (velocity : Velocity) : Prop :=
  framework.divergenceResidualNormSq velocity = 0

def StationaryFlowFramework.hasZeroBoundaryTrace
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure) (velocity : Velocity) : Prop :=
  framework.boundaryTraceNormSq velocity = 0

def StationaryFlowFramework.hasFiniteDirichletIntegral
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure) (velocity : Velocity) : Prop :=
  framework.dirichletIntegral velocity ≠ ⊤

def StationaryFlowFramework.isNontrivial
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure) (velocity : Velocity) : Prop :=
  0 < framework.velocityNormSq velocity

def StationaryFlowFramework.isPotentialFlow
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure) (velocity : Velocity) : Prop :=
  ∃ potential, framework.potentialGradient potential = velocity

def StationaryFlowFramework.isLocallySquareIntegrablePressure
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure) (pressure : Pressure) : Prop :=
  ∀ radius, 0 < radius → framework.localPressureNormSq radius pressure ≠ ⊤

def StationaryFlowFramework.satisfiesStokesMomentum
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  framework.stokesMomentumResidualNormSq velocity pressure = 0

def StationaryFlowFramework.satisfiesNavierStokesMomentum
    {Velocity Pressure : Type*}
    (framework : StationaryFlowFramework Velocity Pressure)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  framework.navierStokesMomentumResidualNormSq velocity pressure = 0

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
