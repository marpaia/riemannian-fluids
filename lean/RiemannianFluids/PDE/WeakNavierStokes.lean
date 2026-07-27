import Mathlib.Analysis.Normed.Module.Basic

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
