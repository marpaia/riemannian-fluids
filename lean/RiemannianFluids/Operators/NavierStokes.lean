import RiemannianFluids.Operators.Stokes

/-!
# Riemannian Navier--Stokes equations and energy analysis

This module corresponds to `riemannian_fluids/operators/navier_stokes.py` and
formalizes the energy consequences of its strong-form terms.  It is an
instantaneous theorem kernel, not yet a time-evolution or weak-solution theory.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- The strong momentum equation at one instant. -/
def SatisfiesMomentumBalance
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    (u uDot : V) (p : Q) (forcing : V) : Prop :=
  uDot + advection.advect u u + ν • viscosity u + calculus.gradient p = forcing

/-- Incompressibility plus the instantaneous nonlinear momentum balance. -/
def IsNavierStokesState
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    (u uDot : V) (p : Q) (forcing : V) : Prop :=
  IsIncompressible V Q calculus u ∧
    SatisfiesMomentumBalance V Q calculus advection viscosity ν u uDot p forcing

/--
If two viscosity operators agree on incompressible fields, they define the
same instantaneous Navier--Stokes states.
-/
theorem navierStokes_iff_of_viscosity_agreesOn
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    {A B : V →ₗ[ℝ] V}
    (hAB : OperatorsAgreeOn V A B (IsIncompressible V Q calculus))
    (ν : ℝ) (u uDot : V) (p : Q) (forcing : V) :
    IsNavierStokesState V Q calculus advection A ν u uDot p forcing ↔
      IsNavierStokesState V Q calculus advection B ν u uDot p forcing := by
  constructor
  · rintro ⟨hu, hMomentum⟩
    refine ⟨hu, ?_⟩
    rw [SatisfiesMomentumBalance] at hMomentum ⊢
    rw [hAB u hu] at hMomentum
    exact hMomentum
  · rintro ⟨hu, hMomentum⟩
    refine ⟨hu, ?_⟩
    rw [SatisfiesMomentumBalance] at hMomentum ⊢
    rw [hAB u hu]
    exact hMomentum

/-- The exact instantaneous energy identity for an abstract Navier--Stokes state. -/
theorem navierStokes_energy_identity
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    {u uDot : V} {p : Q} {forcing : V}
    (state : IsNavierStokesState V Q calculus advection viscosity ν u uDot p forcing) :
    inner ℝ uDot u + ν * inner ℝ (viscosity u) u = inner ℝ forcing u := by
  rcases state with ⟨hu, hMomentum⟩
  have hEnergy := congrArg (fun v : V => inner ℝ v u) hMomentum
  rw [inner_add_left, inner_add_left, inner_add_left] at hEnergy
  rw [advection.energy_cancel u hu] at hEnergy
  rw [pressure_work_eq_zero V Q calculus hu p] at hEnergy
  simpa only [real_inner_smul_left, add_zero, zero_add] using hEnergy

/-- With no forcing, a positive viscosity operator gives a nonpositive energy rate. -/
theorem navierStokes_unforced_energy_rate_nonpositive
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) {ν : ℝ} (hν : 0 ≤ ν)
    {u uDot : V} {p : Q}
    (hPositive : IsNonnegativeOn V viscosity (IsIncompressible V Q calculus))
    (state : IsNavierStokesState V Q calculus advection viscosity ν u uDot p 0) :
    inner ℝ uDot u ≤ 0 := by
  have hEnergy := navierStokes_energy_identity V Q calculus advection viscosity ν state
  rw [inner_zero_left] at hEnergy
  have hDissipation : 0 ≤ ν * inner ℝ (viscosity u) u :=
    mul_nonneg hν (hPositive u state.1)
  linarith

end RiemannianFluids
