import RiemannianFluids.Operators.Stokes

/-!
# Riemannian Navier--Stokes equations and energy analysis

At one instant, the incompressible Navier--Stokes momentum balance has the schematic form

    uDot + ∇_u u + ν L u + grad p = f,
    div u = 0.

The terms match the equation displayed after CCD17 equation (1.3), but the present module is intentionally neutral about which curved-space viscosity
operator `L` has been selected.

## The energy calculation

Take the inner product of the momentum equation with `u`. Linearity gives

    ⟨uDot,u⟩ + ⟨∇_u u,u⟩ + ν⟨Lu,u⟩ + ⟨grad p,u⟩ = ⟨f,u⟩.

The two interfaces from `AbstractEnergy` remove transport and pressure:

    ⟨∇_u u,u⟩ = 0,
    ⟨grad p,u⟩ = -⟨p,div u⟩ = 0.

Thus

    ⟨uDot,u⟩ + ν⟨Lu,u⟩ = ⟨f,u⟩.

If `f = 0`, `ν ≥ 0`, and `L` is nonnegative on incompressible fields, then the second term is nonnegative and `⟨uDot,u⟩ ≤ 0`. The two final theorems
follow this argument line for line.

## What “instantaneous” means

`uDot` is supplied as a vector; it is not constructed as the derivative of a curve `t ↦ u(t)`. Consequently `⟨uDot,u⟩` has not yet been proved equal
to `d/dt (‖u‖²/2)`. Nor has a weak solution, integration theory, or boundary condition been built. The result is an algebraic kernel that a later
time-dependent theory can instantiate.

The first theorem in the file makes operator comparison useful for equations: if `A` and `B` agree on incompressible fields, then replacing one by the
other does not change the instantaneous state predicate. This is how a geometric identity such as the CCD17 divergence-free comparison can eventually
flow into the PDE layer without globally identifying inequivalent operators.
-/

namespace RiemannianFluids

open scoped RealInnerProductSpace

variable
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/--
The strong momentum equation at one instant:

`uDot + ∇_u u + ν L u + grad p = forcing`.

`uDot` is supplied as a vector rather than derived from a time-dependent map. This keeps the declaration honest about the absence of evolution spaces.
-/
def SatisfiesMomentumBalance
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    (u uDot : V) (p : Q) (forcing : V) : Prop :=
  uDot + advection.advect u u + ν • viscosity u + calculus.gradient p = forcing

/--
Incompressibility plus the instantaneous nonlinear momentum balance. The conjunction keeps the constraint available to both pressure and advection
cancellation proofs.
-/
def IsNavierStokesState
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    (u uDot : V) (p : Q) (forcing : V) : Prop :=
  IsIncompressible V Q calculus u ∧
    SatisfiesMomentumBalance V Q calculus advection viscosity ν u uDot p forcing

/--
If two viscosity operators agree on incompressible fields, they define the same instantaneous Navier--Stokes states.
-/
theorem navierStokes_iff_of_viscosity_agreesOn
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    {A B : V →ₗ[ℝ] V}
    (hAB : OperatorsAgreeOn V A B (IsIncompressible V Q calculus))
    (ν : ℝ) (u uDot : V) (p : Q) (forcing : V) :
    IsNavierStokesState V Q calculus advection A ν u uDot p forcing ↔
      IsNavierStokesState V Q calculus advection B ν u uDot p forcing := by
  -- Prove the equivalence in each direction; both arguments are symmetric.
  constructor
  -- Start from an `A`-viscosity state and unpack incompressibility and momentum.
  · rintro ⟨hu, hMomentum⟩
    -- Reuse the same incompressibility proof; only momentum needs rewriting.
    refine ⟨hu, ?_⟩
    -- Expose the momentum predicates on the hypothesis and goal.
    rw [SatisfiesMomentumBalance] at hMomentum ⊢
    -- Agreement is applicable precisely because `hu` proves admissibility.
    rw [hAB u hu] at hMomentum
    exact hMomentum
  -- Repeat in the reverse direction.
  · rintro ⟨hu, hMomentum⟩
    refine ⟨hu, ?_⟩
    rw [SatisfiesMomentumBalance] at hMomentum ⊢
    -- Rewrite the goal's `A u` to `B u`; the known momentum equation then fits.
    rw [hAB u hu]
    exact hMomentum

/--
The exact instantaneous energy identity for an abstract Navier--Stokes state:

`⟪uDot,u⟫ + ν ⟪L u,u⟫ = ⟪forcing,u⟫`.

This is the formal “test the momentum equation against `u`” calculation. Its two cancellations are assumptions of `ScalarVectorCalculus` and
`EnergyConservingAdvection`, not hidden analytic theorems.
-/
theorem navierStokes_energy_identity
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) (ν : ℝ)
    {u uDot : V} {p : Q} {forcing : V}
    (state : IsNavierStokesState V Q calculus advection viscosity ν u uDot p forcing) :
    inner ℝ uDot u + ν * inner ℝ (viscosity u) u = inner ℝ forcing u := by
  -- Unpack incompressibility and the vector-valued momentum equality.
  rcases state with ⟨hu, hMomentum⟩
  -- Apply the linear functional `v ↦ ⟪v,u⟫` to both sides: this is the Lean version of taking the `L²` inner product of the equation with `u`.
  have hEnergy := congrArg (fun v : V => inner ℝ v u) hMomentum
  -- Distribute the inner product over the four terms on the left.
  rw [inner_add_left, inner_add_left, inner_add_left] at hEnergy
  -- Incompressible advection contributes no kinetic energy.
  rw [advection.energy_cancel u hu] at hEnergy
  -- Pressure gradients are orthogonal to incompressible velocity.
  rw [pressure_work_eq_zero V Q calculus hu p] at hEnergy
  -- Move the real scalar `ν` outside the inner product and erase zero summands.
  simpa only [real_inner_smul_left, add_zero, zero_add] using hEnergy

/--
With no forcing, a positive viscosity operator gives a nonpositive energy rate. This is still instantaneous: `⟪uDot,u⟫` has not yet been identified
with the derivative of `‖u‖²/2` for an actual trajectory.
-/
theorem navierStokes_unforced_energy_rate_nonpositive
    (calculus : ScalarVectorCalculus V Q)
    (advection : EnergyConservingAdvection V (IsIncompressible V Q calculus))
    (viscosity : V →ₗ[ℝ] V) {ν : ℝ} (hν : 0 ≤ ν)
    {u uDot : V} {p : Q}
    (hPositive : IsNonnegativeOn V viscosity (IsIncompressible V Q calculus))
    (state : IsNavierStokesState V Q calculus advection viscosity ν u uDot p 0) :
    inner ℝ uDot u ≤ 0 := by
  -- Apply the exact energy identity with zero forcing.
  have hEnergy := navierStokes_energy_identity V Q calculus advection viscosity ν state
  -- The forcing work `⟪0,u⟫` vanishes.
  rw [inner_zero_left] at hEnergy
  -- Nonnegative viscosity and `ν ≥ 0` make the dissipation term nonnegative.
  have hDissipation : 0 ≤ ν * inner ℝ (viscosity u) u :=
    mul_nonneg hν (hPositive u state.1)
  -- The energy equality now reads “rate + nonnegative term = 0”.
  linarith

end RiemannianFluids
