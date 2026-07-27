import RiemannianFluids.Reproductions.CC21.ProofRoute
import RiemannianFluids.ProofStatus

/-!
# CC21 proof routes

Source: Chan--Czubak, *Antithesis of the Stokes paradox on the hyperbolic plane*,
arXiv:1708.05134v1, Theorems 1.2--1.4.

For every obstacle radius and negative-curvature scale, the paper constructs nontrivial
finite-Dirichlet stationary Stokes and Navier--Stokes solutions with zero boundary trace and
locally square-integrable pressure on the exterior of a geodesic ball.  The constructed
velocities are not harmonic potential flows.
-/

namespace RiemannianFluids

/-- CC21 Theorems 1.2 and 1.4 for the stationary Stokes problem. -/
def cc21NontrivialStokesExteriorStatement
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed) : Prop :=
  ∀ R₀ a : ℝ, 0 < R₀ → 0 < a → data.isHyperbolicExteriorDomain R₀ a →
    ∃ velocity pressure,
      IsStationaryStokesSolution (data.flow R₀ a) velocity pressure ∧
        (data.flow R₀ a).isNontrivial velocity ∧
        ¬(data.flow R₀ a).isPotentialFlow velocity

/-- CC21 Theorems 1.3 and 1.4 for the stationary Navier--Stokes problem. -/
def cc21NontrivialNavierStokesExteriorStatement
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed) : Prop :=
  ∀ R₀ a : ℝ, 0 < R₀ → 0 < a → data.isHyperbolicExteriorDomain R₀ a →
    ∃ velocity pressure,
      IsStationaryNavierStokesSolution (data.flow R₀ a) velocity pressure ∧
        (data.flow R₀ a).isNontrivial velocity ∧
        ¬(data.flow R₀ a).isPotentialFlow velocity

/-- CC21 Theorem 1.4, in the stronger form proved in Section 3.6: a nontrivial solenoidal `H¹₀` solution in either constructed branch cannot be a harmonic potential flow. -/
def cc21NoPotentialFlowStatement
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed) : Prop :=
  ∀ R₀ a : ℝ, 0 < R₀ → 0 < a → data.isHyperbolicExteriorDomain R₀ a →
    (∀ velocity pressure,
      IsStationaryStokesSolution (data.flow R₀ a) velocity pressure →
        (data.flow R₀ a).isNontrivial velocity →
          ¬(data.flow R₀ a).isPotentialFlow velocity) ∧
    ∀ velocity pressure,
      IsStationaryNavierStokesSolution (data.flow R₀ a) velocity pressure →
        (data.flow R₀ a).isNontrivial velocity →
          ¬(data.flow R₀ a).isPotentialFlow velocity

@[literature_terminal]
theorem cc21_theorem_1_2
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed) :
    cc21NontrivialStokesExteriorStatement data := by
  intro R₀ a hR₀ ha hGeometry
  obtain ⟨seed, hSeed, hSmall⟩ :=
    cc21_l2_harmonic_seed_exists data R₀ a hR₀ ha hGeometry
  obtain ⟨velocity, pressure, hSolution, hNontrivial⟩ :=
    cc21_stokes_construction_from_harmonic_seed data R₀ a hR₀ ha hGeometry seed hSeed
  exact
    ⟨velocity, pressure, hSolution, hNontrivial,
      cc21_theorem_1_4_stokes_branch data R₀ a hR₀ ha hGeometry
        velocity pressure hSolution hNontrivial⟩

@[literature_terminal]
theorem cc21_theorem_1_3
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed) :
    cc21NontrivialNavierStokesExteriorStatement data := by
  intro R₀ a hR₀ ha hGeometry
  obtain ⟨seed, hSeed, hSmall⟩ :=
    cc21_l2_harmonic_seed_exists data R₀ a hR₀ ha hGeometry
  obtain ⟨velocity, pressure, hSolution, hNontrivial⟩ :=
    cc21_navier_stokes_construction_by_exhaustion
      data R₀ a hR₀ ha hGeometry seed hSeed hSmall
  exact
    ⟨velocity, pressure, hSolution, hNontrivial,
      cc21_theorem_1_4_navier_stokes_branch data R₀ a hR₀ ha hGeometry
        velocity pressure hSolution hNontrivial⟩

/-- CC21 Theorem 1.4 assembled from the Stokes and Navier--Stokes branches proved together in Section 3.6. -/
@[proof_assembly]
theorem cc21_theorem_1_4
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed) :
    cc21NoPotentialFlowStatement data := by
  intro R₀ a hR₀ ha hGeometry
  exact
    ⟨cc21_theorem_1_4_stokes_branch data R₀ a hR₀ ha hGeometry,
      cc21_theorem_1_4_navier_stokes_branch data R₀ a hR₀ ha hGeometry⟩

end RiemannianFluids
