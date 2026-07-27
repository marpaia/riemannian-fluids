import RiemannianFluids.PDE.Stationary
import RiemannianFluids.ProofStatus

/-!
# CC21 exterior hyperbolic Stokes and Navier--Stokes proof graph

This is the source-order decomposition of Chan--Czubak, arXiv:1708.05134v1,
Sections 3--4.  The Stokes branch records Theorem 3.1, Lemmas 3.2--3.5, and Theorem 3.6.
The nonlinear branch records Lemmas 4.1--4.5, the smallness condition (4.36), the
exhaustion passage (4.38)--(4.40), and Theorem 4.6.
-/

namespace RiemannianFluids

/-- Exterior geometry, weak equations, harmonic seed, and the concrete source constructions. -/
structure CC21Data (Velocity Pressure Seed : Type*) where
  isHyperbolicExteriorDomain : ℝ → ℝ → Prop
  flow : ℝ → ℝ → StationaryFlowFramework Velocity Pressure
  selectedSeed : ℝ → ℝ → Seed
  isNonzeroL2HarmonicSeed : ℝ → Seed → Prop
  seedIsSmallEnoughForNavierStokes : ℝ → ℝ → Seed → Prop
  hasEuclideanDivergenceRightInverse : ℝ → ℝ → Prop
  hasAnnularDivergenceCorrector : ℝ → ℝ → Seed → Prop
  stokesForcingIsBounded : ℝ → ℝ → Seed → Prop
  hasRieszStokesCorrection : ℝ → ℝ → Seed → Prop
  stokesVelocity : ℝ → ℝ → Seed → Velocity
  stokesPressure : ℝ → ℝ → Seed → Pressure
  hasLemma34NegativePairing : ℝ → ℝ → Seed → Prop
  cutoffSeedCannotBeCancelled : ℝ → ℝ → Seed → Prop
  hasHarmonicHessianEstimate : ℝ → ℝ → Seed → Prop
  hasH1L4Estimate : ℝ → Prop
  hasH1PoincareEstimate : ℝ → Prop
  hasEquation4_8GlobalL4Estimate : ℝ → Prop
  hasEquation4_9AnnulusDefinition : ℝ → ℝ → Prop
  hasEquation4_10CorrectorL4Estimate : ℝ → ℝ → Seed → Prop
  hasEquation4_11HarmonicL4Estimate : ℝ → ℝ → Seed → Prop
  hasEquation4_12PsiL4Estimate : ℝ → ℝ → Seed → Prop
  hasEquation4_13PsiDerivativeIdentity : ℝ → ℝ → Seed → Prop
  hasEquation4_14PsiGradientEstimate : ℝ → ℝ → Seed → Prop
  hasEquation4_15CombinedEstimate : ℝ → ℝ → Seed → Prop
  hasEquation4_16L2Estimate : ℝ → ℝ → Seed → Prop
  hasUniformExteriorEnergyBound : ℝ → ℝ → Seed → Prop
  hasLeraySchauderFixedPoints : ℝ → ℝ → Seed → Prop
  hasExhaustionRadiusSequence : ℝ → ℝ → Seed → Prop
  hasExteriorWeakLimit : ℝ → ℝ → Seed → Prop
  nonlinearTermsConverge : ℝ → ℝ → Seed → Prop
  hasExteriorWeakEquation : ℝ → ℝ → Seed → Prop
  navierVelocity : ℝ → ℝ → Seed → Velocity
  navierPressure : ℝ → ℝ → Seed → Pressure

/-- The harmonic extension construction supplies a nonzero square-integrable harmonic one-form. -/
@[proof_obligation]
theorem cc21_hyperbolic_l2_harmonic_seed
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a) :
    data.isNonzeroL2HarmonicSeed a (data.selectedSeed R₀ a) := by
  sorry

/-- Equation (4.36): rescaling the harmonic datum meets the explicit nonlinear smallness threshold. -/
@[proof_obligation]
theorem cc21_equation_4_36_small_seed
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a)
    (hSeed : data.isNonzeroL2HarmonicSeed a (data.selectedSeed R₀ a)) :
    data.seedIsSmallEnoughForNavierStokes R₀ a (data.selectedSeed R₀ a) := by
  sorry

/-- The seed existential used by both branches, assembled from harmonic extension and scaling. -/
@[proof_assembly]
theorem cc21_l2_harmonic_seed_exists
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a) :
    ∃ seed,
      data.isNonzeroL2HarmonicSeed a seed ∧
        data.seedIsSmallEnoughForNavierStokes R₀ a seed := by
  have hSeed := cc21_hyperbolic_l2_harmonic_seed data R₀ a hR₀ ha hGeometry
  exact ⟨data.selectedSeed R₀ a, hSeed,
    cc21_equation_4_36_small_seed data R₀ a hR₀ ha hGeometry hSeed⟩


end RiemannianFluids
