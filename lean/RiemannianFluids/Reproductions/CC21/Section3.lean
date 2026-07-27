import RiemannianFluids.Reproductions.CC21.Preliminaries

/-! # CC21 Section 3: the exterior Stokes construction -/

namespace RiemannianFluids

/-- Theorem 3.1: a bounded Euclidean annulus admits a controlled divergence right inverse. -/
@[proof_obligation]
theorem cc21_theorem_3_1_divergence_right_inverse
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a) :
    data.hasEuclideanDivergenceRightInverse R₀ a := by
  sorry

/-- Lemma 3.2: solve the annular divergence equation for the cutoff harmonic seed. -/
@[proof_obligation]
theorem cc21_lemma_3_2_annular_corrector
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hRightInverse : data.hasEuclideanDivergenceRightInverse R₀ a)
    (hSeed : data.isNonzeroL2HarmonicSeed a seed) :
    data.hasAnnularDivergenceCorrector R₀ a seed := by
  sorry

/-- Equation (3.29): the corrected cutoff produces a bounded forcing functional. -/
@[proof_obligation]
theorem cc21_equation_3_29_bounded_stokes_forcing
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hCorrector : data.hasAnnularDivergenceCorrector R₀ a seed) :
    data.stokesForcingIsBounded R₀ a seed := by
  sorry

/-- Lemma 3.3: Riesz representation gives the homogeneous Sobolev correction. -/
@[proof_obligation]
theorem cc21_lemma_3_3_riesz_stokes_correction
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hForcing : data.stokesForcingIsBounded R₀ a seed) :
    data.hasRieszStokesCorrection R₀ a seed := by
  sorry

/-- Lemma 3.4, equation (3.37): the annular corrector pairs negatively with the harmonic seed. -/
@[proof_obligation]
theorem cc21_lemma_3_4_negative_pairing
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hSeed : data.isNonzeroL2HarmonicSeed a seed)
    (hCorrection : data.hasRieszStokesCorrection R₀ a seed) :
    data.hasLemma34NegativePairing R₀ a seed := by
  sorry

/-- Lemma 3.5, equations (3.50)--(3.52): Lemma 3.4 prevents cancellation by any solenoidal correction. -/
@[proof_obligation]
theorem cc21_lemma_3_5_noncancellation
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hPairing : data.hasLemma34NegativePairing R₀ a seed) :
    data.cutoffSeedCannotBeCancelled R₀ a seed := by
  sorry

/-- Theorem 3.6: the corrected cutoff, Riesz term, and recovered pressure form a nontrivial Stokes pair. -/
@[proof_obligation]
theorem cc21_theorem_3_6_stokes_pair
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hSeed : data.isNonzeroL2HarmonicSeed a seed)
    (hCorrector : data.hasAnnularDivergenceCorrector R₀ a seed)
    (hRiesz : data.hasRieszStokesCorrection R₀ a seed)
    (hNoncancel : data.cutoffSeedCannotBeCancelled R₀ a seed) :
    IsStationaryStokesSolution (data.flow R₀ a)
        (data.stokesVelocity R₀ a seed) (data.stokesPressure R₀ a seed) ∧
      (data.flow R₀ a).isNontrivial (data.stokesVelocity R₀ a seed) := by
  sorry

/-- The Stokes construction, assembled in the exact order of Section 3. -/
@[proof_assembly]
theorem cc21_stokes_construction_from_harmonic_seed
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a)
    (seed : Seed) (hSeed : data.isNonzeroL2HarmonicSeed a seed) :
    ∃ velocity pressure,
      IsStationaryStokesSolution (data.flow R₀ a) velocity pressure ∧
        (data.flow R₀ a).isNontrivial velocity := by
  have hRightInverse := cc21_theorem_3_1_divergence_right_inverse data R₀ a hR₀ ha hGeometry
  have hCorrector := cc21_lemma_3_2_annular_corrector data R₀ a seed hRightInverse hSeed
  have hForcing := cc21_equation_3_29_bounded_stokes_forcing data R₀ a seed hCorrector
  have hRiesz := cc21_lemma_3_3_riesz_stokes_correction data R₀ a seed hForcing
  have hPairing := cc21_lemma_3_4_negative_pairing data R₀ a seed hSeed hRiesz
  have hNoncancel := cc21_lemma_3_5_noncancellation data R₀ a seed hPairing
  have hPair := cc21_theorem_3_6_stokes_pair data R₀ a seed hSeed hCorrector hRiesz hNoncancel
  exact ⟨data.stokesVelocity R₀ a seed, data.stokesPressure R₀ a seed, hPair⟩

/-- CC21 Theorem 1.4, Stokes branch: the constructed nontrivial solution is not a harmonic potential flow. -/
@[proof_obligation]
theorem cc21_theorem_1_4_stokes_branch
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a)
    (velocity : Velocity) (pressure : Pressure)
    (hSolution : IsStationaryStokesSolution (data.flow R₀ a) velocity pressure)
    (hNontrivial : (data.flow R₀ a).isNontrivial velocity) :
    ¬(data.flow R₀ a).isPotentialFlow velocity := by
  sorry


end RiemannianFluids
