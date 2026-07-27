import RiemannianFluids.Reproductions.CC21.Section3

/-! # CC21 Section 4: the exterior Navier--Stokes construction -/

namespace RiemannianFluids

/-- Lemma 4.1, equation (4.5): the `L²` Hessian of the harmonic seed is controlled by its `L²` norm. -/
@[proof_obligation]
theorem cc21_lemma_4_1_harmonic_hessian_estimate
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hSeed : data.isNonzeroL2HarmonicSeed a seed) :
    data.hasHarmonicHessianEstimate R₀ a seed := by
  sorry

/-- Lemma 4.2, equation (4.6): the hyperbolic `H¹` interpolation estimate into `L⁴`. -/
@[proof_obligation]
theorem cc21_lemma_4_2_h1_l4_estimate
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (a : ℝ) (ha : 0 < a) :
    data.hasH1L4Estimate a := by
  sorry

/-- Lemma 4.3, equation (4.7): the hyperbolic Poincare estimate on `H¹₀`. -/
@[proof_obligation]
theorem cc21_lemma_4_3_h1_poincare_estimate
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (a : ℝ) (ha : 0 < a) :
    data.hasH1PoincareEstimate a := by
  sorry

/-- Equation (4.8): combine Lemmas 4.2--4.3 into the global homogeneous `H¹ -> L⁴` estimate. -/
@[proof_obligation]
theorem cc21_equation_4_8_global_l4_estimate
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (a : ℝ)
    (hL4 : data.hasH1L4Estimate a)
    (hPoincare : data.hasH1PoincareEstimate a) :
    data.hasEquation4_8GlobalL4Estimate a := by
  sorry

/-- Equation (4.9): the annular domain notation used throughout the exterior approximation. -/
def cc21Equation4_9AnnularDomain
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) : Prop :=
  data.hasEquation4_9AnnulusDefinition R₀ a

/-- Equation (4.10): the annular corrector inherits an `L⁴` bound from (4.8) and Lemma 3.2. -/
@[proof_obligation]
theorem cc21_equation_4_10_corrector_l4
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hCorrector : data.hasAnnularDivergenceCorrector R₀ a seed)
    (hGlobalL4 : data.hasEquation4_8GlobalL4Estimate a) :
    data.hasEquation4_10CorrectorL4Estimate R₀ a seed := by
  sorry

/-- Equation (4.11): Lemma 4.1 and (4.8) bound the harmonic seed in `L⁴`. -/
@[proof_obligation]
theorem cc21_equation_4_11_harmonic_l4
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hHessian : data.hasHarmonicHessianEstimate R₀ a seed)
    (hGlobalL4 : data.hasEquation4_8GlobalL4Estimate a) :
    data.hasEquation4_11HarmonicL4Estimate R₀ a seed := by
  sorry

/-- Equation (4.12): combine (4.10)--(4.11) to control the corrected cutoff `Psi` in `L⁴`. -/
@[proof_obligation]
theorem cc21_equation_4_12_psi_l4
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hCorrectorL4 : data.hasEquation4_10CorrectorL4Estimate R₀ a seed)
    (hHarmonicL4 : data.hasEquation4_11HarmonicL4Estimate R₀ a seed) :
    data.hasEquation4_12PsiL4Estimate R₀ a seed := by
  sorry

/-- Equation (4.13): differentiate the corrected cutoff `Psi`. -/
@[proof_obligation]
theorem cc21_equation_4_13_psi_derivative
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hCorrector : data.hasAnnularDivergenceCorrector R₀ a seed) :
    data.hasEquation4_13PsiDerivativeIdentity R₀ a seed := by
  sorry

/-- Equation (4.14): insert Lemma 4.1 and the corrector estimate into (4.13). -/
@[proof_obligation]
theorem cc21_equation_4_14_psi_gradient
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hHessian : data.hasHarmonicHessianEstimate R₀ a seed)
    (hCorrector : data.hasAnnularDivergenceCorrector R₀ a seed)
    (hDerivative : data.hasEquation4_13PsiDerivativeIdentity R₀ a seed) :
    data.hasEquation4_14PsiGradientEstimate R₀ a seed := by
  sorry

/-- Equation (4.15): collect the `L⁴` and gradient estimates for the corrector and `Psi`. -/
@[proof_obligation]
theorem cc21_equation_4_15_combined_estimate
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hCorrectorL4 : data.hasEquation4_10CorrectorL4Estimate R₀ a seed)
    (hPsiL4 : data.hasEquation4_12PsiL4Estimate R₀ a seed)
    (hPsiGradient : data.hasEquation4_14PsiGradientEstimate R₀ a seed) :
    data.hasEquation4_15CombinedEstimate R₀ a seed := by
  sorry

/-- Equation (4.16): Poincare upgrades (4.15) to the corresponding `L²` estimates. -/
@[proof_obligation]
theorem cc21_equation_4_16_l2_estimate
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hPoincare : data.hasH1PoincareEstimate a)
    (hCombined : data.hasEquation4_15CombinedEstimate R₀ a seed) :
    data.hasEquation4_16L2Estimate R₀ a seed := by
  sorry

/-- Lemma 4.4, equation (4.37): bounded-domain fixed points obey an exhaustion-uniform `H1` estimate. -/
@[proof_obligation]
theorem cc21_lemma_4_4_uniform_exterior_energy
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hEstimates : data.hasEquation4_15CombinedEstimate R₀ a seed)
    (hL2 : data.hasEquation4_16L2Estimate R₀ a seed)
    (hSmall : data.seedIsSmallEnoughForNavierStokes R₀ a seed) :
    data.hasUniformExteriorEnergyBound R₀ a seed := by
  sorry

/-- Lemma 4.5: Leray--Schauder gives a solution on every truncated exterior domain. -/
@[proof_obligation]
theorem cc21_lemma_4_5_leray_schauder
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hUniform : data.hasUniformExteriorEnergyBound R₀ a seed) :
    data.hasLeraySchauderFixedPoints R₀ a seed := by
  sorry

/-- Equation (4.38): choose a strictly increasing exhaustion-radius sequence tending to infinity. -/
@[proof_obligation]
theorem cc21_equation_4_38_exhaustion_radii
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hFixedPoints : data.hasLeraySchauderFixedPoints R₀ a seed)
    (hUniform : data.hasUniformExteriorEnergyBound R₀ a seed) :
    data.hasExhaustionRadiusSequence R₀ a seed := by
  sorry

/-- Equation (4.39): extract the weakly convergent subsequence on the full exterior energy space. -/
@[proof_obligation]
theorem cc21_equation_4_39_exterior_weak_limit
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hFixedPoints : data.hasLeraySchauderFixedPoints R₀ a seed)
    (hUniform : data.hasUniformExteriorEnergyBound R₀ a seed)
    (hRadii : data.hasExhaustionRadiusSequence R₀ a seed) :
    data.hasExteriorWeakLimit R₀ a seed := by
  sorry

/-- Section 4.6 between (4.39) and (4.40): local compactness passes all quadratic terms to the limit. -/
@[proof_obligation]
theorem cc21_section_4_6_nonlinear_limit
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hFixedPoints : data.hasLeraySchauderFixedPoints R₀ a seed)
    (hUniform : data.hasUniformExteriorEnergyBound R₀ a seed)
    (hWeakLimit : data.hasExteriorWeakLimit R₀ a seed) :
    data.nonlinearTermsConverge R₀ a seed := by
  sorry

/-- Equation (4.40): after the nonlinear passage, the exterior weak limit satisfies the weak equation. -/
@[proof_obligation]
theorem cc21_equation_4_40_exterior_weak_equation
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hWeakLimit : data.hasExteriorWeakLimit R₀ a seed)
    (hNonlinear : data.nonlinearTermsConverge R₀ a seed) :
    data.hasExteriorWeakEquation R₀ a seed := by
  sorry

/-- Theorem 4.6: the exhaustion limit and de Rham pressure recovery yield a nontrivial stationary Navier--Stokes pair. -/
@[proof_obligation]
theorem cc21_theorem_4_6_navier_stokes_pair
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (seed : Seed)
    (hSeed : data.isNonzeroL2HarmonicSeed a seed)
    (hLimit : data.hasExteriorWeakLimit R₀ a seed)
    (hWeakEquation : data.hasExteriorWeakEquation R₀ a seed) :
    IsStationaryNavierStokesSolution (data.flow R₀ a)
        (data.navierVelocity R₀ a seed) (data.navierPressure R₀ a seed) ∧
      (data.flow R₀ a).isNontrivial (data.navierVelocity R₀ a seed) := by
  sorry

/-- The nonlinear construction, assembled in the exact order of Section 4. -/
@[proof_assembly]
theorem cc21_navier_stokes_construction_by_exhaustion
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a)
    (seed : Seed) (hSeed : data.isNonzeroL2HarmonicSeed a seed)
    (hSmall : data.seedIsSmallEnoughForNavierStokes R₀ a seed) :
    ∃ velocity pressure,
      IsStationaryNavierStokesSolution (data.flow R₀ a) velocity pressure ∧
        (data.flow R₀ a).isNontrivial velocity := by
  have hHessian := cc21_lemma_4_1_harmonic_hessian_estimate data R₀ a seed hSeed
  have hL4 := cc21_lemma_4_2_h1_l4_estimate data a ha
  have hPoincare := cc21_lemma_4_3_h1_poincare_estimate data a ha
  have hGlobalL4 := cc21_equation_4_8_global_l4_estimate data a hL4 hPoincare
  have hRightInverse := cc21_theorem_3_1_divergence_right_inverse data R₀ a hR₀ ha hGeometry
  have hCorrector := cc21_lemma_3_2_annular_corrector data R₀ a seed hRightInverse hSeed
  have hCorrectorL4 := cc21_equation_4_10_corrector_l4 data R₀ a seed hCorrector hGlobalL4
  have hHarmonicL4 := cc21_equation_4_11_harmonic_l4 data R₀ a seed hHessian hGlobalL4
  have hPsiL4 := cc21_equation_4_12_psi_l4 data R₀ a seed hCorrectorL4 hHarmonicL4
  have hPsiDerivative := cc21_equation_4_13_psi_derivative data R₀ a seed hCorrector
  have hPsiGradient := cc21_equation_4_14_psi_gradient data R₀ a seed
    hHessian hCorrector hPsiDerivative
  have hEstimates := cc21_equation_4_15_combined_estimate data R₀ a seed
    hCorrectorL4 hPsiL4 hPsiGradient
  have hL2Estimate := cc21_equation_4_16_l2_estimate data R₀ a seed hPoincare hEstimates
  have hUniform := cc21_lemma_4_4_uniform_exterior_energy data R₀ a seed
    hEstimates hL2Estimate hSmall
  have hFixed := cc21_lemma_4_5_leray_schauder data R₀ a seed hUniform
  have hRadii := cc21_equation_4_38_exhaustion_radii data R₀ a seed hFixed hUniform
  have hLimit := cc21_equation_4_39_exterior_weak_limit data R₀ a seed hFixed hUniform hRadii
  have hNonlinear := cc21_section_4_6_nonlinear_limit data R₀ a seed
    hFixed hUniform hLimit
  have hWeakEquation := cc21_equation_4_40_exterior_weak_equation data R₀ a seed
    hLimit hNonlinear
  have hPair := cc21_theorem_4_6_navier_stokes_pair data R₀ a seed
    hSeed hLimit hWeakEquation
  exact ⟨data.navierVelocity R₀ a seed, data.navierPressure R₀ a seed, hPair⟩

/-- CC21 Theorem 1.4, Navier--Stokes branch: the same exterior-domain argument excludes potential flow. -/
@[proof_obligation]
theorem cc21_theorem_1_4_navier_stokes_branch
    {Velocity Pressure Seed : Type*}
    (data : CC21Data Velocity Pressure Seed)
    (R₀ a : ℝ) (hR₀ : 0 < R₀) (ha : 0 < a)
    (hGeometry : data.isHyperbolicExteriorDomain R₀ a)
    (velocity : Velocity) (pressure : Pressure)
    (hSolution : IsStationaryNavierStokesSolution (data.flow R₀ a) velocity pressure)
    (hNontrivial : (data.flow R₀ a).isNontrivial velocity) :
    ¬(data.flow R₀ a).isPotentialFlow velocity := by
  sorry


end RiemannianFluids
