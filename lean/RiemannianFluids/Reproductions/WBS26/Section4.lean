import RiemannianFluids.Reproductions.WBS26.Section3

/-! # WBS26 Section 4: rigorous thin-shell limit -/

namespace RiemannianFluids

/-- Theorem 4.1: the revolution-shell Korn inequality, uniform in thickness and azimuthal mode. -/
@[proof_obligation]
theorem wbs26_theorem_4_1_uniform_korn
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    WBS26UniformKorn data := by
  sorry

/-- Lemma 4.2: the two-wall Friedrichs identity yields uniform Gaffney coercivity. -/
@[proof_obligation]
theorem wbs26_lemma_4_2_uniform_gaffney
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    WBS26UniformGaffney data := by
  sorry

/-- Theorem 4.3, equations (23)--(24): exact perfect-square expressions for both rescaled densities. -/
@[proof_obligation]
theorem wbs26_theorem_4_3_exact_limit_densities
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall sequence limit,
      (data.forms wall).weaklyConverges sequence limit →
        (data.forms wall).limitEnergy limit ≤ (data.forms wall).liminfEnergy sequence := by
  sorry

/-- Theorem 4.4, equation (25): the Weitzenbock identity supplies the Ricci shift between the limiting forms. -/
@[proof_obligation]
theorem wbs26_theorem_4_4_ricci_shift
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ limit, data.isTangential limit → data.ricciShiftHolds limit := by
  sorry

/-- Theorem 4.5 (M1): bounded energy and the slice estimate identify the weak limit with its tangential slow field. -/
@[proof_obligation]
theorem wbs26_m1_identifies_tangential_slow_field
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall sequence limit,
      (data.forms wall).weaklyConverges sequence limit →
        data.slowFieldOf sequence = limit ∧ data.isTangential limit := by
  sorry

/-- Theorem 4.5 (M1): the divergence constraint survives the thin direction and makes the slow field solenoidal. -/
@[proof_obligation]
theorem wbs26_m1_identifies_solenoidal_limit
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall sequence limit,
      (data.forms wall).weaklyConverges sequence limit →
        data.slowFieldOf sequence = limit → data.isSolenoidal limit := by
  sorry

@[proof_assembly]
theorem wbs26_mosco_liminf
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall, MoscoLiminf (data.forms wall) := by
  have hKorn := wbs26_theorem_4_1_uniform_korn data hGeometry
  have hGaffney := wbs26_lemma_4_2_uniform_gaffney data hGeometry
  intro wall sequence limit hWeak
  have hIdentification :=
    wbs26_m1_identifies_tangential_slow_field data hGeometry wall sequence limit hWeak
  have hSolenoidal :=
    wbs26_m1_identifies_solenoidal_limit data hGeometry wall sequence limit hWeak
      hIdentification.1
  have hRicci := wbs26_theorem_4_4_ricci_shift data hGeometry limit hIdentification.2
  exact wbs26_theorem_4_3_exact_limit_densities data hGeometry wall sequence limit hWeak

/-- Appendix A.2: the matched two-wall ansatz has the correct slow field and the paper's `O(epsilon^2)` energy expansion on smooth data. -/
@[proof_obligation]
theorem wbs26_smooth_two_wall_recovery
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall limit,
      (data.forms wall).isSmoothLimit limit →
        (data.forms wall).stronglyConverges
          (data.smoothRecoverySequence wall limit) limit ∧
        (data.forms wall).hasQuadraticRecoveryRate
          (data.smoothRecoverySequence wall limit) limit := by
  sorry

/-- Appendix A.2: a uniform divergence right inverse adds an exact solenoidal correction without changing the limit energy. -/
@[proof_obligation]
theorem wbs26_exact_solenoidal_correction
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall limit,
      (data.forms wall).isSmoothLimit limit →
        (data.forms wall).stronglyConverges
          (data.correctedRecoverySequence wall limit) limit ∧
        Filter.Tendsto
          (fun n => (data.forms wall).bulkEnergy n
            (data.correctedRecoverySequence wall limit n))
          Filter.atTop
          (nhds ((data.forms wall).limitEnergy limit)) ∧
        (data.forms wall).hasQuadraticRecoveryRate
          (data.correctedRecoverySequence wall limit) limit := by
  sorry

/-- Theorem 4.5 (M2): density of the smooth form core and diagonal selection extend recovery to the full limit form domain. -/
@[proof_obligation]
theorem wbs26_diagonal_core_recovery
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall limit,
      ¬(data.forms wall).isSmoothLimit limit →
        (data.forms wall).stronglyConverges
          (data.diagonalRecoverySequence wall limit) limit ∧
        Filter.Tendsto
          (fun n => (data.forms wall).bulkEnergy n
            (data.diagonalRecoverySequence wall limit n))
          Filter.atTop
          (nhds ((data.forms wall).limitEnergy limit)) := by
  sorry

@[proof_assembly]
theorem wbs26_mosco_recovery
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall, MoscoRecovery (data.forms wall) := by
  intro wall limit
  classical
  by_cases hSmooth : (data.forms wall).isSmoothLimit limit
  · have hMatched := wbs26_smooth_two_wall_recovery data hGeometry wall limit hSmooth
    have hCorrected := wbs26_exact_solenoidal_correction data hGeometry wall limit hSmooth
    exact ⟨data.correctedRecoverySequence wall limit, hCorrected.1, hCorrected.2.1,
      fun _ => hCorrected.2.2⟩
  · have hDiagonal := wbs26_diagonal_core_recovery data hGeometry wall limit hSmooth
    exact ⟨data.diagonalRecoverySequence wall limit, hDiagonal.1, hDiagonal.2,
      fun h => False.elim (hSmooth h)⟩

/-- WBS26 Theorem 4.5 assembled from its source-designated Mosco `(M1)` and `(M2)` halves. -/
@[proof_assembly]
theorem wbs26_theorem_4_5
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) :
    wbs26Theorem4_5Statement data := by
  intro hGeometry wall
  exact
    ⟨wbs26_mosco_liminf data hGeometry wall,
      wbs26_mosco_recovery data hGeometry wall⟩

/-- Kuwae--Shioya's varying-Hilbert-space theorem applied to Theorem 4.5. -/
@[proof_obligation]
theorem wbs26_mosco_implies_strong_resolvent
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall, MoscoConverges (data.forms wall) →
      StrongResolventConvergence (data.operators wall) := by
  sorry

/-- Corollary 4.6: the functional calculus turns strong resolvent convergence into strong semigroup convergence. -/
@[proof_obligation]
theorem wbs26_resolvent_implies_semigroup
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall, StrongResolventConvergence (data.operators wall) →
      StrongSemigroupConvergence (data.operators wall) := by
  sorry

@[proof_assembly]
theorem wbs26_resolvent_and_semigroup_convergence
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall,
      StrongResolventConvergence (data.operators wall) ∧
        StrongSemigroupConvergence (data.operators wall) := by
  intro wall
  have hMosco := wbs26_theorem_4_5 data hGeometry wall
  have hResolvent := wbs26_mosco_implies_strong_resolvent data hGeometry wall hMosco
  exact ⟨hResolvent, wbs26_resolvent_implies_semigroup data hGeometry wall hResolvent⟩

/-- Corollary 4.6: each azimuthal sector has compact resolvent and fixed-mode eigenvalues converge with multiplicity. -/
@[proof_obligation]
theorem wbs26_modewise_spectral_convergence
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall, ModewiseSpectralConvergence (data.operators wall) := by
  sorry

/-- Corollary 4.6: Korn/Gaffney coercivity yields a uniform quadratic gap on azimuthal mode `m`. -/
@[proof_obligation]
theorem wbs26_uniform_high_mode_gap
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall, UniformHighModeGap (data.operators wall) := by
  sorry

/-- Corollary 4.6: the high-mode cutoff reduces every bounded spectral window to finitely many fixed modes. -/
@[proof_obligation]
theorem wbs26_full_spectral_convergence
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit)
    (hGeometry : data.isTorusTypeSurfaceOfRevolution) :
    ∀ wall,
      ModewiseSpectralConvergence (data.operators wall) →
      UniformHighModeGap (data.operators wall) →
        FullSpectralConvergence (data.operators wall) := by
  sorry

/-- WBS26 Corollary 4.6 assembled from Theorem 4.5, functional calculus, and the modewise/high-mode spectral argument. -/
@[proof_assembly]
theorem wbs26_corollary_4_6
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) :
    wbs26Corollary4_6Statement data := by
  intro hGeometry wall
  have hOperators := wbs26_resolvent_and_semigroup_convergence data hGeometry wall
  have hModewise := wbs26_modewise_spectral_convergence data hGeometry wall
  have hFull := wbs26_full_spectral_convergence data hGeometry wall hModewise
    (wbs26_uniform_high_mode_gap data hGeometry wall)
  exact ⟨hOperators.1, hOperators.2, hModewise, hFull⟩

@[literature_terminal]
theorem wbs26_theorem_4_5_and_corollary_4_6
    {Bulk Limit : Type*} (data : WBS26ConvergenceData Bulk Limit) :
    wbs26MoscoResolventSpectrumStatement data := by
  intro hGeometry wall
  have hTheorem := wbs26_theorem_4_5 data hGeometry wall
  have hCorollary := wbs26_corollary_4_6 data hGeometry wall
  exact
    ⟨hTheorem, hCorollary.1, hCorollary.2.1,
      hCorollary.2.2.1, hCorollary.2.2.2⟩


end RiemannianFluids
