import RiemannianFluids.Reproductions.WBK26.Kinematics

/-! # WBK26 Section 6: coercivity and global weak solutions -/

namespace RiemannianFluids

/-- Equation (41), including the integration-by-parts identification with `2 ||Def u||^2`. -/
@[proof_obligation]
theorem wbk26_equation_41_exact_deformation_identity
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) :
    wbk26ExactDeformationIdentityStatement data := by
  sorry

/-- Equation (42): strict coercivity from equation (41), `Ric(u)=Ku`, and `K <= -kappa^2`. -/
@[proof_obligation]
theorem wbk26_deformation_coercivity
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) :
    wbk26DeformationCoercivityStatement data κ := by
  have hExact := wbk26_equation_41_exact_deformation_identity data κ hGeometry
  sorry

/-- The global two-dimensional Ladyzhenskaya estimate supplied by bounded geometry. -/
@[proof_obligation]
theorem wbk26_global_ladyzhenskaya
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) :
    wbk26LadyzhenskayaStatement data := by
  sorry

/-- WBK26 Step 2: geodesic balls form a smooth nested exhaustion. -/
@[proof_obligation]
theorem wbk26_step_2_smooth_exhaustion
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) :
    HasSmoothExhaustion (data.existenceRoute μ T u0).compactness := by
  sorry

/-- WBK26 Step 2: the compactly supported initial data converge in `H` without norm growth. -/
@[proof_obligation]
theorem wbk26_step_2_initial_approximation
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) :
    HasInitialApproximation (data.existenceRoute μ T u0).compactness u0 := by
  sorry

/-- WBK26 Step 2: classical bounded-domain Galerkin theory supplies each Dirichlet solution. -/
@[proof_obligation]
theorem wbk26_step_2_compact_domain_galerkin
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) :
    HasCompactDomainSolutions (data.existenceRoute μ T u0).compactness := by
  sorry

/-- Equation (46): zero extension and equation (42) give the uniform energy bound. -/
@[proof_obligation]
theorem wbk26_equation_46_uniform_energy
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hCoercivity : wbk26DeformationCoercivityStatement data κ) :
    ∃ bound, HasUniformEnergyBounds (data.existenceRoute μ T u0).compactness bound := by
  sorry

/-- WBK26 Step 3: Ladyzhenskaya plus (46) yields uniform `L4_t L4_x`. -/
@[proof_obligation]
theorem wbk26_step_3_uniform_l4
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hLadyzhenskaya : wbk26LadyzhenskayaStatement data)
    (hEnergy : ∃ bound, HasUniformEnergyBounds
      (data.existenceRoute μ T u0).compactness bound) :
    ∃ bound, HasUniformSpacetimeL4Bound
      (data.existenceRoute μ T u0).compactness bound := by
  sorry

/-- WBK26 Step 3: the equation bounds `partial_t u_R` in `L2(0,T; V_R*)`. -/
@[proof_obligation]
theorem wbk26_step_3_uniform_time_derivative
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hL4 : ∃ bound, HasUniformSpacetimeL4Bound
      (data.existenceRoute μ T u0).compactness bound) :
    ∃ bound, HasUniformTimeDerivativeBound
      (data.existenceRoute μ T u0).compactness bound := by
  sorry

/-- Equation (47): testing the time derivative against the time translate gives the global fractional estimate. -/
@[proof_obligation]
theorem wbk26_equation_47_time_translation
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hTimeDerivative : ∃ bound, HasUniformTimeDerivativeBound
      (data.existenceRoute μ T u0).compactness bound) :
    ∃ constant, HasFractionalTimeTranslationBound
      (data.existenceRoute μ T u0).compactness constant := by
  sorry

/-- WBK26 Step 3: local Rellich--Simon compactness and diagonal extraction. -/
@[proof_obligation]
theorem wbk26_step_3_local_strong_compactness
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hEnergy : ∃ bound, HasUniformEnergyBounds
      (data.existenceRoute μ T u0).compactness bound)
    (hTranslation : ∃ constant, HasFractionalTimeTranslationBound
      (data.existenceRoute μ T u0).compactness constant) :
    HasLocallyStrongSubsequence (data.existenceRoute μ T u0).compactness := by
  sorry

/-- Equation (48): strong local convergence plus the global `L4` bound passes through `u_R tensor u_R`. -/
@[proof_obligation]
theorem wbk26_equation_48_nonlinear_passage
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hL4 : ∃ bound, HasUniformSpacetimeL4Bound
      (data.existenceRoute μ T u0).compactness bound)
    (hCompact : HasLocallyStrongSubsequence
      (data.existenceRoute μ T u0).compactness) :
    HasNonlinearLimitPassage (data.existenceRoute μ T u0).compactness := by
  sorry

/-- WBK26 Step 4: all terms in (48), the initial trace, and the two energy spaces pass to the candidate limit. -/
@[proof_obligation]
theorem wbk26_step_4_limit_is_weak_solution
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T)
    (hExhaustion : HasSmoothExhaustion (data.existenceRoute μ T u0).compactness)
    (hInitial : HasInitialApproximation (data.existenceRoute μ T u0).compactness u0)
    (hDomains : HasCompactDomainSolutions (data.existenceRoute μ T u0).compactness)
    (hEnergy : ∃ bound, HasUniformEnergyBounds
      (data.existenceRoute μ T u0).compactness bound)
    (hNonlinear : HasNonlinearLimitPassage (data.existenceRoute μ T u0).compactness) :
    IsWeakNavierStokesSolutionOn data.equation μ T u0
      (data.existenceRoute μ T u0).compactness.candidateLimit := by
  sorry

/-- Existence assembled exactly from WBK26 proof Steps 1--4. -/
@[proof_assembly]
theorem wbk26_global_weak_solution_exists
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) :
    ∃ u : Trajectory, IsWeakNavierStokesSolutionOn data.equation μ T u0 u := by
  have hCoercivity := wbk26_deformation_coercivity data κ hGeometry
  have hLadyzhenskaya := wbk26_global_ladyzhenskaya data κ hGeometry
  have hExhaustion := wbk26_step_2_smooth_exhaustion data κ μ hGeometry hμ u0 T hT
  have hInitial := wbk26_step_2_initial_approximation data κ μ hGeometry hμ u0 T hT
  have hDomains := wbk26_step_2_compact_domain_galerkin data κ μ hGeometry hμ u0 T hT
  have hEnergy := wbk26_equation_46_uniform_energy data κ μ hGeometry hμ u0 T hT hCoercivity
  have hL4 := wbk26_step_3_uniform_l4 data κ μ hGeometry hμ u0 T hT hLadyzhenskaya hEnergy
  have hDt := wbk26_step_3_uniform_time_derivative data κ μ hGeometry hμ u0 T hT hL4
  have hTranslation := wbk26_equation_47_time_translation data κ μ hGeometry hμ u0 T hT hDt
  have hCompact := wbk26_step_3_local_strong_compactness data κ μ hGeometry hμ u0 T hT hEnergy hTranslation
  have hNonlinear := wbk26_equation_48_nonlinear_passage data κ μ hGeometry hμ u0 T hT hL4 hCompact
  exact ⟨(data.existenceRoute μ T u0).compactness.candidateLimit,
    wbk26_step_4_limit_is_weak_solution data κ μ hGeometry hμ u0 T hT
      hExhaustion hInitial hDomains hEnergy hNonlinear⟩

/-- WBK26 Step 4: the momentum residual annihilates compactly supported solenoidal tests. -/
@[proof_obligation]
theorem wbk26_momentum_residual_annihilates_solenoidal_tests
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (μ : ℝ)
    (u0 : H) (T : ℝ) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u) :
    data.residualAnnihilatesSolenoidalTests μ T u := by
  sorry

/-- De Rham pressure recovery from annihilation of compactly supported divergence-free tests. -/
@[proof_obligation]
theorem wbk26_de_rham_pressure_recovery
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u) :
    data.residualAnnihilatesSolenoidalTests μ T u →
    ∃ pressure : Pressure, data.equation.pressureRecoversMomentumOn μ T u pressure := by
  sorry

/-- Pressure recovery assembled from residual annihilation and the manifold de Rham theorem. -/
@[proof_assembly]
theorem wbk26_pressure_recovery
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u) :
    ∃ pressure : Pressure, data.equation.pressureRecoversMomentumOn μ T u pressure := by
  have hResidual := wbk26_momentum_residual_annihilates_solenoidal_tests data μ u0 T u hu
  exact wbk26_de_rham_pressure_recovery data κ μ hGeometry hμ u0 T hT u hu hResidual

/-- Remark 6.2: Ladyzhenskaya and Young give the absorbable difference-energy estimate. -/
@[proof_obligation]
theorem wbk26_difference_energy_estimate
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u candidate : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u)
    (hcandidate : IsWeakNavierStokesSolutionOn data.equation μ T u0 candidate)
    (hLadyzhenskaya : wbk26LadyzhenskayaStatement data) :
    data.hasDifferenceEnergyEstimate μ T u0 u candidate := by
  sorry

/-- Remark 6.2: Gronwall applied to the difference estimate forces equality. -/
@[proof_obligation]
theorem wbk26_difference_gronwall
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u candidate : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u)
    (hcandidate : IsWeakNavierStokesSolutionOn data.equation μ T u0 candidate)
    (hDifference : data.hasDifferenceEnergyEstimate μ T u0 u candidate) :
    candidate = u := by
  sorry

/-- Uniqueness assembled from the two explicit steps in Remark 6.2. -/
@[proof_assembly]
theorem wbk26_weak_solution_unique
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u) :
    IsUniqueWeakNavierStokesSolutionOn data.equation μ T u0 u := by
  intro candidate hCandidate
  have hLadyzhenskaya := wbk26_global_ladyzhenskaya data κ hGeometry
  have hDifference := wbk26_difference_energy_estimate data κ μ hGeometry hμ u0 T hT
    u candidate hu hCandidate hLadyzhenskaya
  exact wbk26_difference_gronwall data κ μ hGeometry hμ u0 T hT u candidate hu
    hCandidate hDifference


end RiemannianFluids
