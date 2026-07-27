import RiemannianFluids.Reproductions.WBK26.Section6Existence

/-! # WBK26 Section 6: energy equality and long-time decay -/

namespace RiemannianFluids

/-- Equation (43): testing by Steklov averages gives the energy equality. -/
@[proof_obligation]
theorem wbk26_equation_43_steklov_energy_equality
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u) :
    data.hasSteklovEnergyEquality μ T u0 u := by
  sorry

/-- Equation (44): equation (42) inserted into equation (43). -/
@[proof_obligation]
theorem wbk26_equation_44_differential_inequality
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u)
    (hCoercivity : wbk26DeformationCoercivityStatement data κ)
    (hEnergy : data.hasSteklovEnergyEquality μ T u0 u) :
    data.hasDifferentialEnergyInequality κ μ T u0 u := by
  sorry

/-- Equation (45): scalar Gronwall gives the sharp exponential rate. -/
@[proof_obligation]
theorem wbk26_equation_45_gronwall_decay
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hDifferential : data.hasDifferentialEnergyInequality κ μ T u0 u) :
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ‖data.equation.velocityAt u t‖ ^ 2 ≤
        Real.exp (-2 * μ * κ ^ 2 * t) * ‖u0‖ ^ 2 := by
  sorry

/-- Equations (43)--(45), assembled without skipping Steklov testing or the scalar Gronwall step. -/
@[proof_assembly]
theorem wbk26_exponential_energy_decay
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ μ : ℝ)
    (hGeometry : SatisfiesWBK26Geometry data.geometry κ) (hμ : 0 < μ)
    (u0 : H) (T : ℝ) (hT : 0 < T) (u : Trajectory)
    (hu : IsWeakNavierStokesSolutionOn data.equation μ T u0 u) :
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ‖data.equation.velocityAt u t‖ ^ 2 ≤
        Real.exp (-2 * μ * κ ^ 2 * t) * ‖u0‖ ^ 2 := by
  have hCoercivity := wbk26_deformation_coercivity data κ hGeometry
  have hEnergy := wbk26_equation_43_steklov_energy_equality data κ μ hGeometry hμ
    u0 T hT u hu
  have hDifferential := wbk26_equation_44_differential_inequality data κ μ hGeometry hμ
    u0 T hT u hu hCoercivity hEnergy
  exact wbk26_equation_45_gronwall_decay data κ μ hGeometry hμ u0 T hT u hDifferential

/-- WBK26 Theorem 6.1, assembled without an additional placeholder from the six named analytic obligations above. -/
@[literature_terminal]
theorem wbk26_theorem_6_1
    {M H V Pressure Trajectory : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup V]
    (data : WBK26Data M H V Pressure Trajectory) (κ : ℝ) :
    wbk26Theorem6_1Statement data κ := by
  intro hGeometry μ hμ u0 T hT
  obtain ⟨u, hu⟩ := wbk26_global_weak_solution_exists data κ μ hGeometry hμ u0 T hT
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · exact wbk26_pressure_recovery data κ μ hGeometry hμ u0 T hT u hu
  · exact wbk26_weak_solution_unique data κ μ hGeometry hμ u0 T hT u hu
  · exact wbk26_exponential_energy_decay data κ μ hGeometry hμ u0 T hT u hu


end RiemannianFluids
