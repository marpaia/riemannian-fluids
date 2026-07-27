import RiemannianFluids.Reproductions.CC15.Section3

/-! # CC15 Section 4: negative-Ricci extensions -/

namespace RiemannianFluids

/-! ## Section 4: negative-Ricci extensions -/

/-- CC15 Corollary 4.1: finite Dirichlet integral implies the `L²`, `d`, and `d*` bounds under a strict negative Ricci upper bound. -/
@[proof_obligation]
theorem cc15_corollary_4_1_negative_ricci_l2_control
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isCompleteSimplyConnectedWithRicciUpperBound N a)
    (hSmooth : data.isSmoothVelocity velocity)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity) :
    data.exteriorDerivativeIsL2 velocity ∧
      data.isSquareIntegrable velocity ∧
      data.codifferentialIsL2 velocity ∧
      data.hasNegativeRicciL2Estimate N a velocity := by
  sorry

/-- CC15 Corollary 4.2: the integrated deformation identity becomes a coercive inequality on a complete manifold with negative Ricci upper bound. -/
@[proof_obligation]
theorem cc15_corollary_4_2_negative_ricci_deformation_inequality
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isCompleteWithRicciUpperBound N a)
    (hSmooth : data.isSmoothVelocity velocity)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity) :
    data.hasNegativeRicciDeformationInequality N a velocity := by
  sorry


end RiemannianFluids
