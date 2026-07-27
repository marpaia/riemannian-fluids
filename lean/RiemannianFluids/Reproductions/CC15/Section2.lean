import Mathlib.Data.Real.Basic
import RiemannianFluids.ProofStatus

/-!
# CC15 hyperbolic Liouville proof graph

This module follows Chan--Czubak, arXiv:1501.04928v1, rather than compressing Theorem
1.1 into one dimension-by-dimension placeholder.  The named nodes below are exactly the
results used by the proof:

* Lemma 2.1 upgrades finite Dirichlet integral to `L2`, `d u in L2`, and `d* u in L2`;
* Lemma 2.2 is the integrated deformation identity (2.22);
* Lemma 2.3 supplies the dimension-dependent interpolation estimates;
* Lemma 2.4 and Theorem 2.5 supply the current/de Rham and solenoidal-`H1` decomposition;
* equations (3.3)--(3.10) justify testing by the velocity in dimensions at least three;
* equations (3.12)--(3.13) are the two-dimensional vorticity cutoff argument.

The declarations tagged `proof_obligation` are unfinished source steps and may invoke earlier
steps exactly when the proof does.  The branch theorems are sorry-free `proof_assembly` nodes,
so `lean/progress` displays the paper's dependency graph.
-/

namespace RiemannianFluids

/-- Observable geometry, equation, function-space gates, and conclusions for CC15. -/
structure CC15Data (Velocity Pressure Potential : Type*) where
  isHyperbolicSpace : ℕ → ℝ → Prop
  isSmoothVelocity : Velocity → Prop
  isSmoothPressure : Pressure → Prop
  isDivergenceFree : Velocity → Prop
  satisfiesStationaryDeformationNS : ℕ → ℝ → Velocity → Pressure → Prop
  satisfiesStationaryBochnerNS : ℕ → ℝ → Velocity → Pressure → Prop
  satisfiesStationaryHodgeNS : ℕ → ℝ → Velocity → Pressure → Prop
  hasFiniteDirichletIntegral : Velocity → Prop
  exteriorDerivativeIsL2 : Velocity → Prop
  codifferentialIsL2 : Velocity → Prop
  isEssentiallyBounded : Velocity → Prop
  isSquareIntegrable : Velocity → Prop
  liesInH10 : Velocity → Prop
  liesInSolenoidalH1Closure : Velocity → Prop
  hasDeformationIdentity : ℕ → ℝ → Velocity → Prop
  hasDimensionInterpolation : ℕ → Velocity → Prop
  hasCurrentCriterion : Prop
  hasH1InnerProductEquation2_40 : ℕ → ℝ → Velocity → Prop
  hasOrthogonalSplittingEquation2_41 : ℕ → ℝ → Velocity → Prop
  hasOrthogonalityEquation2_42 : ℕ → ℝ → Velocity → Prop
  hasWeitzenbockEquation2_43 : ℕ → ℝ → Velocity → Prop
  hasCurrentEquation2_44 : ℕ → ℝ → Velocity → Prop
  hasEllipticTwoFormEquation2_45 : ℕ → ℝ → Velocity → Prop
  hasCutoffTestEquation2_46 : ℕ → ℝ → Velocity → Prop
  hasCodifferentialExpansionEquation2_47 : ℕ → ℝ → Velocity → Prop
  hasCauchyEstimateEquation2_48 : ℕ → ℝ → Velocity → Prop
  hasCoerciveEstimateEquation2_49 : ℕ → ℝ → Velocity → Prop
  hasClosedComplementConclusion2_50 : ℕ → ℝ → Velocity → Prop
  pressureCancelsAgainstSolenoidalCore : Pressure → Prop
  hasTestedMomentumEquation : Velocity → Prop
  hasNonlinearEstimateEquation3_6 : Velocity → Prop
  nonlinearTermPassesToVelocityTest : Velocity → Prop
  hasVelocityTestEnergyIdentity : Velocity → Prop
  hasConvectionCancellation : Velocity → Prop
  hasZeroDeformationEnergy : Velocity → Prop
  hasVorticityEquation : ℝ → Velocity → Prop
  hasZeroVorticity : Velocity → Prop
  isZero : Velocity → Prop
  isHarmonicPotential : ℕ → ℝ → Potential → Prop
  isGradientOf : Velocity → Potential → Prop
  /-- Section 4's extension from space forms to complete manifolds with a negative Ricci upper bound. -/
  isCompleteSimplyConnectedWithRicciUpperBound : ℕ → ℝ → Prop
  isCompleteWithRicciUpperBound : ℕ → ℝ → Prop
  hasNegativeRicciL2Estimate : ℕ → ℝ → Velocity → Prop
  hasNegativeRicciDeformationInequality : ℕ → ℝ → Velocity → Prop

/-- CC15 Lemma 2.1, equations (2.1)--(2.2). -/
@[proof_obligation]
theorem cc15_lemma_2_1_from_dirichlet_to_l2
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hSmooth : data.isSmoothVelocity velocity)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity) :
    data.exteriorDerivativeIsL2 velocity ∧
      data.codifferentialIsL2 velocity ∧
      data.isSquareIntegrable velocity ∧
      data.liesInH10 velocity := by
  sorry

/-- CC15 Lemma 2.2, the cutoff-justified identity (2.22). -/
@[proof_obligation]
theorem cc15_lemma_2_2_deformation_identity
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hSmooth : data.isSmoothVelocity velocity)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity) :
    data.hasDeformationIdentity N a velocity := by
  sorry

/-- CC15 Lemma 2.3, equations (2.29)--(2.31), including the bounded high-dimensional branch. -/
@[proof_obligation]
theorem cc15_lemma_2_3_interpolation
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (velocity : Velocity)
    (hN : 2 ≤ N)
    (hL2 : data.isSquareIntegrable velocity)
    (hDirichlet : data.hasFiniteDirichletIntegral velocity)
    (hBoundedWhenNeeded : 5 ≤ N → data.isEssentiallyBounded velocity) :
    data.hasDimensionInterpolation N velocity := by
  sorry

/-- CC15 Lemma 2.4: a degree-one current annihilating compactly supported co-closed tests is exact. -/
@[proof_obligation]
theorem cc15_lemma_2_4_current_criterion
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential) :
    data.hasCurrentCriterion := by
  sorry

/-- CC15 equation (2.40): the co-closed `H¹₀` space carries the displayed Hilbert inner product. -/
@[proof_obligation]
theorem cc15_equation_2_40_h1_inner_product
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hH10 : data.liesInH10 velocity) :
    data.hasH1InnerProductEquation2_40 N a velocity := by
  sorry

/-- CC15 equation (2.41): split the Hilbert space from (2.40) as `V ⊕ V⊥`. -/
@[proof_obligation]
theorem cc15_equation_2_41_orthogonal_splitting
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hInnerProduct : data.hasH1InnerProductEquation2_40 N a velocity) :
    data.hasOrthogonalSplittingEquation2_41 N a velocity := by
  sorry

/-- CC15 equation (2.42): an element of `V⊥` is orthogonal to every compactly supported co-closed test. -/
@[proof_obligation]
theorem cc15_equation_2_42_test_orthogonality
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hSplitting : data.hasOrthogonalSplittingEquation2_41 N a velocity) :
    data.hasOrthogonalityEquation2_42 N a velocity := by
  sorry

/-- CC15 equation (2.43): the hyperbolic Weitzenbock identity rewrites the rough Laplacian on tests. -/
@[proof_obligation]
theorem cc15_equation_2_43_test_weizenbock
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hOrthogonality : data.hasOrthogonalityEquation2_42 N a velocity) :
    data.hasWeitzenbockEquation2_43 N a velocity := by
  sorry

/-- CC15 equation (2.44): Lemma 2.4 converts the current annihilating co-closed tests into a pressure current. -/
@[proof_obligation]
theorem cc15_equation_2_44_current_pressure
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hWeitzenbock : data.hasWeitzenbockEquation2_43 N a velocity)
    (hCurrentCriterion : data.hasCurrentCriterion) :
    data.hasCurrentEquation2_44 N a velocity := by
  sorry

/-- CC15 equation (2.45): exterior differentiation gives the elliptic equation for `omega = dv`. -/
@[proof_obligation]
theorem cc15_equation_2_45_elliptic_two_form
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hCurrentEquation : data.hasCurrentEquation2_44 N a velocity) :
    data.hasEllipticTwoFormEquation2_45 N a velocity := by
  sorry

/-- CC15 equation (2.46): test the elliptic two-form equation against `omega * phi_R^2`. -/
@[proof_obligation]
theorem cc15_equation_2_46_cutoff_test
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hElliptic : data.hasEllipticTwoFormEquation2_45 N a velocity) :
    data.hasCutoffTestEquation2_46 N a velocity := by
  sorry

/-- CC15 equation (2.47): expand the codifferential term in the cutoff identity. -/
@[proof_obligation]
theorem cc15_equation_2_47_codifferential_expansion
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hCutoffTest : data.hasCutoffTestEquation2_46 N a velocity) :
    data.hasCodifferentialExpansionEquation2_47 N a velocity := by
  sorry

/-- CC15 equation (2.48): Cauchy's inequality controls the cutoff cross term. -/
@[proof_obligation]
theorem cc15_equation_2_48_cauchy_estimate
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hExpansion : data.hasCodifferentialExpansionEquation2_47 N a velocity) :
    data.hasCauchyEstimateEquation2_48 N a velocity := by
  sorry

/-- CC15 equation (2.49): insert (2.47)--(2.48) into (2.46) to obtain the coercive cutoff estimate. -/
@[proof_obligation]
theorem cc15_equation_2_49_coercive_cutoff_estimate
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hCutoffTest : data.hasCutoffTestEquation2_46 N a velocity)
    (hExpansion : data.hasCodifferentialExpansionEquation2_47 N a velocity)
    (hCauchy : data.hasCauchyEstimateEquation2_48 N a velocity) :
    data.hasCoerciveEstimateEquation2_49 N a velocity := by
  sorry

/-- CC15 equation (2.50): let the cutoff radius tend to infinity to force `omega = dv = 0`. -/
@[proof_obligation]
theorem cc15_equation_2_50_closed_complement
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hCoercive : data.hasCoerciveEstimateEquation2_49 N a velocity) :
    data.hasClosedComplementConclusion2_50 N a velocity := by
  sorry

/-- CC15 Theorem 2.5's final paragraph: classify the closed `L²` complement by dimension. -/
@[proof_obligation]
theorem cc15_theorem_2_5_harmonic_complement_classification
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hH10 : data.liesInH10 velocity)
    (hClosedComplement : data.hasClosedComplementConclusion2_50 N a velocity) :
    (3 ≤ N → data.liesInSolenoidalH1Closure velocity) ∧
      (N = 2 →
        data.liesInSolenoidalH1Closure velocity ∨
          ∃ potential,
            data.isHarmonicPotential N a potential ∧
              data.isGradientOf velocity potential) := by
  sorry

/-- CC15 Theorem 2.5, equations (2.38)--(2.50), assembled in the order of its proof. -/
@[proof_assembly]
theorem cc15_theorem_2_5_solenoidal_h1_decomposition
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity)
    (hN : 2 ≤ N) (ha : 0 < a)
    (hGeometry : data.isHyperbolicSpace N a)
    (hDivergenceFree : data.isDivergenceFree velocity)
    (hH10 : data.liesInH10 velocity)
    (hCurrentCriterion : data.hasCurrentCriterion) :
    (3 ≤ N → data.liesInSolenoidalH1Closure velocity) ∧
      (N = 2 →
        data.liesInSolenoidalH1Closure velocity ∨
          ∃ potential,
            data.isHarmonicPotential N a potential ∧
              data.isGradientOf velocity potential) := by
  have hInnerProduct := cc15_equation_2_40_h1_inner_product data N a velocity
    hN ha hGeometry hDivergenceFree hH10
  have hSplitting := cc15_equation_2_41_orthogonal_splitting data N a velocity hInnerProduct
  have hOrthogonality := cc15_equation_2_42_test_orthogonality data N a velocity hSplitting
  have hWeitzenbock := cc15_equation_2_43_test_weizenbock data N a velocity hOrthogonality
  have hCurrent := cc15_equation_2_44_current_pressure data N a velocity
    hWeitzenbock hCurrentCriterion
  have hElliptic := cc15_equation_2_45_elliptic_two_form data N a velocity hCurrent
  have hCutoffTest := cc15_equation_2_46_cutoff_test data N a velocity hElliptic
  have hExpansion := cc15_equation_2_47_codifferential_expansion data N a velocity hCutoffTest
  have hCauchy := cc15_equation_2_48_cauchy_estimate data N a velocity hExpansion
  have hCoercive := cc15_equation_2_49_coercive_cutoff_estimate data N a velocity
    hCutoffTest hExpansion hCauchy
  have hClosed := cc15_equation_2_50_closed_complement data N a velocity hCoercive
  exact cc15_theorem_2_5_harmonic_complement_classification data N a velocity hN ha
    hGeometry hDivergenceFree hH10 hClosed


end RiemannianFluids
