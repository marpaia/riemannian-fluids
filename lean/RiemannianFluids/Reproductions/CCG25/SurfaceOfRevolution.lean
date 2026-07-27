import RiemannianFluids.Reproductions.CCG25.MainFormulas

/-! # CCG25 Section 4: surface-of-revolution formulas -/

namespace RiemannianFluids

/-- Section 4 input: specialize Corollary 1.24 to the adapted surface-of-revolution frame. -/
@[proof_obligation]
theorem ccg25_corollary_1_24_surface_of_revolution_specialization
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form)
    (hSurface : data.isSurfaceOfRevolutionInR3)
    (hTransverse : data.everyRadialLineIsTransverse)
    (hGradient : 0 < data.definingGradientNorm) :
    data.hasCorollary1_24ProjectedIdentity := by
  sorry

/-- Proposition 4.1: compute the adapted-frame connection coefficients and the derivatives of `|nabla rho|`. -/
@[proof_obligation]
theorem ccg25_proposition_4_1_surface_connection_coefficients
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form)
    (hSurface : data.isSurfaceOfRevolutionInR3)
    (hTransverse : data.everyRadialLineIsTransverse)
    (hGradient : 0 < data.definingGradientNorm)
    (hLieComponents : data.preliminaries.hasLieDerivativeComponentIdentity) :
    data.hasProposition4_1ConnectionIdentities := by
  sorry

/-- Theorem 1.27 coefficient computation after inserting Proposition 4.1 into equation (1.37). -/
@[proof_obligation]
theorem ccg25_theorem_1_27_coefficient_computation
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form)
    (hSurface : data.isSurfaceOfRevolutionInR3)
    (hTransverse : data.everyRadialLineIsTransverse)
    (hGradient : 0 < data.definingGradientNorm)
    (hProjected : data.hasCorollary1_24ProjectedIdentity)
    (hConnection : data.hasProposition4_1ConnectionIdentities) :
    ∀ form,
      data.isSurfaceDivergenceFree form →
      data.isAmbientDivergenceFree form →
        data.restrictedAmbientHodge form =
          data.intrinsicHodge form - data.doubleNormalLie form +
            (data.firstPrincipalCurvature - data.secondPrincipalCurvature) •
              data.normalLie form +
            (1 / data.definingGradientNorm ^ 2) • data.meridionalLie form +
            (2 * (data.secondPrincipalCurvature - data.firstPrincipalCurvature) *
                data.normalLieMeridionalComponent form -
              2 * (data.meridionalGradientDerivative /
                  data.definingGradientNorm) ^ 2 * data.meridionalComponent form) •
              data.meridionalCovector := by
  sorry

@[literature_terminal]
theorem ccg25_theorem_1_27_surface_of_revolution
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form) :
    ccg25SurfaceOfRevolutionLieFormulaStatement data := by
  intro hSurface hTransverse hGradient
  have hProjected :=
    ccg25_corollary_1_24_surface_of_revolution_specialization data hSurface
      hTransverse hGradient
  have hOneFormDerivative := ccg25_lemma_2_5_one_form_derivative data.preliminaries
  have hLieComponents :=
    ccg25_corollary_2_6_lie_derivative_components data.preliminaries hOneFormDerivative
  have hConnection :=
    ccg25_proposition_4_1_surface_connection_coefficients data hSurface
      hTransverse hGradient hLieComponents
  exact ccg25_theorem_1_27_coefficient_computation data hSurface hTransverse
    hGradient hProjected hConnection

/-- Corollary 1.30: regroup equation (1.41) into the operator `E`, retaining the two distinct powers of `|nabla rho|`. -/
@[proof_obligation]
theorem ccg25_corollary_1_30_operator_rewrite
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form)
    (hTheorem : ccg25SurfaceOfRevolutionLieFormulaStatement data) :
    ccg25SurfaceOfRevolutionComparisonStatement data := by
  sorry

@[literature_terminal]
theorem ccg25_corollary_1_30_surface_comparison
    {Form : Type*} [AddCommGroup Form] [Module ℝ Form]
    (data : CCG25SurfaceOfRevolutionData Form) :
    ccg25SurfaceOfRevolutionComparisonStatement data := by
  have hTheorem := ccg25_theorem_1_27_surface_of_revolution data
  exact ccg25_corollary_1_30_operator_rewrite data hTheorem


end RiemannianFluids
