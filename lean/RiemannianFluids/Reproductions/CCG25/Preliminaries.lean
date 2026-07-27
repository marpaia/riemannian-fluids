import RiemannianFluids.Reproductions.CCG25.Statements

/-! # CCG25 Sections 2--3: submanifold preliminaries and trace lemmas -/

namespace RiemannianFluids

/-- Proposition 2.1: the second fundamental form and shape operator are metric adjoints. -/
@[proof_obligation]
theorem ccg25_proposition_2_1_gauss_weingarten
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    data.hasGaussAndWeingartenDefinitions := by
  sorry

/-- Lemma 2.2: normal-frame derivatives are skew in their normal indices. -/
@[proof_obligation]
theorem ccg25_lemma_2_2_normal_frame_derivatives
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    data.hasNormalFrameDerivativeIdentity := by
  sorry

/-- Lemma 2.3: split the ambient derivative of an arbitrary extension into tangential and normal parts. -/
@[proof_obligation]
theorem ccg25_lemma_2_3_extension_derivative_splitting
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    data.hasExtensionDerivativeSplitting := by
  sorry

/-- Lemma 2.5: covariant differentiation commutes with metric duality in the form used for the Hodge corollary. -/
@[proof_obligation]
theorem ccg25_lemma_2_5_one_form_derivative
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    data.hasOneFormCovariantDerivativeIdentity := by
  sorry

/-- Corollary 2.6, equations (2.40)--(2.41): the components of the Lie derivative of a one-form. -/
@[proof_obligation]
theorem ccg25_corollary_2_6_lie_derivative_components
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector)
    (hOneFormDerivative : data.hasOneFormCovariantDerivativeIdentity) :
    data.hasLieDerivativeComponentIdentity := by
  sorry

/-- Lemma 2.8: use Corollary 2.6 to express the normal Lie derivative through the shape operator. -/
@[proof_obligation]
theorem ccg25_lemma_2_8_defining_function_shape
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector)
    (hLieComponents : data.hasLieDerivativeComponentIdentity) :
    data.hasDefiningFunctionShapeIdentity := by
  sorry

/-- Lemma 3.1: the frame trace identity used to expand the ambient rough Laplacian. -/
@[proof_obligation]
theorem ccg25_lemma_3_1_frame_trace
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    data.hasFrameTraceIdentity := by
  sorry

/-- Lemma 3.3: the mixed ambient-curvature trace is invariant under adapted-frame changes. -/
@[proof_obligation]
theorem ccg25_lemma_3_3_mixed_curvature_invariant
    {Vector : Type*} [AddCommGroup Vector]
    (data : CCG25LaplacianData Vector) :
    data.hasInvariantMixedCurvatureTrace := by
  sorry


end RiemannianFluids
