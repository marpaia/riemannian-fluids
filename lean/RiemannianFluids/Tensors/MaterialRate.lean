import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import RiemannianFluids.Tensors.LieDerivative

/-!
# Material metric rate along a particle trajectory

The flow-free formula for the metric Lie derivative is useful algebraically, but the kinematic
argument for deformation strain begins with an actual material derivative.  This module supplies
that first-order bridge.  A particle trajectory is an integral curve of the velocity field, and
two differentiable connecting fields are Lie-dragged at the observation point when their Lie
brackets with the velocity vanish there.

For such data, the scalar curve

    t ↦ g(X(γ(t)), Y(γ(t)))

has the manifold differential obtained by composing the differential of `g(X,Y)` with the
integral-curve velocity.  Its scalar material rate is therefore `u(g(X,Y))`; the Lie-drag
conditions identify this rate with `L_u g`.  The construction is pointwise and does not assert
global existence of the velocity flow.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The scalar inner product observed along a material trajectory. -/
noncomputable def materialInnerProduct
    (trajectory : ℝ → M) (first second : (y : M) → TangentSpace I y) : ℝ → ℝ :=
  fun t ↦ inner ℝ (first (trajectory t)) (second (trajectory t))

/-- The directional rate `u(g(X,Y))` of the metric pairing at a point.  The theorem
`hasMFDerivAt_materialInnerProduct_of_integralCurve` below proves that this directional
differential is the coefficient represented by an actual material trajectory. -/
noncomputable def materialMetricRateAt
    (velocity first second : (y : M) → TangentSpace I y) (x : M) : ℝ :=
  d% (fun y ↦ inner ℝ (first y) (second y)) x (velocity x)

/-- The first-order data used by the Lagrangian strain calculation at `x`.

The trajectory is an actual integral curve through `x`.  The two connecting fields are
differentiable at `x` and Lie-dragged there, expressed intrinsically by vanishing Lie brackets
with the velocity. -/
structure MaterialConnectingPairJetAt
    (velocity : (y : M) → TangentSpace I y) (x : M) where
  trajectory : ℝ → M
  trajectory_zero : trajectory 0 = x
  isIntegralCurveAt : IsMIntegralCurveAt trajectory velocity 0
  first : (y : M) → TangentSpace I y
  second : (y : M) → TangentSpace I y
  first_mdifferentiableAt : MDiffAt (T% first) x
  second_mdifferentiableAt : MDiffAt (T% second) x
  first_lieDraggedAt : VectorField.mlieBracket I velocity first x = 0
  second_lieDraggedAt : VectorField.mlieBracket I velocity second x = 0

/-- Chain rule for the inner product along an actual integral curve.  The displayed differential
is the precise manifold form of

`d/dt|_0 g(X(γ(t)),Y(γ(t))) = d(g(X,Y))_x(u_x)`.

The rightmost map sends a time tangent `a` to `a • u_x`; the left map is the differential of
the scalar metric pairing. -/
theorem hasMFDerivAt_materialInnerProduct_of_integralCurve
    {velocity first second : (y : M) → TangentSpace I y} {x : M}
    {trajectory : ℝ → M}
    (hzero : trajectory 0 = x)
    (htrajectory : IsMIntegralCurveAt trajectory velocity 0)
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    HasMFDerivAt%
      (materialInnerProduct I trajectory first second) (0 : ℝ)
      ((mfderiv I (modelWithCornersSelf ℝ ℝ)
          (fun y ↦ inner ℝ (first y) (second y)) x).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (velocity x))) := by
  subst x
  let pair : M → ℝ := fun y ↦ inner ℝ (first y) (second y)
  have hpair : MDiffAt pair (trajectory 0) :=
    MDifferentiableAt.inner_bundle
      (F := E) (E := (TangentSpace I : M → Type _)) hfirst hsecond
  have hcurve := htrajectory.hasMFDerivAt
  have hcomp := HasMFDerivAt.comp (g := pair) (f := trajectory) (x := (0 : ℝ))
    hpair.hasMFDerivAt hcurve
  change HasMFDerivAt% (pair ∘ trajectory) (0 : ℝ)
    ((mfderiv% pair (trajectory 0)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (velocity (trajectory 0))))
  exact hcomp

/-- A material connecting-pair jet supplies the actual trajectory derivative of its metric
pairing. -/
theorem MaterialConnectingPairJetAt.hasMFDerivAt_materialInnerProduct
    {velocity : (y : M) → TangentSpace I y} {x : M}
    (data : MaterialConnectingPairJetAt I velocity x) :
    HasMFDerivAt%
      (materialInnerProduct I data.trajectory data.first data.second) (0 : ℝ)
      ((mfderiv I (modelWithCornersSelf ℝ ℝ)
          (fun y ↦ inner ℝ (data.first y) (data.second y)) x).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (velocity x))) :=
  hasMFDerivAt_materialInnerProduct_of_integralCurve I
    data.trajectory_zero data.isIntegralCurveAt
    data.first_mdifferentiableAt data.second_mdifferentiableAt

omit [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Lie-dragged connecting fields turn the material metric rate into the metric Lie derivative. -/
theorem materialMetricRateAt_eq_metricLieDerivativeAt
    {velocity first second : (y : M) → TangentSpace I y} {x : M}
    (hfirst : VectorField.mlieBracket I velocity first x = 0)
    (hsecond : VectorField.mlieBracket I velocity second x = 0) :
    materialMetricRateAt I velocity first second x =
      metricLieDerivativeAt I velocity first second x := by
  simp [materialMetricRateAt, metricLieDerivativeAt, hfirst, hsecond]

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The material metric rate of a connecting-pair jet is its flow-free metric Lie derivative. -/
theorem MaterialConnectingPairJetAt.materialMetricRate_eq_metricLieDerivativeAt
    {velocity : (y : M) → TangentSpace I y} {x : M}
    (data : MaterialConnectingPairJetAt I velocity x) :
    materialMetricRateAt I velocity data.first data.second x =
      metricLieDerivativeAt I velocity data.first data.second x :=
  materialMetricRateAt_eq_metricLieDerivativeAt I
    data.first_lieDraggedAt data.second_lieDraggedAt

end RiemannianFluids
