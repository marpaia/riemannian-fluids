import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounded geometry and negative-curvature contracts

Wang--Braunstein, arXiv:2605.17502v2, Theorem 6.1 assumes a complete noncompact two-dimensional Riemannian manifold of bounded geometry whose Gaussian
curvature satisfies `K <= -kappa^2 < 0`.

Mathlib does not currently expose the full injectivity-radius and covariant-curvature-derivative package needed by that sentence. This module therefore
records the exact observable profile that a later concrete Riemannian construction must supply. It deliberately contains no PDE conclusion and no
postulated theorem: the profile consists only of the quantities occurring in the geometric hypotheses, and `SatisfiesWBK26Geometry` states their
required bounds.

The profile is a permanent interface boundary. Replacing its fields by unconstrained booleans would lose mathematical content; bundling the actual
radius and derivative-norm functions lets a future manifold instance prove the displayed inequalities without changing downstream theorem statements.
-/

namespace RiemannianFluids

/-- The geometric observables required by the bounded-geometry hypothesis in WBK26 Theorem 6.1. -/
structure CompleteBoundedSurfaceProfile (M : Type*) where
  /-- Gaussian curvature `K : M -> R`. -/
  gaussianCurvature : M → ℝ
  /-- Pointwise injectivity radius. -/
  injectivityRadius : M → ℝ
  /-- Norm of the indicated covariant derivative of curvature at a point. -/
  curvatureDerivativeNorm : ℕ → M → ℝ
  /-- The concrete predicate expressing geodesic completeness for the eventual Riemannian realization. -/
  geodesicallyComplete : Prop
  /-- The concrete predicate expressing noncompactness for the eventual manifold realization. -/
  noncompact : Prop
  /-- Intrinsic manifold dimension. -/
  intrinsicDimension : ℕ

/--
The complete bounded-geometry, dimension-two, uniformly negative-curvature hypotheses immediately preceding WBK26 Theorem 6.1.

Bounded geometry is expanded into a uniform positive injectivity-radius lower bound and uniform bounds on every covariant curvature derivative. The
curvature parameter is positive and satisfies `K(x) <= -kappa^2` at every point.
-/
def SatisfiesWBK26Geometry {M : Type*} (profile : CompleteBoundedSurfaceProfile M) (κ : ℝ) : Prop :=
  profile.geodesicallyComplete ∧
    profile.noncompact ∧
    profile.intrinsicDimension = 2 ∧
    (∃ injectivityLower : ℝ, 0 < injectivityLower ∧ ∀ x, injectivityLower ≤ profile.injectivityRadius x) ∧
    (∀ order : ℕ, ∃ bound : ℝ, 0 ≤ bound ∧ ∀ x, profile.curvatureDerivativeNorm order x ≤ bound) ∧
    0 < κ ∧
    ∀ x, profile.gaussianCurvature x ≤ -(κ ^ 2)

end RiemannianFluids
