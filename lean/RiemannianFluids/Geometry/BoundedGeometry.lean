import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Compactness.Compact
import RiemannianFluids.Geometry.Curvature
import RiemannianFluids.Geometry.Manifolds

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

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Bounded-geometry observables attached to an actual Mathlib Riemannian manifold. -/
structure BoundedRiemannianSurfaceData where
  curvature : RiemannianCurvatureData (I := I) (M := M)
  injectivityRadius : M → ℝ
  curvatureDerivativeNorm : ℕ → M → ℝ

/-- Complete, noncompact, intrinsically two-dimensional bounded geometry with uniformly negative
Gaussian curvature.  Metric completeness and noncompactness use Mathlib typeclasses; only the
missing injectivity-radius and curvature-derivative constructions are supplied as data. -/
def SatisfiesRiemannianWBK26Geometry
    [CompleteSpace M] [NoncompactSpace M] [IsSurfaceModel E]
    (data : BoundedRiemannianSurfaceData (I := I) (M := M))
    (gaussianCurvature : M → ℝ) (κ : ℝ) : Prop :=
  HasRiemannianSurfaceRicciIdentity I data.curvature gaussianCurvature ∧
    (∃ injectivityLower : ℝ,
      0 < injectivityLower ∧ ∀ x, injectivityLower ≤ data.injectivityRadius x) ∧
    (∀ order : ℕ,
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ x, data.curvatureDerivativeNorm order x ≤ bound) ∧
    0 < κ ∧
    ∀ x, gaussianCurvature x ≤ -(κ ^ 2)

/-- A first-class Mathlib-backed carrier for the geometric setting in WBK26 Theorem 6.1.
The actual manifold `M` is shared with the paper's PDE data; the model, manifold instances,
curvature tensor, injectivity radius, and curvature-derivative norms remain inspectable. -/
structure CompleteBoundedSurfaceProfile (M : Type*) where
  E : Type
  [normedAddCommGroupE : NormedAddCommGroup E]
  [normedSpaceE : NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E]
  [surfaceModelE : IsSurfaceModel E]
  H : Type
  [topologicalSpaceH : TopologicalSpace H]
  I : ModelWithCorners ℝ E H
  [metricSpaceM : MetricSpace M]
  [chartedSpaceM : ChartedSpace H M]
  [isManifoldM : IsManifold I 1 M]
  [completeSpaceM : CompleteSpace M]
  [noncompactSpaceM : NoncompactSpace M]
  boundedGeometry : BoundedRiemannianSurfaceData (I := I) (M := M)
  gaussianCurvature : M → ℝ

/--
The complete bounded-geometry, dimension-two, uniformly negative-curvature hypotheses immediately preceding WBK26 Theorem 6.1.

Bounded geometry is expanded into a uniform positive injectivity-radius lower bound and uniform bounds on every covariant curvature derivative. The
curvature parameter is positive and satisfies `K(x) <= -kappa^2` at every point.
-/
def SatisfiesWBK26Geometry {M : Type*}
    (profile : CompleteBoundedSurfaceProfile M) (κ : ℝ) : Prop :=
  letI := profile.normedAddCommGroupE
  letI := profile.normedSpaceE
  letI := profile.finiteDimensionalE
  letI := profile.surfaceModelE
  letI := profile.topologicalSpaceH
  letI := profile.metricSpaceM
  letI := profile.chartedSpaceM
  letI := profile.isManifoldM
  letI := profile.completeSpaceM
  letI := profile.noncompactSpaceM
  SatisfiesRiemannianWBK26Geometry profile.I profile.boundedGeometry
    profile.gaussianCurvature κ

end RiemannianFluids
