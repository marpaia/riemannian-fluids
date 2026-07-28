import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiemannianFluids.Geometry.Submanifolds

/-!
# Tubular and Fermi-coordinate shell geometry

Mathlib provides the tangent fibers and manifold derivatives used by this interface, but not a
general tubular-neighborhood or parallel-hypersurface theory.  These declarations expose the
additional geometric statements used by CCF25, CCY23, and WBS26.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

/-- Data of a normal-coordinate map around an immersed hypersurface.  Parallel transport is
kept explicit because Mathlib does not yet provide the normal exponential/tubular package needed
to synthesize it. -/
structure FermiTubularData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)) where
  fermiMap : M → ℝ → N
  unitNormal : ∀ x, TangentSpace I' (immersion.toFun x)
  normalTransport :
    ∀ (x : M) (r : ℝ),
      TangentSpace I' (immersion.toFun x) →L[ℝ] TangentSpace I' (fermiMap x r)
  parallelMetric :
    ℝ → ∀ x : M, TangentSpace I x → TangentSpace I x → ℝ
  parallelShapeOperator :
    ℝ → ∀ x : M, TangentSpace I x → TangentSpace I x
  ambientNormalCurvature :
    ℝ → ∀ x : M, TangentSpace I x → TangentSpace I x
  metricDerivative :
    ℝ → ∀ x : M, TangentSpace I x → TangentSpace I x → ℝ
  shapeDerivative :
    ℝ → ∀ x : M, TangentSpace I x → TangentSpace I x
  meanCurvature : ℝ → M → ℝ
  jacobian : ℝ → M → ℝ
  jacobianDerivative : ℝ → M → ℝ
  reach : ℝ

/-- Fermi radius zero is the original immersion. -/
def HasFermiBasepoint
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) : Prop :=
  ∀ x, geometry.fermiMap x 0 = immersion.toFun x

/-- The chosen normal has unit length and is orthogonal to the immersed tangent space. -/
def HasUnitOrthogonalFermiNormal
    [RiemannianBundle (fun x : N => TangentSpace I' x)]
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) : Prop :=
  (∀ x, ‖geometry.unitNormal x‖ = 1) ∧
    ∀ x tangent,
      inner ℝ (geometry.unitNormal x)
        (mfderiv I I' immersion.toFun x tangent) = 0

/-- The metric evolution formula in normal coordinates, with the sign convention encoded by
the displayed minus sign. -/
def HasParallelMetricEvolution
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) : Prop :=
  ∀ r x first second,
    geometry.metricDerivative r x first second =
      -2 * geometry.parallelMetric r x
        (geometry.parallelShapeOperator r x first) second

/-- Riccati evolution of the parallel shape operator. -/
def HasParallelShapeRiccatiEquation
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) : Prop :=
  ∀ r x tangent,
    geometry.shapeDerivative r x tangent =
      geometry.parallelShapeOperator r x
          (geometry.parallelShapeOperator r x tangent) +
        geometry.ambientNormalCurvature r x tangent

/-- Evolution of the tubular Jacobian by mean curvature. -/
def HasTubularJacobianEvolution
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) : Prop :=
  ∀ r x,
    geometry.jacobianDerivative r x =
      -geometry.meanCurvature r x * geometry.jacobian r x

/-- The coordinate map is one-to-one below its asserted reach. -/
def IsInjectiveBelowReach
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) : Prop :=
  0 < geometry.reach ∧
    ∀ r, |r| < geometry.reach → Function.Injective (fun x => geometry.fermiMap x r)

/-- A vector field on the normal-coordinate cylinder. -/
abbrev BulkShellVectorField
    {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}
    (geometry : FermiTubularData immersion) :=
  (x : M) → (r : ℝ) → TangentSpace I' (geometry.fermiMap x r)

/-- The paper-facing trace, pullback, and averaging operations for a tubular shell. -/
structure ShellTraceData
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (geometry : FermiTubularData immersion) where
  tangentialPullback :
    ∀ r, ((x : M) → TangentSpace I' (geometry.fermiMap x r)) →
      ((x : M) → TangentSpace I x)
  normalCoefficient :
    ∀ r, ((x : M) → TangentSpace I' (geometry.fermiMap x r)) → M → ℝ
  surfaceAverage : BulkShellVectorField geometry → ((x : M) → TangentSpace I x)
  isBulkSolenoidal : BulkShellVectorField geometry → Prop
  isSurfaceSolenoidal : ((x : M) → TangentSpace I x) → Prop

/-- The two wall traces of a shell field at signed thicknesses. -/
def ShellWallTraces
    {immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N)}
    {geometry : FermiTubularData immersion}
    (trace : ShellTraceData immersion geometry)
    (lower upper : ℝ) (field : BulkShellVectorField geometry) :=
  (trace.tangentialPullback lower (fun x => field x lower),
    trace.tangentialPullback upper (fun x => field x upper))

/-- The shell limit is a two-parameter problem: first resolve the mesh, then send thickness to
zero.  These are dimensionless real observables, so no additional geometric carrier is needed. -/
structure ShellDoubleLimitData where
  meshSize : ℕ → ℝ
  thickness : ℕ → ℝ
  discretizationError : ℕ → ℕ → ℝ
  thinLimitError : ℕ → ℝ

def HasSeparatedMeshAndThicknessLimits (data : ShellDoubleLimitData) : Prop :=
  (∀ thicknessIndex,
    Filter.Tendsto (data.discretizationError thicknessIndex) Filter.atTop (nhds 0)) ∧
  Filter.Tendsto data.thinLimitError Filter.atTop (nhds 0)

end

end RiemannianFluids
