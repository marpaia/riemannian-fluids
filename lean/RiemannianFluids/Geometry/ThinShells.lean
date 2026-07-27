import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Tubular and Fermi-coordinate shell geometry -/

namespace RiemannianFluids

/-- Geometry of the parallel hypersurfaces `M_r` in a tubular neighborhood. -/
structure FermiShellGeometryData (Point Tangent Normal Shape Metric : Type*) where
  normalExponential : Point → ℝ → Point
  unitNormal : Point → Normal
  parallelMetric : ℝ → Metric
  parallelShapeOperator : ℝ → Shape
  jacobian : ℝ → Point → ℝ
  metricDerivative : ℝ → Metric
  shapeRiccatiDerivative : ℝ → Shape
  thicknessBelowReach : ℝ → Prop

/-- Two-wall traces and the normal/tangential splitting of a shell field. -/
structure ShellTraceData (BulkField SurfaceField NormalComponent : Type*) where
  tangentialTrace : Bool → BulkField → SurfaceField
  normalTrace : Bool → BulkField → NormalComponent
  surfaceAverage : BulkField → SurfaceField
  isBulkSolenoidal : BulkField → Prop
  isSurfaceSolenoidal : SurfaceField → Prop

/-- The shell limit is a two-parameter problem: first resolve the mesh, then send thickness to zero. -/
structure ShellDoubleLimitData where
  meshSize : ℕ → ℝ
  thickness : ℕ → ℝ
  discretizationError : ℕ → ℕ → ℝ
  thinLimitError : ℕ → ℝ

def HasSeparatedMeshAndThicknessLimits (data : ShellDoubleLimitData) : Prop :=
  (∀ thicknessIndex,
    Filter.Tendsto (data.discretizationError thicknessIndex) Filter.atTop (nhds 0)) ∧
  Filter.Tendsto data.thinLimitError Filter.atTop (nhds 0)

end RiemannianFluids
