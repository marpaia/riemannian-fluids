import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Sets.Opens

/-!
# Real-analytic neighborhoods and local inverse charts

This module is the Mathlib-backed analytic layer used by the thin-shell appendices.  It keeps
real analyticity, local inverse charts, and finite compact globalization outside any individual
paper reproduction.
-/

namespace RiemannianFluids

noncomputable section

/-- Euclidean three-space with its Mathlib normed-space structure. -/
abbrev EuclideanThreeSpace := EuclideanSpace ℝ (Fin 3)

/-- Euclidean two-space, used as the parameter domain for surface charts. -/
abbrev EuclideanTwoSpace := EuclideanSpace ℝ (Fin 2)

/-- The defining radial function for the axisymmetric ellipsoid
`x² / a² + y² / a² + z² = 1`. -/
def axisymmetricEllipsoidRadius (axis : ℝ) (point : EuclideanThreeSpace) : ℝ :=
  Real.sqrt
    (point 0 ^ 2 / axis ^ 2 + point 1 ^ 2 / axis ^ 2 + point 2 ^ 2)

/-- The open radial neighborhood used in CCF25 equation (A.1). -/
def radialEllipsoidNeighborhood (axis radius : ℝ) : Set EuclideanThreeSpace :=
  {point |
    1 - radius < axisymmetricEllipsoidRadius axis point ∧
      axisymmetricEllipsoidRadius axis point < 1 + radius}

/-- Componentwise Mathlib real analyticity of a Euclidean vector field on a neighborhood. -/
def IsRealAnalyticVectorFieldOn
    (field : EuclideanThreeSpace → EuclideanThreeSpace)
    (domain : Set EuclideanThreeSpace) : Prop :=
  ∀ component : Fin 3,
    AnalyticOnNhd ℝ (fun point => field point component) domain

/-- Componentwise Mathlib real analyticity of a Euclidean parametrization. -/
def IsRealAnalyticParametrizationOn
    {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (parametrization : Parameter → EuclideanThreeSpace)
    (domain : Set Parameter) : Prop :=
  ∀ component : Fin 3,
    AnalyticOnNhd ℝ (fun parameter => parametrization parameter component) domain

/-- A local Euclidean surface parametrization with its actual open parameter domain. -/
structure RealAnalyticSurfaceChart where
  domain : Set EuclideanTwoSpace
  toFun : EuclideanTwoSpace → EuclideanThreeSpace

/-- The chart domain is open and all three coordinate functions are real analytic there. -/
def IsRealAnalyticSurfaceChart (chart : RealAnalyticSurfaceChart) : Prop :=
  IsOpen chart.domain ∧ IsRealAnalyticParametrizationOn chart.toFun chart.domain

/-- A point is covered by a surface chart when it is the image of a parameter in its domain. -/
def RealAnalyticSurfaceChart.Covers
    (chart : RealAnalyticSurfaceChart) (point : EuclideanThreeSpace) : Prop :=
  ∃ parameter ∈ chart.domain, chart.toFun parameter = point

/-- The hypotheses under which Mathlib's analytic inverse theorem applies to a local chart. -/
def HasInvertibleRealAnalyticDerivativeAt
    {Domain Range : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Range] [NormedSpace ℝ Range] [CompleteSpace Range]
    (chart : OpenPartialHomeomorph Domain Range) (point : Domain)
    (derivative : Domain ≃L[ℝ] Range) : Prop :=
  point ∈ chart.source ∧
    AnalyticAt ℝ chart point ∧
      fderiv ℝ chart point = derivative

/-- The inverse chart is real analytic at the image point. -/
def HasRealAnalyticInverseAt
    {Domain Range : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Range] [NormedSpace ℝ Range] [CompleteSpace Range]
    (chart : OpenPartialHomeomorph Domain Range) (point : Domain) : Prop :=
  AnalyticAt ℝ chart.symm (chart point)

/-- Mathlib's analytic inverse theorem, exposed with the exact hypotheses consumed by the
thin-shell radial-chart argument. -/
theorem realAnalyticInverseAt_of_invertibleDerivative
    {Domain Range : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Range] [NormedSpace ℝ Range] [CompleteSpace Range]
    (chart : OpenPartialHomeomorph Domain Range) (point : Domain)
    (derivative : Domain ≃L[ℝ] Range)
    (hypotheses : HasInvertibleRealAnalyticDerivativeAt chart point derivative) :
    HasRealAnalyticInverseAt chart point := by
  exact chart.analyticAt_symm' hypotheses.1 hypotheses.2.1 hypotheses.2.2

/-- A finite subfamily covers the compact source set.  This is the topological globalization
step used after constructing analytic expansions chart by chart. -/
def HasFiniteSubcover
    {Point Index : Type*} [TopologicalSpace Point]
    (source : Set Point) (cover : Index → Set Point) : Prop :=
  ∃ finite : Finset Index,
    ∀ point ∈ source, ∃ index ∈ finite, point ∈ cover index

theorem finiteSubcover_of_compact_openCover
    {Point Index : Type*} [TopologicalSpace Point]
    (source : Set Point) (cover : Index → Set Point)
    (compact : IsCompact source)
    (openCover : ∀ index, IsOpen (cover index))
    (covers : ∀ point ∈ source, ∃ index, point ∈ cover index) :
    HasFiniteSubcover source cover := by
  have covered : source ⊆ ⋃ index, cover index := by
    intro point hpoint
    rcases covers point hpoint with ⟨index, hindex⟩
    exact Set.mem_iUnion.2 ⟨index, hindex⟩
  rcases compact.elim_finite_subcover cover openCover covered with ⟨finite, hfinite⟩
  refine ⟨finite, ?_⟩
  intro point hpoint
  simpa only [Set.mem_iUnion, exists_prop] using hfinite hpoint

end

end RiemannianFluids
