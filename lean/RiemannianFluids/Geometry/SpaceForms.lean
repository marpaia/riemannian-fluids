import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import RiemannianFluids.Geometry.Curvature

/-!
# Hyperbolic and constant-curvature geometry contracts

This module owns the common geometric hypotheses used in CC13, CC15, CC21, and CCP25.
The paper notation `H^N(-a^2)` is expanded into dimension, completeness, simple connectivity,
absence of boundary, and the pointwise sectional-curvature value.  Pinched negative curvature
is kept separate because CC13 first proves several estimates in the more general range
`-b^2 <= K <= -a^2` before specializing to the space form.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

/-- Mathlib-backed geometric setting for `H^N(-a²)` before Cartan--Hadamard is used to infer
noncompactness.  The nonnegative parameter convention includes the flat case `a = 0`. -/
def IsRiemannianNonpositiveSpaceFormSetting
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [CompleteSpace M] [SimplyConnectedSpace M] [BoundarylessManifold I M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (curvature : RiemannianCurvatureData (I := I) (M := M))
    (dimension : ℕ) (scale : ℝ) : Prop :=
  1 ≤ dimension ∧
    0 ≤ scale ∧
    Module.finrank ℝ E = dimension ∧
    HasRiemannianConstantSectionalCurvature I curvature (-(scale ^ 2))

/-- A first-class carrier for the full Mathlib-backed geometry denoted by `H^N(-a²)`
when the paper allows the flat case `a = 0`.  Keeping the carrier types, instances,
curvature data, and defining proposition together lets paper-level operator packages refer
to real manifold geometry without acquiring dozens of ambient type parameters. -/
structure RiemannianNonpositiveSpaceFormData where
  E : Type
  [normedAddCommGroupE : NormedAddCommGroup E]
  [normedSpaceE : NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E]
  H : Type
  [topologicalSpaceH : TopologicalSpace H]
  I : ModelWithCorners ℝ E H
  M : Type
  [metricSpaceM : MetricSpace M]
  [chartedSpaceM : ChartedSpace H M]
  [isManifoldM : IsManifold I 1 M]
  [completeSpaceM : CompleteSpace M]
  [simplyConnectedSpaceM : SimplyConnectedSpace M]
  [boundarylessManifoldM : BoundarylessManifold I M]
  [riemannianBundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  curvature : RiemannianCurvatureData (I := I) (M := M)
  dimension : ℕ
  scale : ℝ
  satisfies : IsRiemannianNonpositiveSpaceFormSetting I curvature dimension scale

/-- Re-expose the defining proposition after installing the first-class witness's stored
Mathlib instances. -/
def RiemannianNonpositiveSpaceFormData.hasExpectedGeometry
    (data : RiemannianNonpositiveSpaceFormData) : Prop :=
  letI := data.normedAddCommGroupE
  letI := data.normedSpaceE
  letI := data.finiteDimensionalE
  letI := data.topologicalSpaceH
  letI := data.metricSpaceM
  letI := data.chartedSpaceM
  letI := data.isManifoldM
  letI := data.completeSpaceM
  letI := data.simplyConnectedSpaceM
  letI := data.boundarylessManifoldM
  letI := data.riemannianBundleM
  IsRiemannianNonpositiveSpaceFormSetting data.I data.curvature data.dimension data.scale

/-- The exact Mathlib-backed space-form setting behind the notation `H^N(-a²)`.  Completeness,
simple connectivity, noncompactness, and absence of boundary are expressed by Mathlib
typeclasses; the repository only supplies the curvature operations still missing from the
manifold API. -/
def IsRiemannianHyperbolicSpaceForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [CompleteSpace M] [SimplyConnectedSpace M] [NoncompactSpace M]
    [BoundarylessManifold I M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (curvature : RiemannianCurvatureData (I := I) (M := M))
    (dimension : ℕ) (scale : ℝ) : Prop :=
  IsRiemannianNonpositiveSpaceFormSetting I curvature dimension scale ∧
    2 ≤ dimension ∧ 0 < scale ∧
    (∀ x vector,
      curvature.ricciAction x vector =
        (-((dimension - 1 : ℕ) : ℝ) * scale ^ 2) • vector) ∧
    ∀ x,
      curvature.scalarCurvature x =
        -((dimension * (dimension - 1) : ℕ) : ℝ) * scale ^ 2

/-- A first-class Mathlib manifold witness for a complete, simply connected, noncompact,
boundaryless Riemannian manifold on the specified point carrier. -/
structure RiemannianHadamardManifoldData (M : Type*) where
  E : Type
  [normedAddCommGroupE : NormedAddCommGroup E]
  [normedSpaceE : NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E]
  H : Type
  [topologicalSpaceH : TopologicalSpace H]
  I : ModelWithCorners ℝ E H
  [metricSpaceM : MetricSpace M]
  [chartedSpaceM : ChartedSpace H M]
  [isManifoldM : IsManifold I 1 M]
  [completeSpaceM : CompleteSpace M]
  [simplyConnectedSpaceM : SimplyConnectedSpace M]
  [noncompactSpaceM : NoncompactSpace M]
  [boundarylessManifoldM : BoundarylessManifold I M]
  [riemannianBundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  curvature : RiemannianCurvatureData (I := I) (M := M)

/-- Observable geometry for a complete Riemannian manifold.  Global topological and metric
hypotheses are carried by actual Mathlib instances; only scalarized quantities consumed by the
source estimates remain explicit observables. -/
structure RiemannianGeometryProfile (Point : Type*) where
  globalGeometry : RiemannianHadamardManifoldData Point
  intrinsicDimension : ℕ
  sectionalCurvature : Point → ℝ
  ricciEigenvalue : Point → ℝ
  scalarCurvature : Point → ℝ
  distanceFromBasepoint : Point → ℝ
  injectivityRadius : Point → ℝ

def RiemannianGeometryProfile.geodesicallyComplete
    {Point : Type*} (profile : RiemannianGeometryProfile Point) : Prop :=
  letI := profile.globalGeometry.metricSpaceM
  CompleteSpace Point

def RiemannianGeometryProfile.simplyConnected
    {Point : Type*} (profile : RiemannianGeometryProfile Point) : Prop :=
  letI := profile.globalGeometry.metricSpaceM
  SimplyConnectedSpace Point

def RiemannianGeometryProfile.noncompact
    {Point : Type*} (profile : RiemannianGeometryProfile Point) : Prop :=
  letI := profile.globalGeometry.metricSpaceM
  NoncompactSpace Point

def RiemannianGeometryProfile.withoutBoundary
    {Point : Type*} (profile : RiemannianGeometryProfile Point) : Prop :=
  letI := profile.globalGeometry.normedAddCommGroupE
  letI := profile.globalGeometry.normedSpaceE
  letI := profile.globalGeometry.finiteDimensionalE
  letI := profile.globalGeometry.topologicalSpaceH
  letI := profile.globalGeometry.metricSpaceM
  letI := profile.globalGeometry.chartedSpaceM
  letI := profile.globalGeometry.isManifoldM
  BoundarylessManifold profile.globalGeometry.I Point

/-- The exact space-form geometry `H^N(-a^2)` used by the Czubak papers. -/
def IsHyperbolicSpaceForm
    {Point : Type*}
    (profile : RiemannianGeometryProfile Point) (N : ℕ) (a : ℝ) : Prop :=
  2 ≤ N ∧
    0 < a ∧
    profile.intrinsicDimension = N ∧
    profile.geodesicallyComplete ∧
    profile.simplyConnected ∧
    profile.noncompact ∧
    profile.withoutBoundary ∧
    (∀ point, profile.sectionalCurvature point = -(a ^ 2)) ∧
    (∀ point, profile.ricciEigenvalue point = -((N - 1 : ℕ) : ℝ) * a ^ 2) ∧
    ∀ point, profile.scalarCurvature point =
      -((N * (N - 1) : ℕ) : ℝ) * a ^ 2

/-- The pinched-curvature setting `-b^2 <= K <= -a^2` used in CC13 Theorem 1.6. -/
def HasPinchedNegativeCurvature
    {Point : Type*}
    (profile : RiemannianGeometryProfile Point) (a b : ℝ) : Prop :=
  0 < a ∧ a ≤ b ∧
    ∀ point, -(b ^ 2) ≤ profile.sectionalCurvature point ∧
      profile.sectionalCurvature point ≤ -(a ^ 2)

/-- Radial cutoffs `phi_R` with support and derivative bounds used throughout CC13, CC15, and CCP25. -/
structure RadialCutoffData (Point Cutoff : Type*) where
  cutoff : ℝ → Cutoff
  isSmoothCompactlySupported : Cutoff → Prop
  equalsOneOnBall : Cutoff → ℝ → Prop
  supportedInDoubleBall : Cutoff → ℝ → Prop
  gradientNormAt : Cutoff → Point → ℝ

/-- Source contract for the cutoffs with `|d phi_R| <= 2/R`. -/
def HasStandardRadialCutoffs
    {Point Cutoff : Type*}
    (data : RadialCutoffData Point Cutoff) : Prop :=
  ∀ R : ℝ, 1 < R →
    data.isSmoothCompactlySupported (data.cutoff R) ∧
      data.equalsOneOnBall (data.cutoff R) R ∧
      data.supportedInDoubleBall (data.cutoff R) R ∧
      ∀ point, data.gradientNormAt (data.cutoff R) point ≤ 2 / R

/-- Harmonic-potential observables shared by the hyperbolic construction papers. -/
structure HarmonicPotentialProfile (Point Potential OneForm : Type*) where
  isSmooth : Potential → Prop
  isBounded : Potential → Prop
  isNonconstant : Potential → Prop
  isHarmonic : Potential → Prop
  differential : Potential → OneForm
  isL2 : OneForm → Prop
  isH1 : OneForm → Prop
  gradientNormAt : Potential → Point → ℝ
  hessianEnergy : Potential → ℝ
  differentialEnergy : Potential → ℝ

end RiemannianFluids
