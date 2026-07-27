import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hyperbolic and constant-curvature geometry contracts

This module owns the common geometric hypotheses used in CC13, CC15, CC21, and CCP25.
The paper notation `H^N(-a^2)` is expanded into dimension, completeness, simple connectivity,
absence of boundary, and the pointwise sectional-curvature value.  Pinched negative curvature
is kept separate because CC13 first proves several estimates in the more general range
`-b^2 <= K <= -a^2` before specializing to the space form.
-/

namespace RiemannianFluids

/-- Observable geometry for a complete Riemannian manifold. -/
structure RiemannianGeometryProfile (Point : Type*) where
  intrinsicDimension : ℕ
  sectionalCurvature : Point → ℝ
  ricciEigenvalue : Point → ℝ
  scalarCurvature : Point → ℝ
  distanceFromBasepoint : Point → ℝ
  injectivityRadius : Point → ℝ
  geodesicallyComplete : Prop
  simplyConnected : Prop
  noncompact : Prop
  withoutBoundary : Prop

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
