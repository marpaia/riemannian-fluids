import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The radial divergence correction in CCY23

Section 4 of Chan--Czubak--Yoneda constructs a simultaneous ambient/surface divergence-free
extension near the ellipsoid.  If `D rho` is the ambient divergence of an already chosen
tangential extension along one radial ray, the missing contravariant radial coefficient is

`v^rho(rho) = -rho⁻² ∫_1^rho tau² D(tau) d tau`.

This file proves the construction rather than storing its ODE as a hypothesis.  The interval
integral gives the boundary trace at `rho = 1`; the fundamental theorem of calculus gives the
weighted radial ODE; and division by `rho²` is smooth on the positive radial neighborhood used
by the paper.  The parameter indexing radial rays is deliberately arbitrary, so the result can
later be fed by the angular variables of the ellipsoid chart.
-/

namespace RiemannianFluids

noncomputable section

open Set
open scoped ContDiff

namespace EllipsoidRadialExtension

/-- The weighted ambient-divergence density along a fixed ellipsoid ray. -/
def weightedDivergence (divergence : ℝ → ℝ) (rho : ℝ) : ℝ :=
  rho ^ 2 * divergence rho

/-- The radial flux selected by the boundary condition at `rho = 1`. -/
def weightedNormalFlux (divergence : ℝ → ℝ) (rho : ℝ) : ℝ :=
  -(∫ tau in (1 : ℝ)..rho, weightedDivergence divergence tau)

/-- CCY23 equation (4.6), the contravariant coefficient of `partial_rho`. -/
def normalCoefficient (divergence : ℝ → ℝ) (rho : ℝ) : ℝ :=
  weightedNormalFlux divergence rho / rho ^ 2

@[simp]
theorem weightedNormalFlux_at_surface (divergence : ℝ → ℝ) :
    weightedNormalFlux divergence 1 = 0 := by
  simp [weightedNormalFlux]

@[simp]
theorem normalCoefficient_at_surface (divergence : ℝ → ℝ) :
    normalCoefficient divergence 1 = 0 := by
  simp [normalCoefficient]

/-- Away from the radial singularity, multiplying the normal coefficient by the Euclidean
Jacobian factor `rho²` recovers the constructed flux. -/
theorem rho_sq_mul_normalCoefficient
    (divergence : ℝ → ℝ) {rho : ℝ} (rho_ne_zero : rho ≠ 0) :
    rho ^ 2 * normalCoefficient divergence rho = weightedNormalFlux divergence rho := by
  simp only [normalCoefficient]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 rho_ne_zero)

/-- Fundamental theorem of calculus for the flux in (4.6). -/
theorem weightedNormalFlux_hasDerivAt
    {divergence : ℝ → ℝ} (continuous : Continuous divergence) (rho : ℝ) :
    HasDerivAt (weightedNormalFlux divergence)
      (-(rho ^ 2 * divergence rho)) rho := by
  have weightedContinuous : Continuous (weightedDivergence divergence) :=
    (continuous_id.pow 2).mul continuous
  change HasDerivAt
    (fun radius => -(∫ tau in (1 : ℝ)..radius, tau ^ 2 * divergence tau))
      (-(rho ^ 2 * divergence rho)) rho
  exact (weightedContinuous.integral_hasStrictDerivAt 1 rho).hasDerivAt.neg

/-- The concrete coefficient in (4.6) solves
`partial_rho (rho² v^rho) = -rho² div(omega)` at every positive radius. -/
theorem weighted_normalCoefficient_hasDerivAt
    {divergence : ℝ → ℝ} (continuous : Continuous divergence)
    {rho : ℝ} (rho_ne_zero : rho ≠ 0) :
    HasDerivAt (fun radius => radius ^ 2 * normalCoefficient divergence radius)
      (-(rho ^ 2 * divergence rho)) rho := by
  apply (weightedNormalFlux_hasDerivAt continuous rho).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds rho_ne_zero] with radius radius_ne_zero
  exact rho_sq_mul_normalCoefficient divergence radius_ne_zero

/-- The expanded radial-divergence identity from CCY23 Section 4. -/
theorem normalCoefficient_divergence_cancellation
    {divergence : ℝ → ℝ} (continuous : Continuous divergence)
    {rho : ℝ} (rho_ne_zero : rho ≠ 0) :
    (rho ^ 2)⁻¹ *
          deriv (fun radius => radius ^ 2 * normalCoefficient divergence radius) rho +
        divergence rho = 0 := by
  rw [(weighted_normalCoefficient_hasDerivAt continuous rho_ne_zero).deriv]
  field_simp [rho_ne_zero]
  ring

/-- Smooth radial divergence produces a smooth weighted flux. -/
theorem weightedNormalFlux_contDiff
    {divergence : ℝ → ℝ} (smooth : ContDiff ℝ ∞ divergence) :
    ContDiff ℝ ∞ (weightedNormalFlux divergence) := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · intro rho
    exact (weightedNormalFlux_hasDerivAt smooth.continuous rho).differentiableAt
  · have derivativeIdentity :
        deriv (weightedNormalFlux divergence) =
          fun rho => -(rho ^ 2 * divergence rho) := by
      funext rho
      exact (weightedNormalFlux_hasDerivAt smooth.continuous rho).deriv
    rw [derivativeIdentity]
    have identitySmooth : ContDiff ℝ ∞ (fun rho : ℝ => rho) := contDiff_id
    exact ((identitySmooth.pow 2).mul smooth).neg

/-- Equation (4.6) is smooth on the entire positive radial neighborhood. -/
theorem normalCoefficient_contDiffOn_positive
    {divergence : ℝ → ℝ} (smooth : ContDiff ℝ ∞ divergence) :
    ContDiffOn ℝ ∞ (normalCoefficient divergence) (Ioi 0) := by
  have identitySmooth : ContDiff ℝ ∞ (fun rho : ℝ => rho) := contDiff_id
  exact (weightedNormalFlux_contDiff smooth).contDiffOn.div
    (identitySmooth.pow 2).contDiffOn
    (fun rho rho_pos => pow_ne_zero 2 (ne_of_gt rho_pos))

/-- All source obligations supplied by the scalar radial construction for one ray. -/
structure Certificate (divergence : ℝ → ℝ) where
  boundaryTrace : normalCoefficient divergence 1 = 0
  smoothOnPositiveRadii : ContDiffOn ℝ ∞ (normalCoefficient divergence) (Ioi 0)
  weightedODE : ∀ rho, 0 < rho →
    HasDerivAt (fun radius => radius ^ 2 * normalCoefficient divergence radius)
      (-(rho ^ 2 * divergence rho)) rho
  ambientDivergenceZero : ∀ rho, 0 < rho →
    (rho ^ 2)⁻¹ *
          deriv (fun radius => radius ^ 2 * normalCoefficient divergence radius) rho +
        divergence rho = 0

/-- CCY23 Section 4's explicit extension formula produces its complete radial certificate. -/
theorem certificate
    {divergence : ℝ → ℝ} (smooth : ContDiff ℝ ∞ divergence) :
    Certificate divergence where
  boundaryTrace := normalCoefficient_at_surface divergence
  smoothOnPositiveRadii := normalCoefficient_contDiffOn_positive smooth
  weightedODE := fun _ rho_pos =>
    weighted_normalCoefficient_hasDerivAt smooth.continuous (ne_of_gt rho_pos)
  ambientDivergenceZero := fun _ rho_pos =>
    normalCoefficient_divergence_cancellation smooth.continuous (ne_of_gt rho_pos)

/-- The same construction applied independently to every angular ray.  This is the exact
parameterized form needed by the ellipsoid chart; joint angular smoothness is a separate
parametric-integration theorem. -/
theorem familyCertificate
    {Parameter : Type*} (divergence : Parameter → ℝ → ℝ)
    (smoothRadially : ∀ parameter, ContDiff ℝ ∞ (divergence parameter)) :
    ∀ parameter, Certificate (divergence parameter) :=
  fun parameter => certificate (smoothRadially parameter)

end EllipsoidRadialExtension

end

end RiemannianFluids
