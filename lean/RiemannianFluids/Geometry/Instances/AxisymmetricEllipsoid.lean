import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The axisymmetric ellipsoid in the CCY23 coordinates

This file owns the elementary geometry shared by the ellipsoid papers.  The source uses

`Phi (rho, phi, theta) = (a rho sin phi cos theta, a rho sin phi sin theta, rho cos phi)`

and writes `lambda^2 = a^2 cos^2 phi + sin^2 phi`.  We retain `lambdaSquared` as a single
quantity, so occurrences of the paper's `lambda^4` become `lambdaSquared ^ 2`.
-/

namespace RiemannianFluids

noncomputable section

/-- A point in the regular latitude chart of the axisymmetric ellipsoid. -/
structure AxisymmetricEllipsoidChartPoint where
  axis : ℝ
  latitude : ℝ
  axis_pos : 0 < axis
  latitude_pos : 0 < latitude
  latitude_lt_pi : latitude < Real.pi

namespace AxisymmetricEllipsoidChartPoint

/-- The square of the equatorial axis parameter. -/
def axisSquared (point : AxisymmetricEllipsoidChartPoint) : ℝ := point.axis ^ 2

/-- CCY23's `lambda^2 = a^2 cos^2 phi + sin^2 phi`. -/
def lambdaSquared (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  point.axisSquared * Real.cos point.latitude ^ 2 + Real.sin point.latitude ^ 2

/-- The squared Euclidean norm of `grad rho` on `rho = 1`. -/
def gradientRhoNormSquared (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  point.lambdaSquared / point.axisSquared

/-- Gaussian curvature `K_E = 1 / lambda^4` in the source coordinates. -/
def gaussianCurvature (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  1 / point.lambdaSquared ^ 2

/-- The positive square root of Gaussian curvature, written without a redundant square root. -/
def sqrtGaussianCurvature (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  1 / point.lambdaSquared

/-- The positive fourth root of Gaussian curvature. -/
def fourthRootGaussianCurvature (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  1 / Real.sqrt point.lambdaSquared

/-- `1 - a^2`, a recurring coefficient in the Hodge-star calculation. -/
def flatteningCoefficient (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  1 - point.axisSquared

/-! Short aliases matching the notation in the source coordinate calculation. -/

abbrev A (point : AxisymmetricEllipsoidChartPoint) : ℝ := point.axisSquared
abbrev L (point : AxisymmetricEllipsoidChartPoint) : ℝ := point.lambdaSquared
abbrev s (point : AxisymmetricEllipsoidChartPoint) : ℝ := Real.sin point.latitude
abbrev c (point : AxisymmetricEllipsoidChartPoint) : ℝ := Real.cos point.latitude
abbrev b (point : AxisymmetricEllipsoidChartPoint) : ℝ := point.flatteningCoefficient

/-- The coefficient `(1-a^2) sin(phi) cos(phi) / lambda^2`. -/
def normalMixingCoefficient (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  point.flatteningCoefficient * Real.sin point.latitude * Real.cos point.latitude /
    point.lambdaSquared

/-- The displayed latitude derivative of `lambda^2` in CCY23 equation (5.2). -/
def lambdaSquaredLatitudeDerivative (point : AxisymmetricEllipsoidChartPoint) : ℝ :=
  2 * point.flatteningCoefficient * Real.sin point.latitude * Real.cos point.latitude

theorem axis_ne_zero (point : AxisymmetricEllipsoidChartPoint) : point.axis ≠ 0 :=
  ne_of_gt point.axis_pos

theorem axisSquared_pos (point : AxisymmetricEllipsoidChartPoint) : 0 < point.axisSquared := by
  exact sq_pos_of_pos point.axis_pos

theorem axisSquared_ne_zero (point : AxisymmetricEllipsoidChartPoint) :
    point.axisSquared ≠ 0 :=
  ne_of_gt point.axisSquared_pos

theorem sin_latitude_pos (point : AxisymmetricEllipsoidChartPoint) :
    0 < Real.sin point.latitude :=
  Real.sin_pos_of_pos_of_lt_pi point.latitude_pos point.latitude_lt_pi

theorem sin_latitude_ne_zero (point : AxisymmetricEllipsoidChartPoint) :
    Real.sin point.latitude ≠ 0 :=
  ne_of_gt point.sin_latitude_pos

theorem lambdaSquared_pos (point : AxisymmetricEllipsoidChartPoint) :
    0 < point.lambdaSquared := by
  have hsinSq : 0 < Real.sin point.latitude ^ 2 :=
    sq_pos_of_pos point.sin_latitude_pos
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sq_nonneg point.axis) (sq_nonneg (Real.cos point.latitude))) hsinSq

theorem lambdaSquared_ne_zero (point : AxisymmetricEllipsoidChartPoint) :
    point.lambdaSquared ≠ 0 :=
  ne_of_gt point.lambdaSquared_pos

theorem sqrt_lambdaSquared_pos (point : AxisymmetricEllipsoidChartPoint) :
    0 < Real.sqrt point.lambdaSquared :=
  Real.sqrt_pos.2 point.lambdaSquared_pos

theorem sqrt_lambdaSquared_ne_zero (point : AxisymmetricEllipsoidChartPoint) :
    Real.sqrt point.lambdaSquared ≠ 0 :=
  ne_of_gt point.sqrt_lambdaSquared_pos

theorem lambdaSquared_sub_axisSquared (point : AxisymmetricEllipsoidChartPoint) :
    point.lambdaSquared - point.axisSquared =
      point.flatteningCoefficient * Real.sin point.latitude ^ 2 := by
  simp only [lambdaSquared, axisSquared, flatteningCoefficient]
  nlinarith [Real.sin_sq_add_cos_sq point.latitude]

theorem lambdaSquared_eq_axisSquared_mul_one_sub_sinSquared
    (point : AxisymmetricEllipsoidChartPoint) :
    point.L = point.A * (1 - point.s ^ 2) + point.s ^ 2 := by
  simp only [L, A, s, lambdaSquared]
  have hcosSq : Real.cos point.latitude ^ 2 = 1 - Real.sin point.latitude ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq point.latitude]
  rw [hcosSq]

theorem inverse_gradientRhoNormSquared (point : AxisymmetricEllipsoidChartPoint) :
    (point.gradientRhoNormSquared)⁻¹ = point.axisSquared / point.lambdaSquared := by
  rw [gradientRhoNormSquared]
  field_simp [point.axisSquared_ne_zero, point.lambdaSquared_ne_zero]

theorem fourthRoot_mul_sqrtLambda (point : AxisymmetricEllipsoidChartPoint) :
    point.fourthRootGaussianCurvature * Real.sqrt point.lambdaSquared = 1 := by
  simpa only [fourthRootGaussianCurvature, one_div] using
    inv_mul_cancel₀ point.sqrt_lambdaSquared_ne_zero

/-- The non-obvious coefficient in CCY23 (2.7) is the radial metric coefficient divided by
`a^2 sin(phi)`.  Recording this identity keeps the later operator proof small. -/
theorem hodgeStarRhoCoefficient_identity (point : AxisymmetricEllipsoidChartPoint) :
    (((point.flatteningCoefficient ^ 2 / point.axisSquared) *
          Real.sin point.latitude ^ 2 * Real.cos point.latitude ^ 2 + 1) /
        (point.lambdaSquared * Real.sin point.latitude)) =
      (point.axisSquared * Real.sin point.latitude ^ 2 +
          Real.cos point.latitude ^ 2) /
        (point.axisSquared * Real.sin point.latitude) := by
  field_simp [point.axisSquared_ne_zero, point.lambdaSquared_ne_zero,
    point.sin_latitude_ne_zero]
  simp only [lambdaSquared, axisSquared, flatteningCoefficient]
  have hcosSq : Real.cos point.latitude ^ 2 = 1 - Real.sin point.latitude ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq point.latitude]
  rw [hcosSq]
  ring

end AxisymmetricEllipsoidChartPoint

/-- CCY23 equation (1.3), as an actual map into Euclidean three-space. -/
def axisymmetricEllipsoidParametrization
    (axis rho latitude longitude : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2
    ![axis * rho * Real.sin latitude * Real.cos longitude,
      axis * rho * Real.sin latitude * Real.sin longitude,
      rho * Real.cos latitude]

/-- At `rho = 1`, the parametrization lies on `x^2 + y^2 + a^2 z^2 = a^2`. -/
theorem axisymmetricEllipsoidParametrization_mem
    (axis latitude longitude : ℝ) :
    (axisymmetricEllipsoidParametrization axis 1 latitude longitude 0) ^ 2 +
        (axisymmetricEllipsoidParametrization axis 1 latitude longitude 1) ^ 2 +
        axis ^ 2 * (axisymmetricEllipsoidParametrization axis 1 latitude longitude 2) ^ 2 =
      axis ^ 2 := by
  rw [show axisymmetricEllipsoidParametrization axis 1 latitude longitude 0 =
      axis * Real.sin latitude * Real.cos longitude by
        simp [axisymmetricEllipsoidParametrization]]
  rw [show axisymmetricEllipsoidParametrization axis 1 latitude longitude 1 =
      axis * Real.sin latitude * Real.sin longitude by
        simp [axisymmetricEllipsoidParametrization]]
  rw [show axisymmetricEllipsoidParametrization axis 1 latitude longitude 2 =
      Real.cos latitude by
        simp [axisymmetricEllipsoidParametrization]]
  calc
    _ = axis ^ 2 * Real.sin latitude ^ 2 *
          (Real.cos longitude ^ 2 + Real.sin longitude ^ 2) +
        axis ^ 2 * Real.cos latitude ^ 2 := by ring
    _ = axis ^ 2 *
          (Real.sin latitude ^ 2 + Real.cos latitude ^ 2) := by
      rw [Real.cos_sq_add_sin_sq longitude]
      ring
    _ = axis ^ 2 := by rw [Real.sin_sq_add_cos_sq latitude]; ring

end

end RiemannianFluids
