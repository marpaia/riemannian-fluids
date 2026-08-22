import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import RiemannianFluids.Operators.EllipsoidRestriction

/-!
# Eccentricity expansion of the ellipsoid restriction operator

For `mu^2 = (a^2-1)/a^2`, CCY23 equation (5.2) gives

* `1/a^2 = 1-mu^2`, and
* `lambda^2/a^2 = 1-mu^2 sin^2(phi)`.

This file substitutes those identities into the exact projected ambient operator from equation
(2.9).  The resulting candidate is not defined from its Taylor polynomial: it is the original
rational ellipsoid coefficient formula.  We then calculate its exact fourth-order remainder.
-/

namespace RiemannianFluids

noncomputable section

/-- A regular latitude and the first jet of the three coefficients of `dv`. -/
structure EllipsoidEccentricityJet where
  latitude : ℝ
  latitude_pos : 0 < latitude
  latitude_lt_pi : latitude < Real.pi
  vorticity : EllipsoidVorticityJet

namespace EllipsoidEccentricityJet

variable (jet : EllipsoidEccentricityJet)

private abbrev s : ℝ := Real.sin jet.latitude
private abbrev c : ℝ := Real.cos jet.latitude

/-- `1/a^2`. -/
def inverseAxisSquared (eccentricity : ℝ) : ℝ := 1 - eccentricity ^ 2

/-- `lambda^2/a^2`. -/
def normalizedLambdaSquared (eccentricity : ℝ) : ℝ :=
  1 - eccentricity ^ 2 * jet.s ^ 2

theorem sin_latitude_pos : 0 < jet.s :=
  Real.sin_pos_of_pos_of_lt_pi jet.latitude_pos jet.latitude_lt_pi

theorem sin_latitude_ne_zero : jet.s ≠ 0 := ne_of_gt jet.sin_latitude_pos

theorem normalizedLambdaSquared_pos
    {eccentricity : ℝ} (positive : 0 < eccentricity) (lessThanOne : eccentricity < 1) :
    0 < jet.normalizedLambdaSquared eccentricity := by
  have hmuSq : eccentricity ^ 2 < 1 := by nlinarith
  have hsinSq : jet.s ^ 2 ≤ 1 := Real.sin_sq_le_one jet.latitude
  have hproduct : eccentricity ^ 2 * jet.s ^ 2 < 1 :=
    (mul_le_of_le_one_right (sq_nonneg eccentricity) hsinSq).trans_lt hmuSq
  exact sub_pos.2 hproduct

theorem normalizedLambdaSquared_ne_zero
    {eccentricity : ℝ} (positive : 0 < eccentricity) (lessThanOne : eccentricity < 1) :
    jet.normalizedLambdaSquared eccentricity ≠ 0 :=
  ne_of_gt (jet.normalizedLambdaSquared_pos positive lessThanOne)

/-! ## Exact transformed equation (2.9) -/

private def starRhoRhoTheta (eccentricity : ℝ) : ℝ :=
  -(eccentricity ^ 2) * jet.c

private def starRhoPhiTheta (eccentricity : ℝ) : ℝ :=
  (1 - eccentricity ^ 2 * jet.c ^ 2) / jet.s

private def starPhiRhoTheta (eccentricity : ℝ) : ℝ :=
  jet.normalizedLambdaSquared eccentricity / jet.s

private def starPhiPhiTheta (eccentricity : ℝ) : ℝ :=
  -(eccentricity ^ 2) * jet.c

private def starRhoRhoThetaLatitudeDerivative (eccentricity : ℝ) : ℝ :=
  eccentricity ^ 2 * jet.s

private def starRhoPhiThetaLatitudeDerivative (eccentricity : ℝ) : ℝ :=
  2 * eccentricity ^ 2 * jet.c -
    jet.c * (1 - eccentricity ^ 2 * jet.c ^ 2) / jet.s ^ 2

private def ambientCurlRhoTheta (eccentricity : ℝ) : ℝ :=
  jet.vorticity.rhoPhi.rhoDerivative * jet.s -
    jet.starRhoRhoTheta eccentricity * jet.vorticity.rhoTheta.longitudeDerivative -
    jet.starRhoPhiTheta eccentricity * jet.vorticity.phiTheta.longitudeDerivative

private def ambientCurlPhiTheta (eccentricity : ℝ) : ℝ :=
  jet.vorticity.rhoPhi.latitudeDerivative * jet.s +
    jet.vorticity.rhoPhi.value * jet.c +
    jet.starPhiRhoTheta eccentricity * jet.vorticity.rhoTheta.longitudeDerivative +
    jet.starPhiPhiTheta eccentricity * jet.vorticity.phiTheta.longitudeDerivative

private def ambientCurlRhoPhi (eccentricity : ℝ) : ℝ :=
  -jet.starPhiRhoTheta eccentricity * jet.vorticity.rhoTheta.rhoDerivative -
    jet.starPhiPhiTheta eccentricity * jet.vorticity.phiTheta.rhoDerivative +
    jet.starPhiPhiTheta eccentricity * jet.vorticity.phiTheta.value -
    jet.starRhoRhoThetaLatitudeDerivative eccentricity * jet.vorticity.rhoTheta.value -
    jet.starRhoRhoTheta eccentricity * jet.vorticity.rhoTheta.latitudeDerivative -
    jet.starRhoPhiThetaLatitudeDerivative eccentricity * jet.vorticity.phiTheta.value -
    jet.starRhoPhiTheta eccentricity * jet.vorticity.phiTheta.latitudeDerivative

/-- The exact projected ambient Hodge operator after the substitutions in equation (5.2). -/
def exactCandidate (eccentricity : ℝ) : ℝ × ℝ :=
  (-jet.ambientCurlRhoTheta eccentricity * jet.normalizedLambdaSquared eccentricity / jet.s -
      jet.ambientCurlPhiTheta eccentricity * jet.starRhoRhoTheta eccentricity,
    jet.ambientCurlRhoPhi eccentricity * jet.s)

/-! ## The moving intrinsic baseline and the displayed quadratic term -/

private def intrinsicHodgePhi (eccentricity : ℝ) : ℝ :=
  inverseAxisSquared eccentricity * jet.vorticity.phiTheta.longitudeDerivative /
    jet.s ^ 2

private def intrinsicHodgeTheta (eccentricity : ℝ) : ℝ :=
  inverseAxisSquared eccentricity / jet.normalizedLambdaSquared eccentricity *
      (-jet.vorticity.phiTheta.latitudeDerivative +
        jet.c / jet.s * jet.vorticity.phiTheta.value) -
    eccentricity ^ 2 * inverseAxisSquared eccentricity * jet.s * jet.c /
        jet.normalizedLambdaSquared eccentricity ^ 2 *
      jet.vorticity.phiTheta.value

/-- The first line on the right of CCY23 (5.8).  The intrinsic ellipsoid Hodge term moves with
`mu`; only the two displayed normal derivatives are independent of `mu`. -/
def movingBaseline (eccentricity : ℝ) : ℝ × ℝ :=
  (jet.intrinsicHodgePhi eccentricity - jet.vorticity.rhoPhi.rhoDerivative,
    jet.intrinsicHodgeTheta eccentricity - jet.vorticity.rhoTheta.rhoDerivative)

/-- The exact coefficient of `mu^2` in equation (5.8), in coordinate components. -/
def quadraticCorrection : ℝ × ℝ :=
  (jet.s ^ 2 * jet.vorticity.rhoPhi.rhoDerivative +
      jet.c ^ 2 * jet.vorticity.rhoPhi.value +
      jet.s * jet.c * jet.vorticity.rhoPhi.latitudeDerivative,
    jet.s ^ 2 *
        (jet.vorticity.rhoTheta.rhoDerivative - jet.vorticity.rhoTheta.value) +
      jet.s * jet.c *
        (jet.vorticity.phiTheta.rhoDerivative +
          jet.vorticity.rhoTheta.latitudeDerivative -
          2 * jet.vorticity.phiTheta.value))

/-- The exact coefficient multiplying `mu^4` after subtracting the terms displayed in (5.8). -/
def fourthOrderRemainderCoefficient (eccentricity : ℝ) : ℝ :=
  jet.s ^ 3 * jet.c * inverseAxisSquared eccentricity /
        jet.normalizedLambdaSquared eccentricity ^ 2 * jet.vorticity.phiTheta.value -
    jet.s ^ 2 * jet.c ^ 2 / jet.normalizedLambdaSquared eccentricity *
      jet.vorticity.phiTheta.latitudeDerivative

/-- Exact remainder identity behind the `O(mu^4)` in CCY23 equation (5.8). -/
theorem exactCandidate_sub_expansion
    {eccentricity : ℝ} (positive : 0 < eccentricity) (lessThanOne : eccentricity < 1) :
    jet.exactCandidate eccentricity - jet.movingBaseline eccentricity -
        eccentricity ^ 2 • jet.quadraticCorrection =
      (0, eccentricity ^ 4 * jet.fourthOrderRemainderCoefficient eccentricity) := by
  have hdenom := jet.normalizedLambdaSquared_ne_zero positive lessThanOne
  apply Prod.ext
  · simp only [exactCandidate, movingBaseline, quadraticCorrection, Prod.fst_sub,
      Prod.smul_fst, smul_eq_mul]
    unfold ambientCurlRhoTheta ambientCurlPhiTheta intrinsicHodgePhi
      starRhoRhoTheta starRhoPhiTheta starPhiRhoTheta starPhiPhiTheta
      inverseAxisSquared normalizedLambdaSquared
    field_simp [jet.sin_latitude_ne_zero]
    have hcosSq : jet.c ^ 2 = 1 - jet.s ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq jet.latitude]
    ring_nf
    simp_rw [hcosSq]
    ring
  · simp only [exactCandidate, movingBaseline, quadraticCorrection, Prod.snd_sub,
      Prod.smul_snd, smul_eq_mul]
    unfold ambientCurlRhoPhi intrinsicHodgeTheta fourthOrderRemainderCoefficient
      starRhoRhoTheta starRhoPhiTheta starPhiRhoTheta starPhiPhiTheta
      starRhoRhoThetaLatitudeDerivative starRhoPhiThetaLatitudeDerivative
      inverseAxisSquared normalizedLambdaSquared
    unfold normalizedLambdaSquared at hdenom
    field_simp [jet.sin_latitude_ne_zero, hdenom]
    have hcosSq : jet.c ^ 2 = 1 - jet.s ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq jet.latitude]
    have hcosCube : jet.c ^ 3 = jet.c * (1 - jet.s ^ 2) := by
      calc
        jet.c ^ 3 = jet.c * jet.c ^ 2 := by ring
        _ = jet.c * (1 - jet.s ^ 2) := by rw [hcosSq]
    ring_nf
    simp_rw [hcosCube, hcosSq]
    ring

/-- A uniform coefficient bound on `0 < mu < 1/2`.  The constants are intentionally loose;
their role is to turn the exact rational remainder into the source's local `O(mu^4)` estimate. -/
theorem abs_fourthOrderRemainderCoefficient_le
    {eccentricity : ℝ} (positive : 0 < eccentricity)
    (lessThanHalf : eccentricity < (1 / 2 : ℝ)) :
    |jet.fourthOrderRemainderCoefficient eccentricity| ≤
      4 * |jet.vorticity.phiTheta.value| +
        2 * |jet.vorticity.phiTheta.latitudeDerivative| := by
  have lessThanOne : eccentricity < 1 := by linarith
  have hmuSq : eccentricity ^ 2 < (1 / 4 : ℝ) := by nlinarith
  have hsinSq : jet.s ^ 2 ≤ 1 := Real.sin_sq_le_one jet.latitude
  have hcosSq : jet.c ^ 2 ≤ 1 := Real.cos_sq_le_one jet.latitude
  have hsinAbs : |jet.s| ≤ 1 := Real.abs_sin_le_one jet.latitude
  have hcosAbs : |jet.c| ≤ 1 := Real.abs_cos_le_one jet.latitude
  have hproduct : eccentricity ^ 2 * jet.s ^ 2 ≤ eccentricity ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg eccentricity) hsinSq
  have hdenomHalf : (1 / 2 : ℝ) ≤ jet.normalizedLambdaSquared eccentricity := by
    unfold normalizedLambdaSquared
    nlinarith
  have hdenomPos : 0 < jet.normalizedLambdaSquared eccentricity :=
    lt_of_lt_of_le (by norm_num) hdenomHalf
  have hinverseDenom :
      1 / jet.normalizedLambdaSquared eccentricity ≤ 2 := by
    apply (div_le_iff₀ hdenomPos).2
    nlinarith
  have hinverseDenomSq :
      1 / jet.normalizedLambdaSquared eccentricity ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hdenomPos)).2
    nlinarith [sq_nonneg (jet.normalizedLambdaSquared eccentricity - (1 / 2 : ℝ))]
  have haxisPos : 0 < inverseAxisSquared eccentricity := by
    unfold inverseAxisSquared
    nlinarith
  have haxisLe : inverseAxisSquared eccentricity ≤ 1 := by
    unfold inverseAxisSquared
    nlinarith [sq_nonneg eccentricity]
  have hfirstFactors :
      |jet.s| ^ 3 * |jet.c| * |inverseAxisSquared eccentricity| ≤ 1 := by
    rw [abs_of_pos haxisPos]
    calc
      |jet.s| ^ 3 * |jet.c| * inverseAxisSquared eccentricity ≤
          1 ^ 3 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hsecondFactors : |jet.s| ^ 2 * |jet.c| ^ 2 ≤ 1 := by
    calc
      |jet.s| ^ 2 * |jet.c| ^ 2 ≤ 1 ^ 2 * 1 ^ 2 := by gcongr
      _ = 1 := by norm_num
  have hfirst :
      |jet.s ^ 3 * jet.c * inverseAxisSquared eccentricity /
          jet.normalizedLambdaSquared eccentricity ^ 2 *
            jet.vorticity.phiTheta.value| ≤
        4 * |jet.vorticity.phiTheta.value| := by
    calc
      _ = (|jet.s| ^ 3 * |jet.c| * |inverseAxisSquared eccentricity|) *
          (1 / jet.normalizedLambdaSquared eccentricity ^ 2) *
            |jet.vorticity.phiTheta.value| := by
        rw [abs_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_pow,
          abs_of_pos hdenomPos]
        ring
      _ ≤ 1 * 4 * |jet.vorticity.phiTheta.value| := by gcongr
      _ = 4 * |jet.vorticity.phiTheta.value| := by ring
  have hsecond :
      |jet.s ^ 2 * jet.c ^ 2 / jet.normalizedLambdaSquared eccentricity *
          jet.vorticity.phiTheta.latitudeDerivative| ≤
        2 * |jet.vorticity.phiTheta.latitudeDerivative| := by
    calc
      _ = (|jet.s| ^ 2 * |jet.c| ^ 2) *
          (1 / jet.normalizedLambdaSquared eccentricity) *
            |jet.vorticity.phiTheta.latitudeDerivative| := by
        rw [abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hdenomPos]
        ring
      _ ≤ 1 * 2 * |jet.vorticity.phiTheta.latitudeDerivative| := by gcongr
      _ = 2 * |jet.vorticity.phiTheta.latitudeDerivative| := by ring
  unfold fourthOrderRemainderCoefficient
  calc
    |_ - _| ≤
        |jet.s ^ 3 * jet.c * inverseAxisSquared eccentricity /
            jet.normalizedLambdaSquared eccentricity ^ 2 *
              jet.vorticity.phiTheta.value| +
          |jet.s ^ 2 * jet.c ^ 2 / jet.normalizedLambdaSquared eccentricity *
            jet.vorticity.phiTheta.latitudeDerivative| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le
          (jet.s ^ 3 * jet.c * inverseAxisSquared eccentricity /
            jet.normalizedLambdaSquared eccentricity ^ 2 * jet.vorticity.phiTheta.value)
          (-(jet.s ^ 2 * jet.c ^ 2 / jet.normalizedLambdaSquared eccentricity *
            jet.vorticity.phiTheta.latitudeDerivative)))
    _ ≤ 4 * |jet.vorticity.phiTheta.value| +
          2 * |jet.vorticity.phiTheta.latitudeDerivative| :=
      add_le_add hfirst hsecond

/-- The normed `O(mu^4)` estimate in the exact form consumed by the paper-level contract. -/
theorem exactCandidate_expansion_norm_le
    {eccentricity : ℝ} (positive : 0 < eccentricity)
    (lessThanHalf : eccentricity < (1 / 2 : ℝ)) :
    ‖jet.exactCandidate eccentricity - jet.movingBaseline eccentricity -
        eccentricity ^ 2 • jet.quadraticCorrection‖ ≤
      (4 * |jet.vorticity.phiTheta.value| +
          2 * |jet.vorticity.phiTheta.latitudeDerivative|) * eccentricity ^ 4 := by
  have lessThanOne : eccentricity < 1 := by linarith
  rw [jet.exactCandidate_sub_expansion positive lessThanOne]
  have hcoefficient := jet.abs_fourthOrderRemainderCoefficient_le positive lessThanHalf
  have hmul := mul_le_mul_of_nonneg_left hcoefficient (pow_nonneg positive.le 4)
  simp only [Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos positive]
  rw [max_eq_right
    (mul_nonneg (pow_nonneg positive.le 4)
      (abs_nonneg (jet.fourthOrderRemainderCoefficient eccentricity)))]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hmul

end EllipsoidEccentricityJet

end

end RiemannianFluids
