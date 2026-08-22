import RiemannianFluids.Geometry.Instances.AxisymmetricEllipsoid

/-!
# The CCY23 ellipsoid restriction calculation

The paper proves its restriction formula by comparing the `dphi` and `dtheta` coefficients of
the ambient and intrinsic Hodge Laplacians.  The `dtheta` comparison is left to the reader.  This
module records the complete pointwise two-jet calculation.  It is deliberately below the
literature namespace so the same coefficients can be reused by the later ellipsoid papers.

The three entries of `EllipsoidVorticityJet` are the coefficients of
`dv = omega_rho_phi drho wedge dphi + omega_rho_theta drho wedge dtheta +
omega_phi_theta dphi wedge dtheta`, together with their first derivatives.  The normal
contravariant derivative is not an independent input: simultaneous ambient and surface
incompressibility forces it to be `(1-a^2) sin(phi) cos(phi) / lambda^2` times the meridional
velocity.  Its tangential derivatives and the covariant radial component are constructed from
that relation.  These are exactly the cancellations used on pages 7--8 of CCY23.
-/

namespace RiemannianFluids

noncomputable section

open AxisymmetricEllipsoidChartPoint

/-- Value and first coordinate derivatives of one scalar coefficient at `rho = 1`. -/
structure EllipsoidScalarFirstJet where
  value : ℝ
  rhoDerivative : ℝ
  latitudeDerivative : ℝ
  longitudeDerivative : ℝ

/-- The three coefficients of `dv` and their first coordinate derivatives. -/
structure EllipsoidVorticityJet where
  rhoPhi : EllipsoidScalarFirstJet
  rhoTheta : EllipsoidScalarFirstJet
  phiTheta : EllipsoidScalarFirstJet

/-- The pointwise data that remain after tangency and the two divergence equations have fixed
the normal first jet.  `sharedDivergenceResidual` is the common residual of the ambient and
surface divergence equations; it vanishes for the fields in CCY23 Theorem 1.1. -/
structure EllipsoidRestrictionJet where
  vorticity : EllipsoidVorticityJet
  meridionalVelocity : ℝ
  meridionalVelocityLatitudeDerivative : ℝ
  meridionalVelocityLongitudeDerivative : ℝ
  sharedDivergenceResidual : ℝ

namespace EllipsoidRestrictionJet

variable (jet : EllipsoidRestrictionJet) (point : AxisymmetricEllipsoidChartPoint)

/-- The normal derivative of the contravariant radial velocity forced by the difference of the
ambient and surface divergence equations. -/
def normalContravariantDerivative : ℝ :=
  point.normalMixingCoefficient * jet.meridionalVelocity

/-- Its latitude derivative, with the derivative of `lambda^2` left visible. -/
def normalContravariantLatitudeDerivative : ℝ :=
  point.b *
        ((1 - 2 * point.s ^ 2) * jet.meridionalVelocity +
          point.s * point.c * jet.meridionalVelocityLatitudeDerivative) /
      point.L -
    point.b * point.s * point.c * point.lambdaSquaredLatitudeDerivative *
        jet.meridionalVelocity /
      point.L ^ 2

/-- Its longitude derivative. -/
def normalContravariantLongitudeDerivative : ℝ :=
  point.normalMixingCoefficient * jet.meridionalVelocityLongitudeDerivative

/-- Latitude derivative of the covariant radial component on the ellipsoid.  Although the
contravariant radial component vanishes by tangency, `v_rho = (a^2-1) sin(phi) cos(phi) v^phi`
need not vanish. -/
def radialCovectorLatitudeDerivative : ℝ :=
  (point.A - 1) *
    ((1 - 2 * point.s ^ 2) * jet.meridionalVelocity +
      point.s * point.c * jet.meridionalVelocityLatitudeDerivative)

/-- Longitude derivative of the covariant radial component on the ellipsoid. -/
def radialCovectorLongitudeDerivative : ℝ :=
  (point.A - 1) * point.s * point.c * jet.meridionalVelocityLongitudeDerivative

theorem normal_latitude_compatibility :
    point.L * jet.normalContravariantLatitudeDerivative point +
        jet.radialCovectorLatitudeDerivative point =
      2 * (point.A - 1) * point.s * point.c *
        jet.normalContravariantDerivative point := by
  unfold normalContravariantLatitudeDerivative radialCovectorLatitudeDerivative
    normalContravariantDerivative normalMixingCoefficient lambdaSquaredLatitudeDerivative
  dsimp only [AxisymmetricEllipsoidChartPoint.A, AxisymmetricEllipsoidChartPoint.L,
    AxisymmetricEllipsoidChartPoint.s, AxisymmetricEllipsoidChartPoint.c,
    AxisymmetricEllipsoidChartPoint.b, flatteningCoefficient]
  field_simp [point.lambdaSquared_ne_zero]
  ring

theorem normal_longitude_compatibility :
    point.L * jet.normalContravariantLongitudeDerivative point +
        jet.radialCovectorLongitudeDerivative point = 0 := by
  unfold normalContravariantLongitudeDerivative radialCovectorLongitudeDerivative
    normalMixingCoefficient
  dsimp only [AxisymmetricEllipsoidChartPoint.A, AxisymmetricEllipsoidChartPoint.L,
    AxisymmetricEllipsoidChartPoint.s, AxisymmetricEllipsoidChartPoint.c,
    AxisymmetricEllipsoidChartPoint.b, flatteningCoefficient]
  field_simp [point.lambdaSquared_ne_zero]
  ring

/-! ## Hodge-star and exterior-derivative coefficients -/

private def starRhoRhoTheta : ℝ := point.b * point.c / point.A

/-- The simplified form of the `omega_phi_theta` coefficient in CCY23 equation (2.7). -/
private def starRhoPhiTheta : ℝ :=
  (point.A * point.s ^ 2 + (1 - point.s ^ 2)) / (point.A * point.s)

private def starPhiRhoTheta : ℝ := point.L / (point.A * point.s)

private def starPhiPhiTheta : ℝ := point.b * point.c / point.A

private def starRhoRhoThetaLatitudeDerivative : ℝ := -point.b * point.s / point.A

private def radialMetricCoefficientLatitudeDerivative : ℝ :=
  2 * (point.A - 1) * point.s * point.c

private def starRhoPhiThetaLatitudeDerivative : ℝ :=
  radialMetricCoefficientLatitudeDerivative point /
        (point.A * point.s) -
    (point.A * point.s ^ 2 + (1 - point.s ^ 2)) * point.c /
      (point.A * point.s ^ 2)

/-- `F_rho_theta` after differentiating the Hodge-star coefficients. -/
def ambientCurlRhoTheta : ℝ :=
  jet.vorticity.rhoPhi.rhoDerivative * point.s -
    starRhoRhoTheta point * jet.vorticity.rhoTheta.longitudeDerivative -
    starRhoPhiTheta point * jet.vorticity.phiTheta.longitudeDerivative

/-- `F_phi_theta` after differentiating the Hodge-star coefficients. -/
def ambientCurlPhiTheta : ℝ :=
  jet.vorticity.rhoPhi.latitudeDerivative * point.s +
    jet.vorticity.rhoPhi.value * point.c +
    starPhiRhoTheta point * jet.vorticity.rhoTheta.longitudeDerivative +
    starPhiPhiTheta point * jet.vorticity.phiTheta.longitudeDerivative

/-- `F_rho_phi` after differentiating the Hodge-star coefficients. -/
def ambientCurlRhoPhi : ℝ :=
  -starPhiRhoTheta point * jet.vorticity.rhoTheta.rhoDerivative -
    starPhiPhiTheta point * jet.vorticity.phiTheta.rhoDerivative +
    starPhiPhiTheta point * jet.vorticity.phiTheta.value -
    starRhoRhoThetaLatitudeDerivative point * jet.vorticity.rhoTheta.value -
    starRhoRhoTheta point * jet.vorticity.rhoTheta.latitudeDerivative -
    starRhoPhiThetaLatitudeDerivative point * jet.vorticity.phiTheta.value -
    starRhoPhiTheta point * jet.vorticity.phiTheta.latitudeDerivative

/-- The `dphi` coefficient of the projected ambient positive Hodge Laplacian, equation (2.9). -/
def projectedAmbientHodgePhi : ℝ :=
  -jet.ambientCurlRhoTheta point * point.L / (point.A * point.s) -
    jet.ambientCurlPhiTheta point * point.b * point.c / point.A

/-- The `dtheta` coefficient of the projected ambient positive Hodge Laplacian, equation (2.9). -/
def projectedAmbientHodgeTheta : ℝ :=
  jet.ambientCurlRhoPhi point * point.s

/-- The two coordinate coefficients in equation (2.9). -/
def projectedAmbientHodge : ℝ × ℝ :=
  (jet.projectedAmbientHodgePhi point, jet.projectedAmbientHodgeTheta point)

/-! ## Intrinsic and correction terms -/

/-- The `dphi` coefficient of the intrinsic Hodge Laplacian in equation (2.10). -/
def intrinsicHodgePhi : ℝ :=
  jet.vorticity.phiTheta.longitudeDerivative / (point.A * point.s ^ 2)

/-- The expanded `dtheta` coefficient of equation (2.10). -/
def intrinsicHodgeTheta : ℝ :=
  -jet.vorticity.phiTheta.latitudeDerivative / point.L +
    jet.vorticity.phiTheta.value * point.b * point.s * point.c / point.L ^ 2 +
    jet.vorticity.phiTheta.value * point.c / (point.L * point.s)

def intrinsicHodge : ℝ × ℝ :=
  (jet.intrinsicHodgePhi point, jet.intrinsicHodgeTheta point)

private def normalMixingLatitudeDerivative : ℝ :=
  point.b * (1 - 2 * point.s ^ 2) / point.L -
    point.b * point.s * point.c * point.lambdaSquaredLatitudeDerivative / point.L ^ 2

private def inverseGradientLatitudeDerivative : ℝ :=
  -point.A * point.lambdaSquaredLatitudeDerivative / point.L ^ 2

/-- `G_phi` from equations (2.17) and (2.19), after the tangency cancellations. -/
def correctionGPhi : ℝ :=
  (-jet.vorticity.rhoPhi.rhoDerivative +
      inverseGradientLatitudeDerivative point * jet.normalContravariantDerivative point -
      normalMixingLatitudeDerivative point * jet.vorticity.rhoPhi.value -
      point.normalMixingCoefficient * jet.vorticity.rhoPhi.latitudeDerivative) *
    point.L / point.A

/-- `G_theta` from equation (2.18), including the comparison omitted in the paper. -/
def correctionGTheta : ℝ :=
  (-jet.vorticity.rhoTheta.rhoDerivative -
      point.normalMixingCoefficient * jet.vorticity.phiTheta.rhoDerivative +
      point.normalMixingCoefficient * jet.vorticity.phiTheta.value -
      point.normalMixingCoefficient * jet.vorticity.rhoPhi.longitudeDerivative) *
      point.L / point.A +
    (-jet.vorticity.rhoTheta.latitudeDerivative -
        normalMixingLatitudeDerivative point * jet.vorticity.phiTheta.value -
        point.normalMixingCoefficient * jet.vorticity.phiTheta.latitudeDerivative +
        jet.vorticity.rhoPhi.longitudeDerivative) *
      point.b * point.s * point.c / point.A

/-- The `dphi` coefficient of the operator `E(v)` in equation (2.20). -/
def ellipsoidCorrectionPhi : ℝ :=
  jet.correctionGPhi point - jet.normalContravariantLatitudeDerivative point +
    ((point.L - point.A) / point.A + 1 / point.L) * jet.vorticity.rhoPhi.value

/-- The `dtheta` coefficient of the operator `E(v)` in equation (2.21). -/
def ellipsoidCorrectionTheta : ℝ :=
  jet.correctionGTheta point - jet.normalContravariantLongitudeDerivative point +
    ((point.L - point.A) / point.L + point.A / point.L ^ 2) *
      (jet.vorticity.rhoTheta.value * point.L / point.A +
        jet.vorticity.phiTheta.value * point.b * point.s * point.c / point.A)

def ellipsoidCorrection : ℝ × ℝ :=
  (jet.ellipsoidCorrectionPhi point, jet.ellipsoidCorrectionTheta point)

/-- `i_E^* L_Y v` from equation (2.22).  The derivatives are those of the covariant radial
component, as required by Cartan's formula. -/
def scalingLieDerivative : ℝ × ℝ :=
  (jet.vorticity.rhoPhi.value + jet.radialCovectorLatitudeDerivative point,
    jet.vorticity.rhoTheta.value + jet.radialCovectorLongitudeDerivative point)

/-- `i_E^*{(L_{grad rho} v)_phi} e^2`: raising the `phi` component and multiplying by the
orthonormal covector contributes `sqrt(lambda^2) / a^2`. -/
def meridionalLieDerivative : ℝ × ℝ :=
  (Real.sqrt point.L / point.A * jet.vorticity.rhoPhi.value, 0)

/-! ## Complete component comparison -/

theorem projectedAmbientHodgePhi_residual_identity :
    jet.projectedAmbientHodgePhi point -
        (jet.intrinsicHodgePhi point + jet.ellipsoidCorrectionPhi point -
          (1 / point.L) * (jet.scalingLieDerivative point).1 -
          (2 / point.A) * (1 - point.A / point.L) * jet.vorticity.rhoPhi.value) =
      (point.L * jet.normalContravariantLatitudeDerivative point +
          jet.radialCovectorLatitudeDerivative point -
          2 * (point.A - 1) * point.s * point.c *
            jet.normalContravariantDerivative point) /
        point.L := by
  unfold projectedAmbientHodgePhi ambientCurlRhoTheta ambientCurlPhiTheta intrinsicHodgePhi
    ellipsoidCorrectionPhi correctionGPhi scalingLieDerivative
    starRhoRhoTheta starRhoPhiTheta starPhiRhoTheta starPhiPhiTheta
    inverseGradientLatitudeDerivative normalMixingLatitudeDerivative normalMixingCoefficient
    lambdaSquaredLatitudeDerivative
  have hL := point.lambdaSquared_ne_zero
  simp_rw [point.lambdaSquared_eq_axisSquared_mul_one_sub_sinSquared] at hL ⊢
  dsimp only [AxisymmetricEllipsoidChartPoint.A, AxisymmetricEllipsoidChartPoint.s,
    AxisymmetricEllipsoidChartPoint.c, AxisymmetricEllipsoidChartPoint.b,
    flatteningCoefficient] at hL ⊢
  field_simp [point.axisSquared_ne_zero, hL,
    point.sin_latitude_ne_zero]
  have hcosSq : Real.cos point.latitude ^ 2 = 1 - Real.sin point.latitude ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq point.latitude]
  ring_nf
  simp_rw [hcosSq]
  ring

theorem projectedAmbientHodgeTheta_residual_identity :
    jet.projectedAmbientHodgeTheta point -
        (jet.intrinsicHodgeTheta point + jet.ellipsoidCorrectionTheta point -
          (1 / point.L) * (jet.scalingLieDerivative point).2) =
      (point.L * jet.normalContravariantLongitudeDerivative point +
          jet.radialCovectorLongitudeDerivative point) /
        point.L := by
  unfold projectedAmbientHodgeTheta ambientCurlRhoPhi intrinsicHodgeTheta
    ellipsoidCorrectionTheta correctionGTheta scalingLieDerivative
    starRhoRhoTheta starRhoPhiTheta starPhiRhoTheta starPhiPhiTheta
    starRhoRhoThetaLatitudeDerivative starRhoPhiThetaLatitudeDerivative
    radialMetricCoefficientLatitudeDerivative normalMixingLatitudeDerivative
    normalMixingCoefficient lambdaSquaredLatitudeDerivative
  have hL := point.lambdaSquared_ne_zero
  simp_rw [point.lambdaSquared_eq_axisSquared_mul_one_sub_sinSquared] at hL ⊢
  dsimp only [AxisymmetricEllipsoidChartPoint.A, AxisymmetricEllipsoidChartPoint.s,
    AxisymmetricEllipsoidChartPoint.c, AxisymmetricEllipsoidChartPoint.b,
    flatteningCoefficient] at hL ⊢
  field_simp [point.axisSquared_ne_zero, hL,
    point.sin_latitude_ne_zero]
  have hcosSq : Real.cos point.latitude ^ 2 = 1 - Real.sin point.latitude ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq point.latitude]
  have hcosCube :
      Real.cos point.latitude ^ 3 =
        Real.cos point.latitude * (1 - Real.sin point.latitude ^ 2) := by
    calc
      Real.cos point.latitude ^ 3 =
          Real.cos point.latitude * Real.cos point.latitude ^ 2 := by ring
      _ = Real.cos point.latitude * (1 - Real.sin point.latitude ^ 2) := by rw [hcosSq]
  ring_nf
  simp_rw [hcosCube, hcosSq]
  ring

theorem projectedAmbientHodgePhi_eq_sourceFormula :
    jet.projectedAmbientHodgePhi point =
      jet.intrinsicHodgePhi point + jet.ellipsoidCorrectionPhi point -
        point.sqrtGaussianCurvature * (jet.scalingLieDerivative point).1 -
        (2 / point.A) * (1 - point.A / point.L) * jet.vorticity.rhoPhi.value := by
  rw [show point.sqrtGaussianCurvature = 1 / point.L by
    rfl]
  have hresidual := jet.projectedAmbientHodgePhi_residual_identity point
  rw [jet.normal_latitude_compatibility point] at hresidual
  have hnum :
      2 * (point.A - 1) * point.s * point.c * jet.normalContravariantDerivative point -
          2 * (point.A - 1) * point.s * point.c *
            jet.normalContravariantDerivative point = 0 := by ring
  rw [hnum, zero_div] at hresidual
  exact sub_eq_zero.mp hresidual

theorem projectedAmbientHodgeTheta_eq_sourceFormula :
    jet.projectedAmbientHodgeTheta point =
      jet.intrinsicHodgeTheta point + jet.ellipsoidCorrectionTheta point -
        point.sqrtGaussianCurvature * (jet.scalingLieDerivative point).2 := by
  rw [show point.sqrtGaussianCurvature = 1 / point.L by
    rfl]
  have hresidual := jet.projectedAmbientHodgeTheta_residual_identity point
  rw [jet.normal_longitude_compatibility point, zero_div] at hresidual
  exact sub_eq_zero.mp hresidual

theorem weightedMeridionalLieDerivative :
    (2 * point.fourthRootGaussianCurvature *
          (1 - (point.gradientRhoNormSquared)⁻¹)) •
        jet.meridionalLieDerivative point =
      ((2 / point.A) * (1 - point.A / point.L) * jet.vorticity.rhoPhi.value, 0) := by
  rw [point.inverse_gradientRhoNormSquared]
  ext <;>
    simp only [meridionalLieDerivative, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_zero]
  unfold fourthRootGaussianCurvature
  field_simp [point.axisSquared_ne_zero, point.lambdaSquared_ne_zero,
    point.sqrt_lambdaSquared_ne_zero]

/-- CCY23 Theorem 1.1 as the complete two-coordinate calculation. -/
theorem projectedAmbientHodge_eq_invariantRestriction :
    jet.projectedAmbientHodge point =
      jet.intrinsicHodge point + jet.ellipsoidCorrection point -
        point.sqrtGaussianCurvature • jet.scalingLieDerivative point -
        (2 * point.fourthRootGaussianCurvature *
            (1 - (point.gradientRhoNormSquared)⁻¹)) •
          jet.meridionalLieDerivative point := by
  rw [jet.weightedMeridionalLieDerivative point]
  apply Prod.ext
  · simpa [projectedAmbientHodge, intrinsicHodge, ellipsoidCorrection] using
      jet.projectedAmbientHodgePhi_eq_sourceFormula point
  · simpa [projectedAmbientHodge, intrinsicHodge, ellipsoidCorrection] using
      jet.projectedAmbientHodgeTheta_eq_sourceFormula point

end EllipsoidRestrictionJet

end

end RiemannianFluids
