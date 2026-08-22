import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannianFluids.Operators.EllipsoidEccentricity
import RiemannianFluids.Operators.Restriction

/-!
# CCY23: restriction of ambient viscosity to an ellipsoid

The source formulas are pointwise.  An `Argument` indexes an ambient field, its restriction, and a
point of the axisymmetric ellipsoid.  Residual norms expose the three admissibility conditions;
the formula structures contain only the individual geometric terms appearing in the equations.
-/

namespace RiemannianFluids.Literature.CCY23

/-- Pointwise terms in CCY23 Theorem 1.1, equation (1.4). -/
structure EllipsoidRestrictionData
    (Argument Value : Type*) [AddCommGroup Value] [Module ℝ Value] where
  axisParameter : ℝ
  ambientTangencyResidualNormSq : Argument → ℝ
  ambientDivergenceResidualNormSq : Argument → ℝ
  surfaceDivergenceResidualNormSq : Argument → ℝ
  projectedAmbientHodge : Argument → Value
  intrinsicHodge : Argument → Value
  ellipsoidCorrection : Argument → Value
  sqrtGaussianCurvature : Argument → ℝ
  fourthRootGaussianCurvature : Argument → ℝ
  inverseGradientRhoNormSq : Argument → ℝ
  scalingLieDerivative : Argument → Value
  meridionalLieDerivative : Argument → Value

/-- Source signature for CCY23 Theorem 1.1.  Every coefficient and sign in (1.4) remains
visible, including the two distinct curvature-weighted Lie-derivative corrections. -/
def invariant_restriction_statement
    {Argument Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    (data : EllipsoidRestrictionData Argument Value) : Prop :=
  0 < data.axisParameter → ∀ argument,
    data.ambientTangencyResidualNormSq argument = 0 →
    data.ambientDivergenceResidualNormSq argument = 0 →
    data.surfaceDivergenceResidualNormSq argument = 0 →
      data.projectedAmbientHodge argument =
        data.intrinsicHodge argument + data.ellipsoidCorrection argument -
          data.sqrtGaussianCurvature argument • data.scalingLieDerivative argument -
          (2 * data.fourthRootGaussianCurvature argument *
              (1 - data.inverseGradientRhoNormSq argument)) •
            data.meridionalLieDerivative argument

/-! ## Concrete axisymmetric-ellipsoid realization -/

/-- Every observable in Theorem 1.1, assembled from the complete coordinate two-jet
calculation.  The tangency residual is zero by construction.  The ambient and surface
divergence residuals coincide because their difference has already fixed the normal derivative;
the theorem applies when that common residual vanishes. -/
noncomputable def axisymmetricEllipsoidRestrictionData
    (point : AxisymmetricEllipsoidChartPoint) :
    EllipsoidRestrictionData EllipsoidRestrictionJet (ℝ × ℝ) where
  axisParameter := point.axis
  ambientTangencyResidualNormSq := fun _ => 0
  ambientDivergenceResidualNormSq := fun jet => jet.sharedDivergenceResidual ^ 2
  surfaceDivergenceResidualNormSq := fun jet => jet.sharedDivergenceResidual ^ 2
  projectedAmbientHodge := fun jet => jet.projectedAmbientHodge point
  intrinsicHodge := fun jet => jet.intrinsicHodge point
  ellipsoidCorrection := fun jet => jet.ellipsoidCorrection point
  sqrtGaussianCurvature := fun _ => point.sqrtGaussianCurvature
  fourthRootGaussianCurvature := fun _ => point.fourthRootGaussianCurvature
  inverseGradientRhoNormSq := fun _ => (point.gradientRhoNormSquared)⁻¹
  scalingLieDerivative := fun jet => jet.scalingLieDerivative point
  meridionalLieDerivative := fun jet => jet.meridionalLieDerivative point

/-- CCY23 Theorem 1.1 on the actual axisymmetric-ellipsoid coefficients.  This theorem closes
both coordinate components, including the `dtheta` comparison left to the reader in the paper. -/
theorem invariant_restriction_axisymmetric_ellipsoid
    (point : AxisymmetricEllipsoidChartPoint) :
    invariant_restriction_statement (axisymmetricEllipsoidRestrictionData point) := by
  intro _ jet _ _ _
  simpa only [axisymmetricEllipsoidRestrictionData] using
    jet.projectedAmbientHodge_eq_invariantRestriction point

/-- Component observables in the differential-form eccentricity expansion (5.8). -/
structure EllipsoidEccentricityExpansionData
    (Argument Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℝ Value] where
  latitude : Argument → ℝ
  candidate : ℝ → Argument → Value
  movingBaseline : ℝ → Argument → Value
  phiCovector : Argument → ℝ →ₗ[ℝ] Value
  thetaCovector : Argument → ℝ →ₗ[ℝ] Value
  radialOmegaRhoPhi : Argument → ℝ
  omegaRhoPhi : Argument → ℝ
  latitudeOmegaRhoPhi : Argument → ℝ
  radialOmegaRhoTheta : Argument → ℝ
  omegaRhoTheta : Argument → ℝ
  radialOmegaPhiTheta : Argument → ℝ
  latitudeOmegaRhoTheta : Argument → ℝ
  omegaPhiTheta : Argument → ℝ

/-- The exact coefficient of `mu^2` in CCY23 equation (5.8). -/
noncomputable def eccentricityQuadraticCorrection
    {Argument Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (data : EllipsoidEccentricityExpansionData Argument Value)
    (argument : Argument) : Value :=
  let latitude := data.latitude argument
  data.phiCovector argument
      (Real.sin latitude ^ 2 * data.radialOmegaRhoPhi argument +
        Real.cos latitude ^ 2 * data.omegaRhoPhi argument +
        Real.sin latitude * Real.cos latitude * data.latitudeOmegaRhoPhi argument) +
    data.thetaCovector argument
      (Real.sin latitude ^ 2 *
          (data.radialOmegaRhoTheta argument - data.omegaRhoTheta argument) +
        Real.sin latitude * Real.cos latitude *
          (data.radialOmegaPhiTheta argument +
            data.latitudeOmegaRhoTheta argument -
            2 * data.omegaPhiTheta argument))

/-- Source signature for the eccentricity expansion (5.8), using the paper's coordinate
`mu = sqrt((a^2-1)/a^2)`: the displayed residual is locally `O(mu^4)` as `mu -> 0+`.
The baseline depends on `mu` because the first term in (5.8) is the intrinsic Hodge Laplacian
on the varying ellipsoid `E_mu`; treating it as a fixed spherical term would change the claim. -/
def eccentricity_expansion_statement
    {Argument Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (data : EllipsoidEccentricityExpansionData Argument Value) : Prop :=
  ∀ argument,
    ∃ constant cutoff : ℝ, 0 ≤ constant ∧ 0 < cutoff ∧
      ∀ eccentricity,
        0 < eccentricity → eccentricity < cutoff → eccentricity < 1 →
          ‖data.candidate eccentricity argument - data.movingBaseline eccentricity argument -
              eccentricity ^ 2 • eccentricityQuadraticCorrection data argument‖ ≤
            constant * eccentricity ^ 4

/-! ## Concrete eccentricity realization -/

private def phiCoordinateCovector : ℝ →ₗ[ℝ] ℝ × ℝ :=
  LinearMap.inl ℝ ℝ ℝ

private def thetaCoordinateCovector : ℝ →ₗ[ℝ] ℝ × ℝ :=
  LinearMap.inr ℝ ℝ ℝ

/-- The exact rational candidate, moving intrinsic baseline, and vorticity jets in CCY23
equation (5.8). -/
noncomputable def axisymmetricEllipsoidEccentricityData :
    EllipsoidEccentricityExpansionData EllipsoidEccentricityJet (ℝ × ℝ) where
  latitude := EllipsoidEccentricityJet.latitude
  candidate := fun eccentricity jet => jet.exactCandidate eccentricity
  movingBaseline := fun eccentricity jet => jet.movingBaseline eccentricity
  phiCovector := fun _ => phiCoordinateCovector
  thetaCovector := fun _ => thetaCoordinateCovector
  radialOmegaRhoPhi := fun jet => jet.vorticity.rhoPhi.rhoDerivative
  omegaRhoPhi := fun jet => jet.vorticity.rhoPhi.value
  latitudeOmegaRhoPhi := fun jet => jet.vorticity.rhoPhi.latitudeDerivative
  radialOmegaRhoTheta := fun jet => jet.vorticity.rhoTheta.rhoDerivative
  omegaRhoTheta := fun jet => jet.vorticity.rhoTheta.value
  radialOmegaPhiTheta := fun jet => jet.vorticity.phiTheta.rhoDerivative
  latitudeOmegaRhoTheta := fun jet => jet.vorticity.rhoTheta.latitudeDerivative
  omegaPhiTheta := fun jet => jet.vorticity.phiTheta.value

theorem eccentricityQuadraticCorrection_axisymmetricEllipsoid
    (jet : EllipsoidEccentricityJet) :
    eccentricityQuadraticCorrection axisymmetricEllipsoidEccentricityData jet =
      jet.quadraticCorrection := by
  apply Prod.ext <;>
    simp [eccentricityQuadraticCorrection, axisymmetricEllipsoidEccentricityData,
      phiCoordinateCovector, thetaCoordinateCovector,
      EllipsoidEccentricityJet.quadraticCorrection]

/-- CCY23 equation (5.8), with the exact candidate from equation (2.9) and an explicit uniform
remainder constant on `0 < mu < 1/2`. -/
theorem eccentricity_expansion_axisymmetric_ellipsoid :
    eccentricity_expansion_statement axisymmetricEllipsoidEccentricityData := by
  intro jet
  refine ⟨4 * |jet.vorticity.phiTheta.value| +
      2 * |jet.vorticity.phiTheta.latitudeDerivative|, 1 / 2, ?_, by norm_num, ?_⟩
  · positivity
  intro eccentricity positive lessThanHalf _
  rw [eccentricityQuadraticCorrection_axisymmetricEllipsoid]
  exact jet.exactCandidate_expansion_norm_le positive lessThanHalf

end RiemannianFluids.Literature.CCY23
