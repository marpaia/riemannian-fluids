import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

/-- Component observables in the differential-form eccentricity expansion (5.8). -/
structure EllipsoidEccentricityExpansionData
    (Argument Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℝ Value] where
  latitude : Argument → ℝ
  candidate : ℝ → Argument → Value
  sphericalTerm : Argument → Value
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
`mu = sqrt((a^2-1)/a^2)`: the displayed residual is locally `O(mu^4)` as `mu -> 0+`. -/
def eccentricity_expansion_statement
    {Argument Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (data : EllipsoidEccentricityExpansionData Argument Value) : Prop :=
  ∀ argument,
    ∃ constant cutoff : ℝ, 0 ≤ constant ∧ 0 < cutoff ∧
      ∀ eccentricity,
        0 < eccentricity → eccentricity < cutoff → eccentricity < 1 →
          ‖data.candidate eccentricity argument - data.sphericalTerm argument -
              eccentricity ^ 2 • eccentricityQuadraticCorrection data argument‖ ≤
            constant * eccentricity ^ 4

end RiemannianFluids.Literature.CCY23
