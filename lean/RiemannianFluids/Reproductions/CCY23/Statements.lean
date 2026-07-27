import Mathlib.Analysis.Normed.Module.Basic
import RiemannianFluids.ProofStatus

/-!
# CCY23 statement contracts

Source: Chan--Czubak--Yoneda, *The restriction problem on the ellipsoid*,
arXiv:2203.16050v1, Theorem 1.1 and equations (5.8)--(5.9).

The restriction theorem assumes an ambient field tangent to the ellipsoid and divergence-free
both in the ambient space and intrinsically.  Its eccentricity expansion is even through order
two, with an `O(mu^4)` remainder as the ellipsoid approaches the sphere.
-/

namespace RiemannianFluids

/-- All operator-valued observables appearing in the invariant restriction formula. -/
structure CCY23RestrictionData (Field Form : Type*) where
  axisScale : ℝ
  isTangentialToEllipsoid : Field → Prop
  isAmbientDivergenceFree : Field → Prop
  isEllipsoidDivergenceFree : Field → Prop
  ambientHodgeRestriction : Field → Form
  ellipsoidHodge : Field → Form
  extensionCorrection : Field → Form
  lieDerivativeCorrection : Field → Form
  radialDerivativeCorrection : Field → Form
  hasEllipsoidMetricAndVolumeIdentities : Prop
  hasAmbientHodgeComponentFormula : Field → Prop
  hasIntrinsicHodgeComponentFormula : Field → Prop
  hasExtensionOperatorComponents : Field → Prop
  hasRadialLieDerivativeComponents : Field → Prop
  hasLatitudeCorrectionComponent : Field → Prop
  dPhiComponentsAgree : Field → Prop
  dThetaComponentsAgree : Field → Prop

/-- Theorem 1.1, grouped into its invariant intrinsic and extrinsic correction terms. -/
def ccy23InvariantRestrictionStatement
    {Field Form : Type*} [AddCommGroup Form]
    (data : CCY23RestrictionData Field Form) : Prop :=
  0 < data.axisScale →
  ∀ field,
    data.isTangentialToEllipsoid field →
      data.isAmbientDivergenceFree field →
        data.isEllipsoidDivergenceFree field →
          data.ambientHodgeRestriction field =
            data.ellipsoidHodge field +
              data.extensionCorrection field +
              data.lieDerivativeCorrection field +
              data.radialDerivativeCorrection field

/-- Section 4's ambient extension, including the radial scalar solving equation (4.6). -/
structure CCY23DivergenceFreeExtensionData (SurfaceField AmbientField : Type*) where
  axisScale : ℝ
  ambientExtension : SurfaceField → AmbientField
  isSmoothSurfaceField : SurfaceField → Prop
  isIntrinsicallyDivergenceFree : SurfaceField → Prop
  isSmoothAmbientField : AmbientField → Prop
  restrictsTo : AmbientField → SurfaceField → Prop
  isTangentialOnEllipsoid : AmbientField → Prop
  isAmbientDivergenceFree : AmbientField → Prop
  radialComponentSolvesEquation4_6 : AmbientField → Prop

/-- Section 4: every smooth intrinsic solenoidal field has a smooth tangent ambient extension that is also ambient-solenoidal. -/
def ccy23DivergenceFreeExtensionStatement
    {SurfaceField AmbientField : Type*}
    (data : CCY23DivergenceFreeExtensionData SurfaceField AmbientField) : Prop :=
  0 < data.axisScale →
  ∀ field,
    data.isSmoothSurfaceField field →
      data.isIntrinsicallyDivergenceFree field →
        let extension := data.ambientExtension field
        data.isSmoothAmbientField extension ∧
          data.restrictsTo extension field ∧
          data.isTangentialOnEllipsoid extension ∧
          data.isAmbientDivergenceFree extension ∧
          data.radialComponentSolvesEquation4_6 extension

/-- Observable terms in the even eccentricity expansion (5.8)--(5.9). -/
structure CCY23EccentricityData (Field Form : Type*) [NormedAddCommGroup Form] where
  candidate : ℝ → Field → Form
  sphericalTerm : Field → Form
  quadraticTerm : Field → Form
  remainder : ℝ → Field → Form
  hasEccentricityIdentities5_2 : Prop
  hasGeometricSeries5_3 : Prop
  hasSquaredDenominatorSeries5_4 : Prop
  hasExtensionFormula5_5 : Field → Prop
  hasExtensionPhiExpansion5_6 : Field → Prop
  hasExtensionThetaExpansion5_7 : Field → Prop
  hasFormCoefficient5_8 : Field → Prop
  hasVectorCoefficient5_9 : Field → Prop

/-- The paper's `mu^0 + mu^2 + O(mu^4)` expansion as `mu -> 0+`. -/
def ccy23EccentricityExpansionStatement
    {Field Form : Type*} [NormedAddCommGroup Form] [NormedSpace ℝ Form]
    (data : CCY23EccentricityData Field Form) : Prop :=
  ∀ field,
    (∀ μ : ℝ, 0 < μ → μ < 1 →
      data.candidate μ field =
        data.sphericalTerm field + μ ^ 2 • data.quadraticTerm field + data.remainder μ field) ∧
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ μ : ℝ, 0 < μ → μ < δ → ‖data.remainder μ field‖ ≤ C * μ ^ 4


end RiemannianFluids
