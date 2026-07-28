import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import RiemannianFluids.Geometry.SpaceForms

/-!
# Harmonic-potential decay and energy contracts

CC13, CC15, and CC21 repeatedly use the same analytic chain: solve a Dirichlet problem at
infinity, prove exponential decay of the gradient, infer square integrability, and then control
the Hessian or deformation dissipation.  These predicates expose that chain over an actual
Mathlib measure instead of storing conclusions in paper-specific `hasX : Prop` fields.

The differential operators which produce the scalar norm functions remain explicit data until
the corresponding global noncompact-manifold constructions are available in Mathlib.  The
integrability conclusions themselves use Mathlib's `MeasureTheory.Integrable`.
-/

namespace RiemannianFluids

open MeasureTheory

/-- Second-order pointwise observables attached to a harmonic-potential profile. -/
structure HarmonicPotentialEnergyProfile
    (Point Potential OneForm : Type*) [MeasurableSpace Point] where
  harmonic : HarmonicPotentialProfile Point Potential OneForm
  volumeMeasure : Measure Point
  hessianNormAt : Potential → Point → ℝ
  deformationNormAt : Potential → Point → ℝ
  gradientEnergyDerivativeNormAt : Potential → Point → ℝ
  ricciQuadraticAt : Potential → Point → ℝ

/-- Smooth, bounded, nonconstant, harmonic potential—the seed used by the hyperbolic
nonuniqueness constructions. -/
def IsBoundedNonconstantHarmonicPotential
    {Point Potential OneForm : Type*}
    (data : HarmonicPotentialProfile Point Potential OneForm)
    (potential : Potential) : Prop :=
  data.isSmooth potential ∧ data.isBounded potential ∧
    data.isNonconstant potential ∧ data.isHarmonic potential

/-- The source-level estimate `|∇F|(x) ≤ C ‖φ'‖∞ exp (-δ ρ(x))`. -/
def HasPointwiseExponentialGradientDecay
    {Point Potential OneForm : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (data : HarmonicPotentialProfile Point Potential OneForm)
    (potential : Potential) (boundaryDerivativeNorm constant decayRate : ℝ) : Prop :=
  0 ≤ boundaryDerivativeNorm ∧ 0 ≤ constant ∧ 0 < decayRate ∧
    ∀ point,
      data.gradientNormAt potential point ≤
        constant * boundaryDerivativeNorm *
          Real.exp (-decayRate * geometry.distanceFromBasepoint point)

/-- The literal finite-energy condition `|∇F|² ∈ L¹(M,dvol)`. -/
def HasSquareIntegrableGradient
    {Point Potential OneForm : Type*}
    [MeasurableSpace Point]
    (data : HarmonicPotentialEnergyProfile Point Potential OneForm)
    (potential : Potential) : Prop :=
  Integrable
    (fun point => data.harmonic.gradientNormAt potential point ^ 2)
    data.volumeMeasure

/-- The Hessian energy density is integrable.  This is the analytic content behind the
paper notation `∇dF ∈ L²`. -/
def HasSquareIntegrableHessian
    {Point Potential OneForm : Type*}
    [MeasurableSpace Point]
    (data : HarmonicPotentialEnergyProfile Point Potential OneForm)
    (potential : Potential) : Prop :=
  Integrable (fun point => data.hessianNormAt potential point ^ 2) data.volumeMeasure

/-- The deformation energy density is integrable. -/
def HasSquareIntegrableDeformation
    {Point Potential OneForm : Type*}
    [MeasurableSpace Point]
    (data : HarmonicPotentialEnergyProfile Point Potential OneForm)
    (potential : Potential) : Prop :=
  Integrable (fun point => data.deformationNormAt potential point ^ 2) data.volumeMeasure

/-- The Section 4 quantity `|∇ |∇F|²|` is integrable. -/
def HasIntegrableGradientEnergyDerivative
    {Point Potential OneForm : Type*}
    [MeasurableSpace Point]
    (data : HarmonicPotentialEnergyProfile Point Potential OneForm)
    (potential : Potential) : Prop :=
  Integrable
    (fun point => data.gradientEnergyDerivativeNormAt potential point)
    data.volumeMeasure

/-- Integrated Bochner identity used to turn curvature into Hessian dissipation. -/
def HasIntegratedBochnerDissipationIdentity
    {Point Potential OneForm : Type*}
    [MeasurableSpace Point]
    (data : HarmonicPotentialEnergyProfile Point Potential OneForm)
    (potential : Potential) : Prop :=
  (∫ point, data.hessianNormAt potential point ^ 2 ∂data.volumeMeasure) =
    -(∫ point, data.ricciQuadraticAt potential point ∂data.volumeMeasure)

end RiemannianFluids
