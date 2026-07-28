import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Ring.Periodic

/-!
# Closed surfaces of revolution

Mathlib supplies the one-dimensional differentiability and periodicity notions used below, but
does not currently bundle the profile geometry of a closed surface of revolution.  This file
records that small missing layer for the thin-shell papers without replacing the profile by an
opaque geometric hypothesis.
-/

namespace RiemannianFluids

noncomputable section

/-- A periodic meridian profile together with the derivatives and curvature observables used in
orthogonal coordinates on a surface of revolution. -/
structure ClosedRevolutionProfile where
  period : ℝ
  radius : ℝ → ℝ
  height : ℝ → ℝ
  radiusDerivative : ℝ → ℝ
  heightDerivative : ℝ → ℝ
  radiusSecondDerivative : ℝ → ℝ
  heightSecondDerivative : ℝ → ℝ
  meridianCurvature : ℝ → ℝ
  azimuthalCurvature : ℝ → ℝ
  gaussCurvature : ℝ → ℝ

/-- The literal smooth, closed, positive-radius, unit-speed profile assumptions used for the
torus-type surfaces of revolution in WBS26.  The signs of the two principal curvatures encode
the normal convention through the displayed formulas. -/
def IsSmoothClosedUnitSpeedRevolutionProfile (profile : ClosedRevolutionProfile) : Prop :=
  0 < profile.period ∧
    ContDiff ℝ ⊤ profile.radius ∧
    ContDiff ℝ ⊤ profile.height ∧
    Function.Periodic profile.radius profile.period ∧
    Function.Periodic profile.height profile.period ∧
    (∀ s, 0 < profile.radius s) ∧
    (∀ s, HasDerivAt profile.radius (profile.radiusDerivative s) s) ∧
    (∀ s, HasDerivAt profile.height (profile.heightDerivative s) s) ∧
    (∀ s, HasDerivAt profile.radiusDerivative (profile.radiusSecondDerivative s) s) ∧
    (∀ s, HasDerivAt profile.heightDerivative (profile.heightSecondDerivative s) s) ∧
    (∀ s, profile.radiusDerivative s ^ 2 + profile.heightDerivative s ^ 2 = 1) ∧
    (∀ s,
      profile.meridianCurvature s =
        profile.radiusDerivative s * profile.heightSecondDerivative s -
          profile.heightDerivative s * profile.radiusSecondDerivative s) ∧
    (∀ s,
      profile.azimuthalCurvature s =
        profile.heightDerivative s / profile.radius s) ∧
    ∀ s,
      profile.gaussCurvature s =
        profile.meridianCurvature s * profile.azimuthalCurvature s

end

end RiemannianFluids
