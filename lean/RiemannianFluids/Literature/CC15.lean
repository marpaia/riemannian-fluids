import Mathlib.Data.ENNReal.Basic
import RiemannianFluids.Geometry.SpaceForms

/-!
# CC15: stationary Liouville theorems on hyperbolic space

The three conclusions of Theorem 1.1 are separate source signatures.  Their shared data exposes
smoothness, coclosedness, the deformation-viscosity momentum residual, Dirichlet energy,
essential boundedness, the `L²` norm, and harmonic gradients as distinct observables.
-/

namespace RiemannianFluids.Literature.CC15

/-- Observable realization of the stationary equation and function spaces in CC15 Theorem 1.1. -/
structure StationaryLiouvilleData (Velocity Pressure Potential : Type*) where
  isSmoothVelocity : Velocity → Prop
  isSmoothPressure : Pressure → Prop
  divergenceResidualNormSq : Velocity → ℝ
  deformationMomentumResidualNormSq : Velocity → Pressure → ℝ
  dirichletIntegral : Velocity → ENNReal
  essentialSupremum : Velocity → ENNReal
  l2NormSq : Velocity → ENNReal
  isHarmonic : Potential → Prop
  differential : Potential → Velocity

/-- The common smooth, divergence-free, finite-Dirichlet-energy stationary solution class. -/
def IsStationaryLiouvilleSolution
    {Velocity Pressure Potential : Type*}
    (data : StationaryLiouvilleData Velocity Pressure Potential)
    (velocity : Velocity) (pressure : Pressure) : Prop :=
  data.isSmoothVelocity velocity ∧
    data.isSmoothPressure pressure ∧
    data.divergenceResidualNormSq velocity = 0 ∧
    data.deformationMomentumResidualNormSq velocity pressure = 0 ∧
    data.dirichletIntegral velocity ≠ ⊤

/-- The additional `L∞` hypothesis in the two-dimensional and high-dimensional cases. -/
def IsEssentiallyBounded
    {Velocity Pressure Potential : Type*}
    (data : StationaryLiouvilleData Velocity Pressure Potential)
    (velocity : Velocity) : Prop :=
  data.essentialSupremum velocity ≠ ⊤

/-- Source signature for the `N = 3,4` conclusion of CC15 Theorem 1.1. -/
def stationary_liouville_dimensions_three_four_statement
    {Point Velocity Pressure Potential : Type*} [Zero Velocity]
    (geometry : RiemannianGeometryProfile Point)
    (data : StationaryLiouvilleData Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry N a →
    (N = 3 ∨ N = 4) →
      ∀ velocity pressure,
        IsStationaryLiouvilleSolution data velocity pressure → velocity = 0

/-- Source signature for the `N = 2` conclusion: every additionally bounded solution is the
`L²` differential of a harmonic function. -/
def stationary_liouville_dimension_two_statement
    {Point Velocity Pressure Potential : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (data : StationaryLiouvilleData Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry N a →
    N = 2 →
      ∀ velocity pressure,
        IsStationaryLiouvilleSolution data velocity pressure →
          IsEssentiallyBounded data velocity →
            ∃ potential,
              data.isHarmonic potential ∧
                data.differential potential = velocity ∧
                data.l2NormSq velocity ≠ ⊤

/-- Source signature for the `N ≥ 5` conclusion of CC15 Theorem 1.1. -/
def stationary_liouville_dimensions_at_least_five_statement
    {Point Velocity Pressure Potential : Type*} [Zero Velocity]
    (geometry : RiemannianGeometryProfile Point)
    (data : StationaryLiouvilleData Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry N a →
    5 ≤ N →
      ∀ velocity pressure,
        IsStationaryLiouvilleSolution data velocity pressure →
          IsEssentiallyBounded data velocity → velocity = 0

end RiemannianFluids.Literature.CC15
