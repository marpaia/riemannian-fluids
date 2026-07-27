import RiemannianFluids.Reproductions.CC15.ProofRoute
import RiemannianFluids.ProofStatus

/-!
# CC15 proof route

Source: Chan--Czubak, *Liouville theorems for the Stationary Navier Stokes equation
on a hyperbolic space*, arXiv:1501.04928v1, Theorem 1.1.

The theorem is dimension-sensitive.  Finite Dirichlet integral alone gives vanishing in
dimensions three and four.  In dimension two, an additional `L^infinity` hypothesis yields
an `L^2` harmonic gradient, which need not vanish.  In dimensions at least five, the same
additional boundedness hypothesis restores vanishing.
-/

namespace RiemannianFluids

/-- The dimension-dependent conclusion shared by Theorem 1.1 and Corollary 1.3. -/
def cc15LiouvilleConclusion
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential)
    (N : ℕ) (a : ℝ) (velocity : Velocity) : Prop :=
  ((N = 3 ∨ N = 4) → data.isZero velocity) ∧
    (N = 2 → data.isEssentiallyBounded velocity →
      ∃ potential,
        data.isHarmonicPotential N a potential ∧
          data.isGradientOf velocity potential ∧
          data.isSquareIntegrable velocity) ∧
    (5 ≤ N → data.isEssentiallyBounded velocity → data.isZero velocity)

/-- The exact three-branch conclusion of CC15 Theorem 1.1. -/
def cc15StationaryLiouvilleStatement
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential) : Prop :=
  ∀ N a velocity pressure,
    2 ≤ N →
      0 < a →
        data.isHyperbolicSpace N a →
          data.isSmoothVelocity velocity →
            data.isSmoothPressure pressure →
                data.isDivergenceFree velocity →
                data.satisfiesStationaryDeformationNS N a velocity pressure →
                  data.hasFiniteDirichletIntegral velocity →
                    cc15LiouvilleConclusion data N a velocity

/-- Corollary 1.3: the same conclusion for either the rough/Bochner or Hodge viscosity operator. -/
def cc15AlternativeViscosityLiouvilleStatement
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential) : Prop :=
  ∀ N a velocity pressure,
    2 ≤ N →
      0 < a →
        data.isHyperbolicSpace N a →
          data.isSmoothVelocity velocity →
            data.isSmoothPressure pressure →
              data.isDivergenceFree velocity →
                data.hasFiniteDirichletIntegral velocity →
                  (data.satisfiesStationaryBochnerNS N a velocity pressure →
                    cc15LiouvilleConclusion data N a velocity) ∧
                  (data.satisfiesStationaryHodgeNS N a velocity pressure →
                    cc15LiouvilleConclusion data N a velocity)

@[literature_terminal]
theorem cc15_theorem_1_1
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential) :
    cc15StationaryLiouvilleStatement data := by
  intro N a velocity pressure hN ha hGeometry hSmoothVelocity hSmoothPressure
    hDivergenceFree hEquation hDirichlet
  refine ⟨?_, ?_, ?_⟩
  · intro hDimension
    exact cc15_vanishing_in_dimensions_three_and_four data N a velocity pressure
      hDimension ha hGeometry hSmoothVelocity hSmoothPressure hDivergenceFree hEquation hDirichlet
  · intro hDimension hBounded
    subst N
    exact cc15_harmonic_gradient_in_dimension_two data a velocity pressure ha hGeometry
      hSmoothVelocity hSmoothPressure hDivergenceFree hEquation hDirichlet hBounded
  · intro hDimension hBounded
    exact cc15_vanishing_in_dimensions_at_least_five data N a velocity pressure
      hDimension ha hGeometry hSmoothVelocity hSmoothPressure hDivergenceFree hEquation hDirichlet hBounded

/-- CC15 Corollary 1.3. The paper repeats the argument with the Bochner and Hodge equations; those two source branches remain open independently. -/
@[proof_obligation]
theorem cc15_corollary_1_3_alternative_viscosities
    {Velocity Pressure Potential : Type*}
    (data : CC15Data Velocity Pressure Potential) :
    cc15AlternativeViscosityLiouvilleStatement data := by
  sorry

end RiemannianFluids
