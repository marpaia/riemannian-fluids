import RiemannianFluids.Operators.ConstructedHodge
import RiemannianFluids.Geometry.SpaceForms

/-!
# CCD17: curvature comparison of viscosity operators

The literature namespace exposes the fully constructed divergence-free comparison.  Its geometric
hypotheses remain visible in the inferred theorem type and are documented in the claim crosswalk.
-/

namespace RiemannianFluids.Literature.CCD17

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

/-- Observable terms in the global Hodge--Stokes estimate ruled out by CCD17 Theorems 3.2
and 3.3.  The two instances used below distinguish the weak and classical solution classes. -/
structure HodgeEnergyEstimateData (Initial Force Solution : Type*) where
  isAdmissibleInitial : Initial → Prop
  isAdmissibleForce : ℝ → Force → Prop
  isSolutionOn : ℝ → Initial → Force → Solution → Prop
  velocitySupNormSq : ℝ → Solution → ℝ
  gradientEnergy : ℝ → Solution → ℝ
  initialNormSq : Initial → ℝ
  forceDualNormSq : ℝ → Force → ℝ

/-- A single positive constant controls the source energy estimate for every terminal time and
every solution in the selected solution class. -/
def HasUniformHodgeEnergyEstimate
    {Initial Force Solution : Type*}
    (data : HodgeEnergyEstimateData Initial Force Solution) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    ∀ terminalTime, 0 < terminalTime → ∀ initial force solution,
      data.isAdmissibleInitial initial →
      data.isAdmissibleForce terminalTime force →
      data.isSolutionOn terminalTime initial force solution →
        data.velocitySupNormSq terminalTime solution +
            data.gradientEnergy terminalTime solution ≤
          constant *
            (data.initialNormSq initial + data.forceDualNormSq terminalTime force)

/-- Source signature for CCD17 Theorems 3.2--3.3: on `H²(-a²)`, neither the stated weak
solution class nor its classical subclass admits a terminal-time-uniform Hodge energy bound. -/
def hyperbolic_energy_obstruction_statement
    {Point WeakInitial WeakForce WeakSolution
      ClassicalInitial ClassicalForce ClassicalSolution : Type*}
    (geometry : RiemannianGeometryProfile Point) (a : ℝ)
    (weakData : HodgeEnergyEstimateData WeakInitial WeakForce WeakSolution)
    (classicalData :
      HodgeEnergyEstimateData ClassicalInitial ClassicalForce ClassicalSolution) : Prop :=
  IsHyperbolicSpaceForm geometry 2 a →
    ¬ HasUniformHodgeEnergyEstimate weakData ∧
      ¬ HasUniformHodgeEnergyEstimate classicalData

/-- The three first-order relativistic stress prescriptions compared in CCD17 Section 5. -/
inductive FirstOrderRelativisticStress where
  | lichnerowicz
  | choquetBruhat
  | freistuehlerTemple
  deriving DecidableEq

/-- Spatial nonrelativistic-limit observables for the three relativistic stress models. -/
structure RelativisticStressLimitData (Velocity SpatialForce : Type*) where
  spatialMomentumLimit : FirstOrderRelativisticStress → Velocity → SpatialForce
  divergenceTwoDeformation : Velocity → SpatialForce

/-- Source signature for CCD17 Section 5: every listed relativistic stress has the same
`div(2 Def v)` contribution in the nonrelativistic spatial momentum equation. -/
def relativistic_first_order_limit_statement
    {Velocity SpatialForce : Type*}
    (data : RelativisticStressLimitData Velocity SpatialForce) : Prop :=
  ∀ model velocity,
    data.spatialMomentumLimit model velocity = data.divergenceTwoDeformation velocity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The constructed divergence-free identity between deformation and Hodge viscosity. -/
abbrev divergenceFree_deformation_eq_hodge_sub_two_ricci
    [IsManifold I 3 M]
    (regularity : ℕ∞ω) (hreg : (2 : ℕ∞ω) ≤ regularity + 1)
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection.connection x)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (hdiv : IsDivergenceFree I connection regularity smooth field)
    (x : M) (w : TangentSpace I x) :=
  _root_.RiemannianFluids.ccd17_divfree_def_hodge_constructed I regularity hreg
    connection smooth regular field hdiv x w

end RiemannianFluids.Literature.CCD17
