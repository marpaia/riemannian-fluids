import RiemannianFluids.ProofStatus
import RiemannianFluids.Operators.GeometricIdentities

/-!
# CCD17 source contract

This module places the existing Chan--Czubak--Disconzi equation (1.3) route at its permanent literature-facing path. The statement is the
analysis-positive divergence-free specialization

    L_Def u = L_Hodge u - 2 Ric(u).

The terminal theorem is checked, but it remains an interface result: the Weitzenbock and symmetric-gradient identities are explicit parameters. Its
clean axiom audit therefore means only that the algebra and divergence-free cancellation are proved from those visible hypotheses.
-/

namespace RiemannianFluids

open Bundle
open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- CCD17 equation (1.3), after imposing divergence-freeness and translating to the repository's positive convention. -/
def ccd17DivergenceFreeStatement
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  ∀ field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity),
    IsDivergenceFree I connection (regularity + 1) smooth field →
      operators.deformationLaplacian field =
        operators.hodgeLaplacian I regularity connection smooth field -
          (2 : ℝ) • operators.ricci.action I regularity field

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The checked CCD17 interface route, tagged as a literature-facing terminal declaration. -/
@[literature_terminal]
theorem ccd17_divergence_free_contract_checked
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators) :
    ccd17DivergenceFreeStatement I regularity connection smooth operators := by
  intro field hdiv
  exact ccd17_divfree_def_hodge I regularity connection smooth operators hWeitzenbock hSymmetric field hdiv

/-- Observable witness family for the hyperbolic Hodge-Stokes energy obstruction of Theorems 3.2--3.3. -/
structure CCD17HyperbolicEnergyData (Velocity Force : Type*) where
  isHyperbolicPlane : ℝ → Prop
  witnessVelocity : ℝ → Velocity
  witnessForce : ℝ → Force
  satisfiesHodgeStokes : ℝ → Velocity → Force → Prop
  energyLeftHandSide : ℝ → Velocity → ℝ
  dataRightHandSide : ℝ → Velocity → Force → ℝ
  isNonzeroL2HarmonicGradient : ℝ → Velocity → Prop
  hasWitnessFormula3_12 : ℝ → Prop
  hasForcingFormula3_13 : ℝ → Prop
  hasVelocityNormFormula3_14 : ℝ → Prop
  hasDissipationFormula3_15 : ℝ → ℝ → Prop
  hasForcingBound3_16 : ℝ → Prop
  hasContradiction3_17 : ℝ → ℝ → Prop
  satisfiesClassicalHodgeNavierStokes : ℝ → Velocity → Force → Prop
  pressureFormula3_19 : ℝ → Prop
  energyEquality3_23WouldForceZero : ℝ → Prop

/-- No positive absolute constant controls the expected global energy estimate uniformly over terminal time. -/
def ccd17HyperbolicEnergyObstructionStatement
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force) : Prop :=
  ∀ a : ℝ, 0 < a → data.isHyperbolicPlane a →
    ∀ constant : ℝ, 0 < constant →
      ∃ T : ℝ, 0 < T ∧
        data.satisfiesHodgeStokes T (data.witnessVelocity T) (data.witnessForce T) ∧
        constant * data.dataRightHandSide T (data.witnessVelocity T) (data.witnessForce T) <
          data.energyLeftHandSide T (data.witnessVelocity T)

/-- CCD17 Theorem 3.3: the same witness, with pressure (3.19), obstructs the classical nonlinear estimate. -/
def ccd17HyperbolicNavierStokesEnergyObstructionStatement
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force) : Prop :=
  ∀ a : ℝ, 0 < a → data.isHyperbolicPlane a →
    ∀ constant : ℝ, 0 < constant →
      ∃ T : ℝ, 0 < T ∧
        data.satisfiesClassicalHodgeNavierStokes T
          (data.witnessVelocity T) (data.witnessForce T) ∧
        constant * data.dataRightHandSide T
          (data.witnessVelocity T) (data.witnessForce T) <
          data.energyLeftHandSide T (data.witnessVelocity T)

/-- CCD17 Theorem 3.6: the expected rough-gradient energy equality is incompatible with the weak witness. -/
def ccd17HyperbolicEnergyEqualityObstructionStatement
    {Velocity Force : Type*}
    (data : CCD17HyperbolicEnergyData Velocity Force) : Prop :=
  ∀ a : ℝ, 0 < a → data.isHyperbolicPlane a →
    ∃ T : ℝ, 0 < T ∧
      data.satisfiesHodgeStokes T (data.witnessVelocity T) (data.witnessForce T) ∧
      data.energyEquality3_23WouldForceZero T

/-- The three first-order relativistic models discussed in Section 5. -/
inductive CCD17RelativisticModel where
  | lichnerowicz
  | choquetBruhat
  | freistuehlerTemple
  deriving DecidableEq

/-- Observable spatial viscous terms before and after taking the nonrelativistic limit. -/
structure CCD17RelativisticLimitData (Velocity Term : Type*) where
  nonrelativisticLimit : CCD17RelativisticModel → Velocity → Term
  deformationViscosity : Velocity → Term
  hasProjectorExpansion : Velocity → Prop
  hasFourVelocityExpansion : Velocity → Prop
  hasIncompressibleLimit : Velocity → Prop
  hasEckartLimitEquation4_16 : Velocity → Prop
  hasLichnerowiczEnthalpyLimit : Velocity → Prop
  hasChoquetBruhatShearLimit : Velocity → Prop
  hasFreistuehlerTempleShearLimit : Velocity → Prop

/-- Section 5: each cited relativistic stress model limits to the divergence of twice the deformation tensor. -/
def ccd17RelativisticLimitStatement
    {Velocity Term : Type*}
    (data : CCD17RelativisticLimitData Velocity Term) : Prop :=
  ∀ model velocity,
    data.nonrelativisticLimit model velocity = data.deformationViscosity velocity


end RiemannianFluids
