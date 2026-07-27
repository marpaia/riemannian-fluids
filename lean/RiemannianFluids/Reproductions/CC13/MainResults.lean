import RiemannianFluids.Reproductions.CC13.ProofRoute
import RiemannianFluids.ProofStatus

/-!
# CC13 proof route

Source: Chan--Czubak, *Non-uniqueness of the Leray--Hopf solutions in the
hyperbolic setting*, arXiv:1006.2819v1, Theorem 1.2.

For every `a > 0`, the paper works on the hyperbolic plane of sectional curvature
`-a^2` and constructs multiple Leray--Hopf solutions from a nonconstant bounded harmonic
function whose differential is square integrable.
-/

namespace RiemannianFluids

/-! ## Section 1: stated results

The paper opens with the Euclidean Prodi--Serrin--Ladyzhenskaya theorem as a quoted
background result, then states its hyperbolic and pinched-curvature conclusions.  These
nodes are kept even when a result is imported or is not needed by the registered terminal:
the purpose of this module is to preserve the source's theorem graph.
-/

/-- Observables in the quoted Prodi--Serrin--Ladyzhenskaya theorem, CC13 Theorem 1.1. -/
structure CC13ProdiSerrinData (Initial Solution : Type*) where
  euclideanLerayHopf : LerayHopfFramework Initial Solution
  isProdiSerrinIntegrable : ℝ → ℝ → Solution → Prop
  isSmoothForPositiveTime : Solution → Prop

/-- CC13 Theorem 1.1: the quoted Euclidean conditional regularity and uniqueness result. -/
def cc13ProdiSerrinLadyzhenskayaStatement
    {Initial Solution : Type*}
    (data : CC13ProdiSerrinData Initial Solution) : Prop :=
  ∀ initial solution p q,
    IsLerayHopfSolution data.euclideanLerayHopf initial solution →
      0 < p → 3 < q → 2 / p + 3 / q = 1 →
        data.isProdiSerrinIntegrable p q solution →
          data.isSmoothForPositiveTime solution ∧
            ∀ other,
              IsLerayHopfSolution data.euclideanLerayHopf initial other →
                other = solution

/-- CC13 Theorem 1.1 is an imported background theorem, retained as a source node. -/
@[proof_obligation]
theorem cc13_theorem_1_1_prodi_serrin_ladyzhenskaya
    {Initial Solution : Type*}
    (data : CC13ProdiSerrinData Initial Solution) :
    cc13ProdiSerrinLadyzhenskayaStatement data := by
  sorry

/-- Geometry and solution observables for CC13 Theorem 1.6 and Corollaries 1.4, 1.7, and 3.4. -/
structure CC13PinchedData (Initial Solution Potential StationarySolution : Type*) where
  isHyperbolicSpace : ℕ → ℝ → Prop
  isCompleteSimplyConnectedPinched : ℕ → ℝ → ℝ → Prop
  modifiedLerayHopf : ℝ → ℝ → LerayHopfFramework Initial Solution
  initialFromPotential : ℝ → ℝ → Potential → Initial
  solutionFromPotential : ℝ → ℝ → Potential → ℝ → Solution
  seedPotential : ℝ → ℝ → Potential
  isBoundedNonconstantHarmonic : ℝ → ℝ → Potential → Prop
  hasGradientDecayAtRate : ℝ → ℝ → ℝ → Potential → Prop
  harmonicGradientHasFiniteEnergy : ℝ → ℝ → Potential → Prop
  hyperbolicStationarySolution : ℕ → ℝ → StationarySolution
  modifiedStationarySolution : ℕ → ℝ → ℝ → StationarySolution
  isNontrivialBoundedHyperbolicStationarySolution : ℕ → ℝ → StationarySolution → Prop
  isNontrivialBoundedModifiedStationarySolution : ℕ → ℝ → ℝ → StationarySolution → Prop

/-- CC13 Corollary 1.4: every negatively curved space form has a nontrivial bounded stationary solution. -/
def cc13HyperbolicLiouvilleFailureStatement
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) : Prop :=
  ∀ n a, 2 ≤ n → 0 < a → data.isHyperbolicSpace n a →
    ∃ solution,
      data.isNontrivialBoundedHyperbolicStationarySolution n a solution

/-- CC13 Theorem 1.6: nonuniqueness for the modified equation on a pinched negatively curved surface. -/
def cc13PinchedModifiedNonuniquenessStatement
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) : Prop :=
  ∀ a b, 0 < a → 0 < b → b / 2 < a → a ≤ b →
    data.isCompleteSimplyConnectedPinched 2 a b →
      ∃ initial solution₁ solution₂,
        IsLerayHopfSolution (data.modifiedLerayHopf a b) initial solution₁ ∧
          IsLerayHopfSolution (data.modifiedLerayHopf a b) initial solution₂ ∧
          solution₁ ≠ solution₂

/-- CC13 Corollary 1.7: the modified stationary equation fails the Liouville property in every dimension. -/
def cc13PinchedLiouvilleFailureStatement
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) : Prop :=
  ∀ n a b, 2 ≤ n → 0 < a → a ≤ b →
    data.isCompleteSimplyConnectedPinched n a b →
      ∃ solution,
        data.isNontrivialBoundedModifiedStationarySolution n a b solution

/-- The two-dimensional constant-curvature identity `Scal = 2K = -2a^2`. -/
def cc13HyperbolicCurvatureModelStatement
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential) : Prop :=
  ∀ a : ℝ, data.isHyperbolicPlane a → data.scalarCurvature a = -2 * a ^ 2

/-- Section 2.1: in dimension two, constant sectional curvature `-a²` contracts to scalar curvature `-2a²`. -/
@[proof_obligation]
theorem cc13_hyperbolic_plane_scalar_curvature
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential) :
    ∀ a : ℝ, data.isHyperbolicPlane a →
      data.scalarCurvature a = -2 * a ^ 2 := by
  sorry

/-- The geometric model used by CC13, exposed as a routed claim instead of an unconnected statement. -/
@[literature_terminal]
theorem cc13_hyperbolic_curvature_model
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential) :
    cc13HyperbolicCurvatureModelStatement data := by
  exact cc13_hyperbolic_plane_scalar_curvature data

/-- Theorem 1.2: two distinct Leray--Hopf solutions share the same initial datum on `H^2(-a^2)`. -/
def cc13LerayHopfNonuniquenessStatement
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential) : Prop :=
  ∀ a : ℝ, 0 < a → data.isHyperbolicPlane a →
    ∃ initial solution₁ solution₂,
      IsLerayHopfSolution (data.lerayHopf a) initial solution₁ ∧
        IsLerayHopfSolution (data.lerayHopf a) initial solution₂ ∧
        solution₁ ≠ solution₂

@[literature_terminal]
theorem cc13_theorem_1_2
    {Initial Solution Potential : Type*}
    (data : CC13Data Initial Solution Potential) :
    cc13LerayHopfNonuniquenessStatement data := by
  intro a ha hGeometry
  obtain ⟨potential, hPotential, hFiniteEnergy, hDissipation⟩ :=
    cc13_harmonic_seed_exists data a ha hGeometry
  let initial := data.initialFromPotential a potential
  let solution₁ := data.solutionFromPotential a potential 0
  let solution₂ := data.solutionFromPotential a potential 1
  refine ⟨initial, solution₁, solution₂, ?_, ?_, ?_⟩
  · exact cc13_parametrized_solution_is_leray_hopf
      data a ha hGeometry potential hPotential hFiniteEnergy hDissipation 0
  · exact cc13_parametrized_solution_is_leray_hopf
      data a ha hGeometry potential hPotential hFiniteEnergy hDissipation 1
  · exact cc13_two_parameters_give_distinct_solutions
      data a ha hGeometry potential hPotential

/-- CC13 Corollary 1.4, kept separate from Theorem 1.2 because it drops the finite-energy requirement and works in every dimension. -/
@[proof_obligation]
theorem cc13_corollary_1_4_hyperbolic_liouville_failure
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) :
    cc13HyperbolicLiouvilleFailureStatement data := by
  sorry

/-- CC13 Theorem 1.6 for the Ricci-free modified equation on pinched surfaces. -/
@[proof_obligation]
theorem cc13_theorem_1_6_pinched_modified_nonuniqueness
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) :
    cc13PinchedModifiedNonuniquenessStatement data := by
  sorry

/-- CC13 Corollary 1.7; unlike Theorem 1.6, the stationary construction does not require `b / 2 < a`. -/
@[proof_obligation]
theorem cc13_corollary_1_7_pinched_liouville_failure
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) :
    cc13PinchedLiouvilleFailureStatement data := by
  sorry

/-- CC13 Corollary 3.4: decay faster than half the volume-growth exponent makes the harmonic gradient square-integrable. -/
@[proof_obligation]
theorem cc13_corollary_3_4_pinched_l2_gradient
    {Initial Solution Potential StationarySolution : Type*}
    (data : CC13PinchedData Initial Solution Potential StationarySolution) :
    ∀ a b δ, 0 < a → a ≤ b → b / 2 < δ → δ < a →
      data.isCompleteSimplyConnectedPinched 2 a b →
      data.isBoundedNonconstantHarmonic a b (data.seedPotential a b) →
      data.hasGradientDecayAtRate a b δ (data.seedPotential a b) →
        data.harmonicGradientHasFiniteEnergy a b (data.seedPotential a b) := by
  sorry

end RiemannianFluids
