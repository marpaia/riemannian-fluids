import RiemannianFluids.Reproductions.CCF25.Statements

/-! # CCF25 Section 3: geometric boundary conditions -/

namespace RiemannianFluids

/-- Proposition 3.1, equation (3.6): perfect Navier slip is the tangential normal Lie bracket. -/
@[proof_obligation]
theorem ccf25_proposition_3_1_navier_lie_bracket
    {Field VectorCondition FormCondition : Type*}
    (data : CCF25BoundaryData Field VectorCondition FormCondition) :
    ∀ field, data.perfectNavierSlip field = data.tangentialNormalLieBracket field := by
  sorry

/-- Proposition 3.2, equation (3.11): `curl v cross N` is the pulled-back Lie derivative of `v-flat`. -/
@[proof_obligation]
theorem ccf25_proposition_3_2_hodge_lie_derivative
    {Field VectorCondition FormCondition : Type*}
    (data : CCF25BoundaryData Field VectorCondition FormCondition) :
    ∀ field, data.hodgeCurlCondition field = data.pulledBackNormalLieDerivative field := by
  sorry

@[literature_terminal]
theorem ccf25_theorem_1_9_geometric_boundary_conditions
    {Field VectorCondition FormCondition : Type*}
    (data : CCF25BoundaryData Field VectorCondition FormCondition) :
    ccf25GeometricBoundaryStatement data := by
  exact ⟨ccf25_proposition_3_1_navier_lie_bracket data,
    ccf25_proposition_3_2_hodge_lie_derivative data⟩


end RiemannianFluids
