import RiemannianFluids.Reproductions.CCP25.Statements

/-! # CCP25 Section 2: Sobolev forms and currents -/

namespace RiemannianFluids

/-! ## Section 2.3: the source definitions

These wrappers deliberately retain the source numbering in the literature module.  The generic
definitions live in `FunctionSpaces.SobolevForms`, where they can be reused by other papers.
-/

/-- CCP25 Definition 2.3, routed to the generic weak-covariant-derivative definition. -/
def ccp25Definition2_3WeakNabla
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test) : Form → Prop :=
  HasWeakCovariantDerivative data

/-- CCP25 Definition 2.4, routed to the generic weak exterior derivative. -/
def ccp25Definition2_4WeakD
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test) : Form → Prop :=
  HasWeakExteriorDerivative data

/-- CCP25 Definition 2.5, routed to the generic weak codifferential. -/
def ccp25Definition2_5WeakDStar
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test) : Form → Prop :=
  HasWeakCodifferential data

/-- CCP25 Definition 2.6, routed to the completion of compactly supported smooth forms in the norm (2.16). -/
def ccp25Definition2_6SobolevH1
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test) : Form → Prop :=
  IsSobolevH1Form data

/-- CCP25 Lemma 2.7: `H1` controls both weak `d` and weak `d*` in `L2`. -/
@[proof_obligation]
theorem ccp25_lemma_2_7_h1_has_weak_d_and_dstar
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form) :
    ∀ form, data.isSobolevH1 form →
      data.hasL2WeakExteriorDerivative form ∧
        data.hasL2WeakCodifferential form := by
  sorry

/-- CCP25 Definition 2.9: currents are linear functionals on compactly supported forms. -/
abbrev CCP25Definition2_9Current
    (Test : Type*) [AddCommGroup Test] [Module ℝ Test] :=
  CCP25Current Test

/-- CCP25 Theorem 2.10: de Rham's current criterion for being homologous to zero. -/
@[proof_obligation]
theorem ccp25_theorem_2_10_current_de_rham
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form) :
    data.hasCurrentDeRhamCriterion := by
  sorry

/-- CCP25 Lemma 2.11: in degree one, annihilating compactly supported co-closed tests is equivalent to being `dP`. -/
@[proof_obligation]
theorem ccp25_lemma_2_11_degree_one_current_criterion
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (hDeRham : data.hasCurrentDeRhamCriterion) :
    data.hasDegreeOneCurrentCriterion := by
  sorry

/-- CCP25 Lemma 2.12: the preceding current criterion in arbitrary form degree. -/
@[proof_obligation]
theorem ccp25_lemma_2_12_degree_k_current_criterion
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (hDeRham : data.hasCurrentDeRhamCriterion) :
    data.hasDegreeKCurrentCriterion := by
  sorry


end RiemannianFluids
