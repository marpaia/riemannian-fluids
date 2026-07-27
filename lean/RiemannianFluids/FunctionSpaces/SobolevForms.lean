import Mathlib.Algebra.Module.Basic
import RiemannianFluids.Tensors.DifferentialForms

/-!
# Weak derivatives and Sobolev spaces of forms

CCP25 Definitions 2.3--2.6 distinguish weak covariant differentiation, weak exterior
differentiation, and weak codifferentiation before defining `H1`.  Keeping those relations
separate is essential: Lemma 2.7 proves that an `H1` form has weak `d` and `d*` in `L2`; it is
not part of the definition of a generic weak derivative.
-/

namespace RiemannianFluids

/-- CCP25 Definition 2.9: a current is a linear functional on compactly supported test forms. -/
structure CCP25Current (Test : Type*) [AddCommGroup Test] [Module ℝ Test] where
  actsOn : Test → ℝ
  map_add : ∀ left right, actsOn (left + right) = actsOn left + actsOn right
  map_smul : ∀ scalar test, actsOn (scalar • test) = scalar * actsOn test

/-- Test-pairing observables used to define weak derivatives of one fixed form degree. -/
structure WeakFormDerivativeData
    (Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*) where
  isLocallyIntegrable : Form → Prop
  isLocallyIntegrableCovariantDerivative : CovariantDerivative → Prop
  isLocallyIntegrableExteriorDerivative : ExteriorDerivative → Prop
  isLocallyIntegrableCodifferential : Codifferential → Prop
  isL2Form : Form → Prop
  isInH1ClosureOfSmoothCompact : Form → Prop
  isL2CovariantDerivative : CovariantDerivative → Prop
  isL2ExteriorDerivative : ExteriorDerivative → Prop
  isL2Codifferential : Codifferential → Prop
  isSmoothCompactTest : Test → Prop
  weakCovariantIdentity : Form → CovariantDerivative → Test → Prop
  weakExteriorIdentity : Form → ExteriorDerivative → Test → Prop
  weakCodifferentialIdentity : Form → Codifferential → Test → Prop

/-- CCP25 Definition 2.3: existence of a weak Levi--Civita derivative. -/
def HasWeakCovariantDerivative
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test)
    (form : Form) : Prop :=
  ∃ derivative, data.isLocallyIntegrableCovariantDerivative derivative ∧
    ∀ test, data.isSmoothCompactTest test →
      data.weakCovariantIdentity form derivative test

/-- CCP25 Definition 2.4: existence of a weak exterior derivative. -/
def HasWeakExteriorDerivative
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test)
    (form : Form) : Prop :=
  ∃ derivative, data.isLocallyIntegrableExteriorDerivative derivative ∧
    ∀ test, data.isSmoothCompactTest test →
      data.weakExteriorIdentity form derivative test

/-- CCP25 Definition 2.5: existence of a weak codifferential. -/
def HasWeakCodifferential
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test)
    (form : Form) : Prop :=
  ∃ derivative, data.isLocallyIntegrableCodifferential derivative ∧
    ∀ test, data.isSmoothCompactTest test →
      data.weakCodifferentialIdentity form derivative test

/-- CCP25 Definition 2.6: `H¹` is the completion of compactly supported smooth forms in the norm (2.16). -/
def IsSobolevH1Form
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test)
    (form : Form) : Prop :=
  data.isInH1ClosureOfSmoothCompact form

/-- The additional predicates needed to state CCP25 Theorem 2.10 for currents of a fixed degree. -/
structure CurrentData (Current Test : Type*) where
  actsOn : Current → Test → ℝ
  isSmoothCompactTest : Test → Prop
  isClosedTest : Test → Prop
  isHomologousToZero : Current → Prop

/-- CCP25 Theorem 2.10: the current-level de Rham criterion used in Lemmas 4.4--4.5. -/
def CurrentDeRhamCriterion
    {Current Test : Type*} (data : CurrentData Current Test) : Prop :=
  ∀ current,
    data.isHomologousToZero current ↔
      ∀ test, data.isSmoothCompactTest test →
        data.isClosedTest test → data.actsOn current test = 0

end RiemannianFluids
