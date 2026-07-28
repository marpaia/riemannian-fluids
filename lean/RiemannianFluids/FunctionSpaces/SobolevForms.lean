import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import RiemannianFluids.Tensors.SmoothSections
import RiemannianFluids.Tensors.DifferentialForms

/-!
# Weak derivatives and Sobolev spaces of forms

CCP25 Definitions 2.3--2.6 distinguish weak covariant differentiation, weak exterior
differentiation, and weak codifferentiation before defining `H1`.  Keeping those relations
separate is essential: Lemma 2.7 proves that an `H1` form has weak `d` and `d*` in `L2`; it is
not part of the definition of a generic weak derivative.
-/

namespace RiemannianFluids

open Bundle MeasureTheory
open scoped Bundle ContDiff Manifold ENNReal

/-- A current is a linear functional on compactly supported test forms.  The concept is shared
mathematics; the compatibility abbreviation below preserves the paper-local name. -/
structure Current (Test : Type*) [AddCommGroup Test] [Module ℝ Test] where
  actsOn : Test → ℝ
  map_add : ∀ left right, actsOn (left + right) = actsOn left + actsOn right
  map_smul : ∀ scalar test, actsOn (scalar • test) = scalar * actsOn test

/-- Compatibility name used by the CCP25 source statements. -/
abbrev CCP25Current := Current

/-- The missing measurability layer for sections of a varying normed bundle.  Mathlib's `MemLp`
handles ordinary functions into one normed space; a future vector-bundle integration API can
replace this explicit section predicate without changing the source statements below. -/
structure MeasurableSectionData
    (Base : Type*) (Fiber : Base → Type*) where
  isStronglyMeasurableSection : ((x : Base) → Fiber x) → Prop

/-- `L^p` membership of a varying-fiber section: explicit section measurability plus Mathlib's
`MemLp` condition for its scalar norm. -/
def SectionMemLp
    {Base : Type*} [MeasurableSpace Base]
    {Fiber : Base → Type*}
    (measurability : MeasurableSectionData Base Fiber)
    (fiberNorm : ∀ x, Fiber x → ℝ)
    (μ : Measure Base) (p : ℝ≥0∞) (fieldSection : (x : Base) → Fiber x) : Prop :=
  measurability.isStronglyMeasurableSection fieldSection ∧
    MemLp (fun x => fiberNorm x (fieldSection x)) p μ

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Raw (not necessarily smooth) Riemannian vector fields used in Sobolev completions. -/
abbrev RiemannianL2VectorField := RawTangentFieldSection (M := M) I

/-- Raw tangent-valued one-forms, the fiber type of a weak covariant derivative. -/
abbrev RiemannianL2VectorOneForm :=
  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x

/-- Concrete `L²` membership for tangent fields, resting on Mathlib's `MemLp`. -/
def IsL2RiemannianVectorField
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (measurability : MeasurableSectionData M (fun x => TangentSpace I x))
    (μ : Measure M) (field : RiemannianL2VectorField (I := I) (M := M)) : Prop :=
  SectionMemLp measurability (fun _ value => ‖value‖) μ 2 field

/-- Concrete `L²` membership for tangent-valued one-forms. -/
def IsL2RiemannianVectorOneForm
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (measurability : MeasurableSectionData M
      (fun x => TangentSpace I x →L[ℝ] TangentSpace I x))
    (μ : Measure M) (tensor : RiemannianL2VectorOneForm (I := I) (M := M)) : Prop :=
  SectionMemLp measurability (fun _ value => ‖value‖) μ 2 tensor

/-- Test-pairing data for the weak Levi--Civita derivative of an actual tangent field.  The
formal adjoint on smooth compactly supported tests remains explicit because it depends on the
chosen connection and Riemannian volume theory. -/
structure WeakRiemannianVectorDerivativeData
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] where
  measure : Measure M
  vectorMeasurability : MeasurableSectionData M (fun x => TangentSpace I x)
  derivativeMeasurability : MeasurableSectionData M
    (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)
  isSmoothCompactTest : SmoothVectorOneForm (M := M) I ∞ → Prop
  derivativePairing : ∀ x : M,
    (TangentSpace I x →L[ℝ] TangentSpace I x) →
      (TangentSpace I x →L[ℝ] TangentSpace I x) → ℝ
  formalAdjointOnTests : SmoothVectorOneForm (M := M) I ∞ →
    RiemannianL2VectorField (I := I) (M := M)

/-- The integral identity defining one weak covariant derivative. -/
def IsWeakRiemannianCovariantDerivative
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (data : WeakRiemannianVectorDerivativeData (I := I) (M := M))
    (field : RiemannianL2VectorField (I := I) (M := M))
    (derivative : RiemannianL2VectorOneForm (I := I) (M := M)) : Prop :=
  IsL2RiemannianVectorOneForm data.derivativeMeasurability data.measure derivative ∧
    ∀ test, data.isSmoothCompactTest test →
      (∫ x, data.derivativePairing x (derivative x) (test x) ∂data.measure) =
        ∫ x, inner ℝ (field x) (data.formalAdjointOnTests test x) ∂data.measure

/-- The first-order Riemannian Sobolev class: an `L²` tangent field possessing an `L²` weak
covariant derivative. -/
def IsRiemannianH1VectorField
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (data : WeakRiemannianVectorDerivativeData (I := I) (M := M))
    (field : RiemannianL2VectorField (I := I) (M := M)) : Prop :=
  IsL2RiemannianVectorField data.vectorMeasurability data.measure field ∧
    ∃ derivative, IsWeakRiemannianCovariantDerivative data field derivative

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

/-- A weak exterior derivative represented by an `L²` form. -/
def HasL2WeakExteriorDerivative
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test)
    (form : Form) : Prop :=
  ∃ derivative,
    data.isL2ExteriorDerivative derivative ∧
      data.isLocallyIntegrableExteriorDerivative derivative ∧
      ∀ test, data.isSmoothCompactTest test →
        data.weakExteriorIdentity form derivative test

/-- A weak codifferential represented by an `L²` form. -/
def HasL2WeakCodifferential
    {Form CovariantDerivative ExteriorDerivative Codifferential Test : Type*}
    (data : WeakFormDerivativeData
      Form CovariantDerivative ExteriorDerivative Codifferential Test)
    (form : Form) : Prop :=
  ∃ derivative,
    data.isL2Codifferential derivative ∧
      data.isLocallyIntegrableCodifferential derivative ∧
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
