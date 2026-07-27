import Mathlib.Data.Real.Basic
import RiemannianFluids.FunctionSpaces.HodgeDecomposition
import RiemannianFluids.FunctionSpaces.SobolevForms
import RiemannianFluids.ProofStatus

/-!
# CCP25 proof route

Source: Chan--Czubak--Pinilla Suarez, *Hodge decomposition of the Sobolev space
H1 on a space form of nonpositive curvature*, arXiv:1812.11764v1, Theorem 1.3.

For every form degree on `H^N(-a^2)`, `a >= 0`, the `H^1` space is the orthogonal direct
sum of the `H^1` closures of compactly supported exact and coexact forms and the space of
`L^2` harmonic forms.  The paper's proof uses the `H^1` inner product, the constant-curvature
Bochner--Weitzenbock formula, closedness of the first two summands, and identification of
their orthogonal complement with the harmonic forms.
-/

namespace RiemannianFluids

/-- Smooth and `L²` summands in the classical Hodge decompositions quoted as Theorems 1.1--1.2. -/
structure CCP25ClassicalHodgeData (Form : Type*) where
  isCompactWithoutBoundary : Prop
  isCompleteWithoutBoundary : Prop
  isSmoothKForm : Form → Prop
  isL2KForm : Form → Prop
  isSmoothExact : Form → Prop
  isSmoothCoexact : Form → Prop
  isSmoothHarmonic : Form → Prop
  isL2ExactClosure : Form → Prop
  isL2CoexactClosure : Form → Prop
  isL2Harmonic : Form → Prop
  smoothOrthogonal : Form → Form → Prop
  l2Orthogonal : Form → Form → Prop

/-- Existence, pairwise orthogonality, and uniqueness for a three-summand decomposition. -/
def HasUniqueOrthogonalHodgeDecomposition
    {Form : Type*} [AddCommGroup Form]
    (isWhole isExact isCoexact isHarmonic : Form → Prop)
    (orthogonal : Form → Form → Prop) : Prop :=
  ∀ form, isWhole form →
    ∃ pieces : HodgePieces Form,
      isExact pieces.exactPart ∧
        isCoexact pieces.coexactPart ∧
        isHarmonic pieces.harmonicPart ∧
        form = pieces.exactPart + pieces.coexactPart + pieces.harmonicPart ∧
        orthogonal pieces.exactPart pieces.coexactPart ∧
        orthogonal pieces.exactPart pieces.harmonicPart ∧
        orthogonal pieces.coexactPart pieces.harmonicPart ∧
        ∀ other : HodgePieces Form,
          isExact other.exactPart →
          isCoexact other.coexactPart →
          isHarmonic other.harmonicPart →
          form = other.exactPart + other.coexactPart + other.harmonicPart →
            other = pieces

/-- CCP25 Theorem 1.1: the classical smooth Hodge decomposition on a compact manifold without boundary. -/
def ccp25CompactHodgeDecompositionStatement
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25ClassicalHodgeData Form) : Prop :=
  data.isCompactWithoutBoundary →
    HasUniqueOrthogonalHodgeDecomposition
      data.isSmoothKForm data.isSmoothExact data.isSmoothCoexact
      data.isSmoothHarmonic data.smoothOrthogonal

/-- CCP25 Theorem 1.2: the Hodge--Kodaira `L²` decomposition on a complete manifold without boundary. -/
def ccp25L2HodgeKodairaDecompositionStatement
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25ClassicalHodgeData Form) : Prop :=
  data.isCompleteWithoutBoundary →
    HasUniqueOrthogonalHodgeDecomposition
      data.isL2KForm data.isL2ExactClosure data.isL2CoexactClosure
      data.isL2Harmonic data.l2Orthogonal

/-- CCP25 Theorem 1.1 is a classical imported result, retained as the first theorem node in the paper. -/
@[proof_obligation]
theorem ccp25_theorem_1_1_compact_hodge_decomposition
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25ClassicalHodgeData Form) :
    ccp25CompactHodgeDecompositionStatement data := by
  sorry

/-- CCP25 Theorem 1.2 is Kodaira's imported complete-manifold `L²` decomposition. -/
@[proof_obligation]
theorem ccp25_theorem_1_2_l2_hodge_kodaira
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25ClassicalHodgeData Form) :
    ccp25L2HodgeKodairaDecompositionStatement data := by
  sorry

/-- Geometric parameters and `H^1` summands for one form degree. -/
structure CCP25H1Data (Form : Type*) where
  dimension : ℕ
  degree : ℕ
  curvatureScale : ℝ
  isHyperbolicSpaceForm : Prop
  hodge : H1HodgeData Form
  /-- Definitions 2.3--2.6, specialized to the fixed degree represented by `Form`. -/
  isSobolevH1 : Form → Prop
  hasL2WeakExteriorDerivative : Form → Prop
  hasL2WeakCodifferential : Form → Prop
  isWeaklyClosed : Form → Prop
  isWeaklyCoClosed : Form → Prop
  /-- Formula (2.6) and its integrated corollary for the constant-curvature rough Laplacian. -/
  hasConstantCurvatureWeitzenbockIdentity : Form → Prop
  hasIntegratedWeitzenbockIdentity : Form → Prop
  hasBochnerNormIdentity2_11 : Form → Prop
  /-- Theorem 2.10 and its degree-one/degree-`k` reformulations, Lemmas 2.11--2.12. -/
  hasCurrentDeRhamCriterion : Prop
  hasDegreeOneCurrentCriterion : Prop
  hasDegreeKCurrentCriterion : Prop
  /-- The current primitives in equations (4.26)--(4.27). -/
  hasCurrentPrimitive : Form → Prop
  hasCurrentCoprimitive : Form → Prop

/-- A unique two-summand decomposition of a distinguished subspace. -/
def HasUniqueBinaryDecomposition
    {Form : Type*} [AddCommGroup Form]
    (isWhole isLeft isRight : Form → Prop) : Prop :=
  ∀ form, isWhole form →
    ∃ left right,
      isLeft left ∧ isRight right ∧ form = left + right ∧
        ∀ otherLeft otherRight,
          isLeft otherLeft → isRight otherRight →
            form = otherLeft + otherRight →
              otherLeft = left ∧ otherRight = right

/-- The three spaces occurring in CCP25 Theorem 1.4 on one-forms over `H²(-a²)`. -/
structure CCP25HelmholtzData (Form : Type*) where
  h1 : CCP25H1Data Form
  isWeaklyDivergenceFree : Form → Prop
  isCompactSolenoidalH1Closure : Form → Prop

/-- Theorem 1.4: the divergence-free `H¹` space is both `V ⊕ H¹` and the coexact closure `⊕ H¹`. -/
def ccp25H1HelmholtzDecompositionStatement
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25HelmholtzData Form) : Prop :=
  data.h1.dimension = 2 →
    data.h1.degree = 1 →
    0 ≤ data.h1.curvatureScale →
    data.h1.isHyperbolicSpaceForm →
      HasUniqueBinaryDecomposition
        data.isWeaklyDivergenceFree
        data.isCompactSolenoidalH1Closure
        data.h1.hodge.isL2Harmonic ∧
      (∀ form,
        data.isCompactSolenoidalH1Closure form ↔
          data.h1.hodge.isCoexactClosure form) ∧
      HasUniqueBinaryDecomposition
        data.isWeaklyDivergenceFree
        data.h1.hodge.isCoexactClosure
        data.h1.hodge.isL2Harmonic

/-- Exact statement contract for CCP25 Theorem 1.3. -/
def ccp25H1NoncompactDecompositionStatement
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form) : Prop :=
  2 ≤ data.dimension →
    0 ≤ data.curvatureScale →
    data.degree ≤ data.dimension →
      data.isHyperbolicSpaceForm →
        HasH1HodgeDecomposition data.hodge ∧
          (∀ exact, data.hodge.isExactClosure exact → data.hasCurrentPrimitive exact) ∧
          ∀ coexact, data.hodge.isCoexactClosure coexact → data.hasCurrentCoprimitive coexact

/-- CCP25 Lemma 2.1: the pointwise Weitzenbock formula on `k`-forms over `H^N(-a^2)`. -/
@[proof_obligation]
theorem ccp25_lemma_2_1_constant_curvature_weizenbock
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ form, data.hasConstantCurvatureWeitzenbockIdentity form := by
  sorry

/-- CCP25 Corollary 2.2: the integrated `d`/`d*`/covariant-derivative identity. -/
@[proof_obligation]
theorem ccp25_corollary_2_2_integrated_weizenbock
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm) :
    ∀ form,
      data.hasConstantCurvatureWeitzenbockIdentity form →
        data.hasIntegratedWeitzenbockIdentity form := by
  sorry

/-- CCP25 equation (2.11): the scalar Bochner identity for the pointwise norm of a `k`-form. -/
@[proof_obligation]
theorem ccp25_equation_2_11_bochner_norm
    {Form : Type*} [AddCommGroup Form]
    (data : CCP25H1Data Form)
    (ha : 0 ≤ data.curvatureScale)
    (hDegree : data.degree ≤ data.dimension)
    (hGeometry : data.isHyperbolicSpaceForm)
    (hWeitzenbock : ∀ form, data.hasConstantCurvatureWeitzenbockIdentity form)
    (hIntegrated : ∀ form,
      data.hasConstantCurvatureWeitzenbockIdentity form →
        data.hasIntegratedWeitzenbockIdentity form) :
    ∀ form, data.hasBochnerNormIdentity2_11 form := by
  sorry


end RiemannianFluids
