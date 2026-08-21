import Mathlib.Data.Real.Basic
import RiemannianFluids.Tensors.SmoothSections

/-!
# Differential-form calculus contracts

The analytic papers use differential forms in fixed adjacent degrees, not only smooth vector
fields.  This module records the primitive operations needed by CC13, CC15, CCD17, and CCP25
without pretending that mathlib's current differential-form API already supplies their global
noncompact Sobolev theory.

`FormDegreeCalculus` is deliberately data-only.  Nilpotence, adjointness, Weitzenbock
identities, weak extensions, and closed-range results are propositions in later modules.  In
particular, none of the mathematical conclusions to be proved are stored as structure fields.
-/

namespace RiemannianFluids

open scoped ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A raw degree-`k` differential-form section on Mathlib tangent fibers.  No smoothness or
integrability is imposed, so this is the common carrier on which the literature packages place
`L²`, weak-derivative, and Sobolev predicates. -/
abbrev RawDifferentialFormSection (degree : ℕ) :=
  (x : M) → TangentSpace I x [⋀^Fin degree]→L[ℝ] ℝ

/-- A raw covariant derivative of a degree-`k` form: one tangent input followed by the
alternating form inputs. -/
abbrev RawCovariantDifferentialFormSection (degree : ℕ) :=
  (x : M) → TangentSpace I x →L[ℝ]
    (TangentSpace I x [⋀^Fin degree]→L[ℝ] ℝ)

/-- A raw section of the tangent bundle, without regularity or integrability assumptions. -/
abbrev RawTangentFieldSection := (x : M) → TangentSpace I x

/-- Smooth de Rham operators in three adjacent degrees, using Mathlib's actual smooth
alternating-form sections.  Mathlib supplies these section types but not, at the pinned revision,
the manifold exterior derivative or codifferential. -/
structure SmoothAdjacentFormOperators (lowerDegree : ℕ) where
  exteriorFromLower :
    SmoothDifferentialForm (M := M) I lowerDegree ∞ →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I (lowerDegree + 1) ∞
  exterior :
    SmoothDifferentialForm (M := M) I (lowerDegree + 1) ∞ →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I (lowerDegree + 2) ∞
  codifferentialFromUpper :
    SmoothDifferentialForm (M := M) I (lowerDegree + 2) ∞ →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I (lowerDegree + 1) ∞
  codifferential :
    SmoothDifferentialForm (M := M) I (lowerDegree + 1) ∞ →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I lowerDegree ∞
  hodgeLaplacian :
    SmoothDifferentialForm (M := M) I (lowerDegree + 1) ∞ →ₗ[ℝ]
      SmoothDifferentialForm (M := M) I (lowerDegree + 1) ∞

/-- `d ∘ d = 0` in the two adjacent degrees represented by the operator package. -/
def HasSmoothExteriorNilpotence
    (lowerDegree : ℕ)
    (operators : SmoothAdjacentFormOperators (M := M) I lowerDegree) : Prop :=
  ∀ form,
    operators.exterior (operators.exteriorFromLower form) = 0

/-- `d* ∘ d* = 0` in the two adjacent degrees represented by the operator package. -/
def HasSmoothCodifferentialNilpotence
    (lowerDegree : ℕ)
    (operators : SmoothAdjacentFormOperators (M := M) I lowerDegree) : Prop :=
  ∀ form,
    operators.codifferential (operators.codifferentialFromUpper form) = 0

/-- The analysis-positive Hodge Laplacian `d d* + d* d` on the central degree. -/
def HasSmoothHodgeLaplacianFormula
    (lowerDegree : ℕ)
    (operators : SmoothAdjacentFormOperators (M := M) I lowerDegree) : Prop :=
  ∀ form,
    operators.hodgeLaplacian form =
      operators.exteriorFromLower (operators.codifferential form) +
        operators.codifferentialFromUpper (operators.exterior form)

/-- Operations involving one fixed form degree and its two adjacent degrees. -/
structure FormDegreeCalculus
    (Lower Form Upper CovariantDerivative : Type*) where
  /-- Exterior derivative from degree `k - 1` to degree `k`. -/
  exteriorFromLower : Lower → Form
  /-- Exterior derivative from degree `k` to degree `k + 1`. -/
  exterior : Form → Upper
  /-- Codifferential from degree `k + 1` to degree `k`. -/
  codifferentialFromUpper : Upper → Form
  /-- Codifferential from degree `k` to degree `k - 1`. -/
  codifferential : Form → Lower
  /-- Levi--Civita covariant derivative of a degree-`k` form. -/
  covariantDerivative : Form → CovariantDerivative
  /-- Analysis-positive Hodge Laplacian `d d* + d* d`. -/
  hodgeLaplacian : Form → Form
  /-- Analysis-positive Bochner Laplacian `nabla* nabla`. -/
  bochnerLaplacian : Form → Form
  /-- Smoothness at the regularity used by a source theorem. -/
  isSmooth : Form → Prop
  /-- Compact support at the central degree `k`. -/
  hasCompactSupport : Form → Prop
  /-- Compact support at degree `k - 1`, used to generate the exact sector. -/
  hasCompactSupportLower : Lower → Prop
  /-- Compact support at degree `k + 1`, used to generate the coexact sector. -/
  hasCompactSupportUpper : Upper → Prop
  /-- Square integrability. -/
  isL2 : Form → Prop
  /-- First-order Sobolev membership. -/
  isH1 : Form → Prop
  /-- The `L2` pairing at this degree. -/
  l2Pairing : Form → Form → ℝ
  /-- The covariant-derivative pairing used in the `H1` inner product. -/
  derivativePairing : CovariantDerivative → CovariantDerivative → ℝ

/-- A form is closed when its exterior derivative vanishes. -/
def IsClosedForm
    {Lower Form Upper CovariantDerivative : Type*}
    [Zero Upper]
    (calculus : FormDegreeCalculus Lower Form Upper CovariantDerivative)
    (form : Form) : Prop :=
  calculus.exterior form = 0

/-- A form is co-closed when its codifferential vanishes. -/
def IsCoClosedForm
    {Lower Form Upper CovariantDerivative : Type*}
    [Zero Lower]
    (calculus : FormDegreeCalculus Lower Form Upper CovariantDerivative)
    (form : Form) : Prop :=
  calculus.codifferential form = 0

/-- A source-level harmonic form lies in `L2` and is killed by the Hodge Laplacian. -/
def IsL2HarmonicForm
    {Lower Form Upper CovariantDerivative : Type*}
    [Zero Form]
    (calculus : FormDegreeCalculus Lower Form Upper CovariantDerivative)
    (form : Form) : Prop :=
  calculus.isL2 form ∧ calculus.hodgeLaplacian form = 0

/-- The `H1` pairing `(u,v) + (nabla u,nabla v)` used in CCP25 equation (4.3). -/
def FormDegreeCalculus.h1Pairing
    {Lower Form Upper CovariantDerivative : Type*}
    (calculus : FormDegreeCalculus Lower Form Upper CovariantDerivative)
    (first second : Form) : ℝ :=
  calculus.l2Pairing first second +
    calculus.derivativePairing
      (calculus.covariantDerivative first)
      (calculus.covariantDerivative second)

/-- The exact part generated by compactly supported `(k-1)`-forms: the generating lower-degree
form itself is compactly supported, as in the CCP25 construction of the exact sector. -/
def IsCompactlyGeneratedExact
    {Lower Form Upper CovariantDerivative : Type*}
    (calculus : FormDegreeCalculus Lower Form Upper CovariantDerivative)
    (form : Form) : Prop :=
  ∃ lower, calculus.hasCompactSupportLower lower ∧
    calculus.exteriorFromLower lower = form

/-- The coexact part generated by compactly supported `(k+1)`-forms: the generating upper-degree
form itself is compactly supported, as in the CCP25 construction of the coexact sector. -/
def IsCompactlyGeneratedCoexact
    {Lower Form Upper CovariantDerivative : Type*}
    (calculus : FormDegreeCalculus Lower Form Upper CovariantDerivative)
    (form : Form) : Prop :=
  ∃ upper, calculus.hasCompactSupportUpper upper ∧
    calculus.codifferentialFromUpper upper = form

end RiemannianFluids
