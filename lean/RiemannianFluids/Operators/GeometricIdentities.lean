import RiemannianFluids.Operators.Hodge
import RiemannianFluids.Operators.Viscosity
import RiemannianFluids.Geometry.Curvature

/-!
# Ricci action and the CCD17 comparison identities

This file is the destination of the first geometric proof path. Its theorem is short because the analysis has already separated the argument into the
two identities that actually do the mathematical work.

Source: Chan--Czubak--Disconzi, *The formulation of the Navier--Stokes equations on Riemannian manifolds*, arXiv:1608.05114v2, equations (1.1)--(1.3)
and the divergence-free sentence immediately following (1.3).

## The operator ambiguity

On Euclidean space several natural second-order vector operators collapse to the componentwise Laplacian. Curvature separates them. The three
operators relevant here are

    B = ∇*∇,                    the rough or Bochner Laplacian,
    H = d d* + d* d,           the positive Hodge Laplacian,
    D = 2 Def* Def,             the deformation or strain Laplacian.

There is also the zeroth-order curvature action `R = Ric`. The purpose of the calculation is not to declare one notation for all three operators, but
to measure their differences exactly.

## Movement 1: Weitzenböck

Equation (1.1) of CCD17 is the Weitzenböck identity

    B = H - R.

Here `H` means the positive sum `d d* + d* d`. This already translates the paper's later convention `Δ_H = -H` into the repository's analysis-positive
notation.

## Movement 2: expand the symmetric gradient

Equation (1.2) defines `Def`; commuting the two covariant derivatives in the formal-adjoint composition produces Ricci curvature. The resulting
identity used by the paper is

    D = B + d d* - R.

This is named `SymmetricGradientIdentity` below. Notice the extra `d d*`: one copy is already inside `H`, and a second copy appears because the
symmetric gradient averages the two derivative orders.

## Movement 3: substitute, then impose incompressibility

The full calculation is now ordinary operator algebra:

    D = B + d d* - R
      = (H - R) + d d* - R
      = H + d d* - 2R.

This is CCD17 equation (1.3) in the positive convention. For a divergence-free vector field, the previous module proved

    d*(u♭) = -div u = 0,

so `(d d*(u♭))♯ = 0`. Evaluating the full operator identity at `u` leaves

    L_Def u = L_Hodge u - 2 Ric(u).

The Lean proof of the full identity is correspondingly just two rewrites and module normalization. The specialization rewrites the full identity,
evaluates it on `u`, and invokes the concrete codifferential cancellation.

## What Lean has and has not proved

The first-order ingredients leading to `Def u`, divergence, `d*`, and the vanishing of `d d*` are concrete constructions. This module states the
comparison at the level of bundled section operators, where the Hodge Laplacian and the formal-adjoint composition `2 Def*Def` are interface data.
Accordingly:

* `RicciData` can receive the connection-derived raised-index Ricci endomorphism once its smooth
  dependence on the base point is supplied;
* `OneFormHodgeData` receives the missing degree-one de Rham maps;
* `CCD17OperatorData` receives the rough and deformation Laplacians as bundled operators;
* the Weitzenböck and symmetric-gradient identities are explicit hypotheses of the final theorem.

They are hypotheses, not hidden axioms: every use appears in the theorem type. Thus `ccd17_divfree_def_hodge` is an interface proof of the paper's
logical reduction, together with a concrete proof of the divergence-free cancellation.

`Operators.ConstructedLaplacians` proves the geometric core in divergence form: it constructs the pointwise rough Laplacian `-tr_g ∇²u` and the
deformation Laplacian `-2 (div_g Def u)♯` from the connection and proves `⟨L_Def u, w⟩ = ⟨L_rough u, w⟩ - Ric(w, u)` on divergence-free fields,
including the Ricci-commutation and divergence-commutation lemmas. `Operators.ConstructedHodge` constructs the Hodge Laplacian from its two de Rham
halves and proves the Weitzenböck identity for the constructed operators (`weitzenbock_constructedAt`), giving the fully constructed counterpart
`ccd17_divfree_def_hodge_constructed` of the interface theorem below; this module's interface form remains the statement at the level of bundled
section operators, where `OneFormHodgeData` still awaits a standalone degree-two codifferential on arbitrary two-forms.
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

/--
Linear second-order vector operators with an explicit loss of two derivatives. All operators in the comparison share this type, so their equality
expresses both equality of values and agreement on the same regularity domain.
-/
abbrev SecondOrderVectorOperator (regularity : ℕ∞ω) :=
  SmoothVectorField (M := M) I (SecondOrderRegularity regularity) →ₗ[ℝ]
    SmoothVectorField (M := M) I regularity

/--
Forget excess regularity of a vector field. A zeroth-order Ricci action only needs `C^k` input, but it is compared with second-order operators whose
common domain is `C^(k+2)`. This map restricts the stronger regularity proof without changing the underlying field.
-/
noncomputable def restrictVectorFieldRegularity
    {lower higher : ℕ∞ω} (h : lower ≤ higher) :
    SmoothVectorField (M := M) I higher →ₗ[ℝ]
      SmoothVectorField (M := M) I lower where
  toFun field :=
    -- Keep the same pointwise function and weaken only its smoothness proof.
    { toFun := field
      contMDiff_toFun := field.contMDiff.of_le h }
  -- Addition and scalar multiplication are unchanged pointwise.
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem restrictVectorFieldRegularity_apply
    {lower higher : ℕ∞ω} (h : lower ≤ higher)
    (field : SmoothVectorField (M := M) I higher) (x : M) :
    restrictVectorFieldRegularity I h field x = field x :=
  rfl

/--
Pointwise action of a smooth tangent-bundle endomorphism. If `R(x)` represents the metric-raised Ricci tensor, this constructs the field `x ↦
R(x)(u(x))`.
-/
noncomputable def applyVectorEndomorphism
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (endomorphism : SmoothVectorOneForm (M := M) I regularity) :
    SmoothVectorField (M := M) I regularity →ₗ[ℝ]
      SmoothVectorField (M := M) I regularity where
  toFun field :=
    -- Apply the endomorphism and vector section in the same tangent fiber.
    { toFun := fun x => endomorphism x (field x)
      -- Mathlib's smooth bundle-application theorem proves the resulting section remains `C^k`.
      contMDiff_toFun := endomorphism.contMDiff.clm_bundle_apply field.contMDiff }
  map_add' first second := by
    -- Pointwise linearity of the endomorphism gives additivity.
    ext x
    simp
  map_smul' scalar field := by
    -- The same pointwise linearity gives homogeneity.
    ext x
    simp

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem applyVectorEndomorphism_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (endomorphism : SmoothVectorOneForm (M := M) I regularity)
    (field : SmoothVectorField (M := M) I regularity) (x : M) :
    applyVectorEndomorphism I regularity endomorphism field x =
      endomorphism x (field x) :=
  rfl

/--
Ricci curvature as the metric-raised endomorphism field. `RicciData.ofConnection` below populates
this interface from the constructed curvature tensor under an explicit global smoothness proof.

In CCD17, `(Ric(v))ᵢ = Ricᵢⱼ vʲ`. `endomorphism` is the coordinate-free version of the raised-index tensor `Ricᵢ{}ʲ`. Supplying it as data marks the
remaining curvature-regularity boundary honestly.
-/
structure RicciData (regularity : ℕ∞ω) where
  endomorphism : SmoothVectorOneForm (M := M) I regularity

/-- Populate the downstream Ricci interface from the connection-derived contraction.

`regular` is the pointwise hypothesis used to construct `R(X,Y)Z`; `smooth` is separate because
pointwise tensoriality does not by itself establish `C^k` dependence on `x`. -/
noncomputable def RicciData.ofConnection
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (smooth : HasConnectionRicciRegularity I regularity connection regular) :
    RicciData (M := M) I regularity where
  endomorphism := connectionRicciVectorOneForm I regularity connection regular smooth

/-- Populate the downstream Ricci interface directly from contraction-regular connection
curvature, discharging the older standalone smooth-Ricci hypothesis. -/
noncomputable def RicciData.ofRegularConnection
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular) :
    RicciData (M := M) I regularity where
  endomorphism := connectionRicciVectorOneFormOfCurvatureRegularity I regularity connection
    regular hcontraction

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem RicciData.ofRegularConnection_endomorphism_apply
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (hcontraction : HasConnectionRicciContractionRegularity I regularity connection regular)
    (x : M) (vector : TangentSpace I x) :
    (RicciData.ofRegularConnection I regularity connection regular hcontraction).endomorphism
        x vector =
      connectionRicciActionAt I connection x (regular x) vector := by
  exact connectionRicciVectorOneFormOfCurvatureRegularity_apply I regularity connection regular
    hcontraction x vector

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem RicciData.ofConnection_endomorphism_apply
    [IsManifold I 3 M]
    (regularity : ℕ∞ω)
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection x)
    (smooth : HasConnectionRicciRegularity I regularity connection regular)
    (x : M) (vector : TangentSpace I x) :
    (RicciData.ofConnection I regularity connection regular smooth).endomorphism x vector =
      connectionRicciActionAt I connection x (regular x) vector :=
  rfl

/--
Zeroth-order Ricci action, viewed on the common second-order domain. The regularity restriction changes only the proof that the input is smooth
enough; the pointwise theorem below confirms that the value remains `Ric(u)`.
-/
noncomputable def RicciData.action
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (ricci : RicciData (M := M) I regularity) :
    SecondOrderVectorOperator (M := M) I regularity :=
  -- First forget the two excess derivatives, then apply Ricci pointwise.
  (applyVectorEndomorphism I regularity ricci.endomorphism).comp
    (restrictVectorFieldRegularity I
      (le_trans (le_self_add : regularity ≤ regularity + 1) le_self_add))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
@[simp]
theorem RicciData.action_apply
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    (ricci : RicciData (M := M) I regularity)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (x : M) :
    ricci.action I regularity field x = ricci.endomorphism x (field x) :=
  rfl

/--
The geometric data entering CCD17. `deformationLaplacian` denotes the analysis-positive operator `2 Def* Def`.

Only `hodge` is decomposed into first-order de Rham pieces at present. The rough and deformation Laplacians remain fields because their formal-adjoint
constructions have not yet been built. Their intended meanings are fixed here so the comparison hypotheses cannot exchange them accidentally.
-/
structure CCD17OperatorData (regularity : ℕ∞ω) where
  /-- The `d` and `d*` data used to construct `L_Hodge`. -/
  hodge : OneFormHodgeData (M := M) I regularity
  /-- The smooth, raised-index Ricci tensor. -/
  ricci : RicciData (M := M) I regularity
  /-- The analysis-positive rough/Bochner operator `∇*∇`. -/
  roughLaplacian : SecondOrderVectorOperator (M := M) I regularity
  /-- The analysis-positive deformation operator `L_Def = 2 Def* Def`. -/
  deformationLaplacian : SecondOrderVectorOperator (M := M) I regularity

/-- The vector Hodge Laplacian determined by the degree-one de Rham data. -/
noncomputable def CCD17OperatorData.hodgeLaplacian
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) :
    SecondOrderVectorOperator (M := M) I regularity :=
  operators.hodge.hodgeLaplacianVector I regularity connection smooth

/--
Analysis-positive Weitzenböck identity: `∇*∇ = L_Hodge - Ric`.

This is CCD17 equation (1.1), because the repository defines `L_Hodge = d d* + d* d`. It is a predicate rather than a postulate or structure field:
the final theorem must receive an explicit proof of it.
-/
def WeitzenbockIdentity
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  operators.roughLaplacian =
    operators.hodgeLaplacian I regularity connection smooth -
      operators.ricci.action I regularity

/--
Symmetric-gradient identity: `2 Def*Def = ∇*∇ + d d* - Ric`.

CCD17 describes this as the direct computation, using a Ricci commutation identity, which combines with (1.1) to produce equation (1.3). Separating it
from Weitzenbock makes the two geometric obligations visible.
-/
def SymmetricGradientIdentity
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity) : Prop :=
  operators.deformationLaplacian =
    operators.roughLaplacian +
      exactCodifferentialCorrection I regularity connection smooth -
      operators.ricci.action I regularity

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/--
CCD17 equation (1.3), translated to the analysis-positive convention: `L_Def = L_Hodge + d d* - 2 Ric`.

The theorem is purely the algebraic combination of the preceding two identities. This is deliberate: it checks the sign and coefficient bookkeeping
without claiming that the geometric identities have already been proved.
-/
theorem ccd17_positive_full
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators) :
    operators.deformationLaplacian =
      operators.hodgeLaplacian I regularity connection smooth +
        exactCodifferentialCorrection I regularity connection smooth -
        (2 : ℝ) • operators.ricci.action I regularity := by
  -- Substitute `L_Def = rough + d d* - Ric`, then substitute `rough = L_Hodge - Ric`.
  rw [hSymmetric, hWeitzenbock]
  -- Normalize addition, subtraction, and scalar multiplication in the module of linear maps; the two Ricci terms combine to `2 • Ric`.
  module

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/--
CCD17 equation (1.3) on a divergence-free field: `L_Def u = L_Hodge u - 2 Ric(u)`.

This is the source claim `CCD17-divfree-def-hodge`. The theorem remains an interface proof because `hWeitzenbock` and `hSymmetric` are explicit
hypotheses, while the elimination of `d d*` is concrete.
-/
theorem ccd17_divfree_def_hodge
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E
      (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (operators : CCD17OperatorData (M := M) I regularity)
    (hWeitzenbock : WeitzenbockIdentity I regularity connection smooth operators)
    (hSymmetric : SymmetricGradientIdentity I regularity connection smooth operators)
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (hdiv : IsDivergenceFree I connection (regularity + 1) smooth field) :
    operators.deformationLaplacian field =
      operators.hodgeLaplacian I regularity connection smooth field -
        (2 : ℝ) • operators.ricci.action I regularity field := by
  -- Rewrite the deformation operator by the full positive-convention form of CCD17 equation (1.3).
  rw [ccd17_positive_full I regularity connection smooth operators hWeitzenbock hSymmetric]
  -- Evaluate sums and differences of linear maps at `field`, then use the concrete theorem that divergence-freeness kills `(d d*(u♭))♯`.
  rw [LinearMap.sub_apply, LinearMap.add_apply,
    exactCodifferentialCorrection_eq_zero_of_divergenceFree
      I regularity connection smooth field hdiv]
  -- Remove the resulting zero summand. What remains is exactly `L_Hodge u - 2 Ric(u)`.
  simp

end RiemannianFluids
