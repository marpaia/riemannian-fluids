import RiemannianFluids.Tensors.SecondDerivative
import RiemannianFluids.Tensors.VectorCalculus

/-!
# Constructed rough and deformation Laplacians

CCD17 (Chan--Czubak--Disconzi, arXiv:1608.05114v2, equations (1.1)--(1.3)) compares three
second-order operators on vector fields. Two of them are constructed here directly from a
Levi-Civita connection, using the divergence formulation that avoids formal adjoints and
integration entirely:

    L_rough u = ∇*∇ u = -tr_g ∇²u,
    L_Def u   = 2 Def* Def u = -2 (div_g Def u)♯.

Both are algebraic contractions of the single geometric object `∇²u`, the pointwise second
covariant derivative of `Tensors.SecondDerivative`. The rough Laplacian contracts the two input
slots against the metric. The divergence of the deformation tensor is computed from the pointwise
expansion

    (∇_X Def u)(Y,Z) = ½ (⟨∇²u(X,Y),Z⟩ + ⟨∇²u(X,Z),Y⟩),

proved below from metric compatibility, so `div Def u` decomposes into the input trace of `∇²u`
and the mixed input/output trace `Σᵢ ⟨∇²u(eᵢ,Y),eᵢ⟩`. Ricci commutation converts that mixed trace
into the trace of `∇²u(Y,·)` plus the Ricci contraction `tr(X ↦ R(X,Y)u)`, which is literally
`connectionRicciFormAt`. The trace of `∇²u(Y,·)` is the derivative of `div u` in the direction
`Y`; `DivergenceCommutationAt` names that scalar frame identity precisely. The resulting proved
comparison, on any field with vanishing divergence, is

    ⟨L_Def u, Y⟩ = ⟨L_rough u, Y⟩ - Ric(Y, u).

## The Hodge framing

CCD17 states the divergence-free comparison as `L_Def = L_Hodge - 2 Ric` and derives it from the
Weitzenböck identity `L_rough = L_Hodge - Ric`. This module stays on the divergence side of that
reduction; `Operators.ConstructedHodge` constructs the Hodge Laplacian from the connection — the
exterior derivative on lowered fields as the antisymmetrized lowered covariant derivative, with
its connection-free bracket formula proved — and proves the Weitzenböck identity for the
constructed operators, so the full CCD17 chain holds with every operator constructed. The Ricci
term appears through the repository's Ricci convention `Ric(Y,Z) = tr(X ↦ R(X,Y)Z)` tested as
`Ric(Y(x), u(x))`; the symmetric rearrangement `Ric(u(x), Y(x))` would additionally require the
first Bianchi identity, which is not used here.

All statements are pointwise with explicit `MDiffAt`/`CMDiffAt` hypotheses; the bundled
divergence-free corollary consumes `IsDivergenceFree` through its pointwise characterization.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

/-! ## Metric contractions of a vector-valued bilinear map

A vector-valued bilinear map `B : V →L V →L V` on an inner-product space admits two contractions
relevant to the operator comparison: the input trace `Σᵢ B(eᵢ,eᵢ)`, contracting the two inputs
against the metric, and the mixed trace `Σᵢ ⟨B(eᵢ,w),eᵢ⟩`, pairing the first input with the
output. Both are defined by algebraic traces, hence basis independent; the orthonormal-basis
formulas are theorems. -/

section BilinearContraction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Lower the vector output of a bilinear map against a fixed vector: `(v,z) ↦ ⟨B v z, w⟩`. -/
noncomputable def bilinearFormAgainst (B : V →L[ℝ] V →L[ℝ] V) (w : V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ V V ℝ (innerSL ℝ w)).comp B

omit [FiniteDimensional ℝ V] in
@[simp]
theorem bilinearFormAgainst_apply (B : V →L[ℝ] V →L[ℝ] V) (w v z : V) :
    bilinearFormAgainst B w v z = inner ℝ (B v z) w := by
  simp [bilinearFormAgainst, real_inner_comm]

/-- The endomorphism representing the lowered bilinear map through the metric:
`⟨(B♯_w) v, z⟩ = ⟨B v z, w⟩`. -/
noncomputable def bilinearRaisedAgainst (B : V →L[ℝ] V →L[ℝ] V) (w : V) : V →L[ℝ] V :=
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  InnerProductSpace.continuousLinearMapOfBilin (bilinearFormAgainst B w)

@[simp]
theorem bilinearRaisedAgainst_inner (B : V →L[ℝ] V →L[ℝ] V) (w v z : V) :
    inner ℝ (bilinearRaisedAgainst B w v) z = inner ℝ (B v z) w := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  rw [bilinearRaisedAgainst, InnerProductSpace.continuousLinearMapOfBilin_apply,
    bilinearFormAgainst_apply]

/-- The metric input trace of `B` tested against `w`: intrinsically the trace of the raised
lowered form, equal to `Σᵢ ⟨B(eᵢ,eᵢ),w⟩` in every orthonormal basis. -/
noncomputable def bilinearMetricTraceAgainst (B : V →L[ℝ] V →L[ℝ] V) (w : V) : ℝ :=
  LinearMap.trace ℝ V (bilinearRaisedAgainst B w).toLinearMap

/-- Every orthonormal basis computes the metric input trace as the diagonal sum. -/
theorem bilinearMetricTraceAgainst_eq_sum {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℝ V) (B : V →L[ℝ] V →L[ℝ] V) (w : V) :
    bilinearMetricTraceAgainst B w = ∑ i, inner ℝ (B (basis i) (basis i)) w := by
  rw [bilinearMetricTraceAgainst, LinearMap.trace_eq_sum_inner _ basis]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm]
  exact bilinearRaisedAgainst_inner B w (basis i) (basis i)

/-- The metric input trace of a vector-valued bilinear map, as a vector: the Riesz representative
of `w ↦ bilinearMetricTraceAgainst B w`. -/
noncomputable def bilinearMetricTrace (B : V →L[ℝ] V →L[ℝ] V) : V :=
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  (InnerProductSpace.toDual ℝ V).symm
    (LinearMap.toContinuousLinearMap
      { toFun := fun w ↦ bilinearMetricTraceAgainst B w
        map_add' := fun w w' ↦ by
          have hraised : bilinearRaisedAgainst B (w + w') =
              bilinearRaisedAgainst B w + bilinearRaisedAgainst B w' := by
            ext v
            apply ext_inner_right ℝ
            intro z
            simp only [bilinearRaisedAgainst_inner, add_apply,
              inner_add_left, inner_add_right]
          simp [bilinearMetricTraceAgainst, hraised]
        map_smul' := fun c w ↦ by
          have hraised : bilinearRaisedAgainst B (c • w) =
              c • bilinearRaisedAgainst B w := by
            ext v
            apply ext_inner_right ℝ
            intro z
            simp only [bilinearRaisedAgainst_inner, smul_apply,
              real_inner_smul_left, real_inner_smul_right]
          simp [bilinearMetricTraceAgainst, hraised] })

/-- Testing the intrinsic input-trace vector against `w` recovers the scalar contraction. -/
@[simp]
theorem inner_bilinearMetricTrace (B : V →L[ℝ] V →L[ℝ] V) (w : V) :
    inner ℝ (bilinearMetricTrace B) w = bilinearMetricTraceAgainst B w := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  simp [bilinearMetricTrace, InnerProductSpace.toDual_symm_apply]

/-- The mixed input/output trace of `B` with second slot frozen at `w`:
the trace of `v ↦ B v w`. -/
noncomputable def bilinearMixedTraceAgainst (B : V →L[ℝ] V →L[ℝ] V) (w : V) : ℝ :=
  LinearMap.trace ℝ V (B.flip w).toLinearMap

/-- The Riesz representative of a linear functional on a finite-dimensional real inner-product
space.  Keeping this construction named makes the passage from independently constructed tested
covectors to actual operator outputs explicit. -/
noncomputable def rieszRepresentative (functional : V →ₗ[ℝ] ℝ) : V :=
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  (InnerProductSpace.toDual ℝ V).symm
    (LinearMap.toContinuousLinearMap functional)

/-- Testing a Riesz representative recovers the original functional. -/
@[simp]
theorem inner_rieszRepresentative (functional : V →ₗ[ℝ] ℝ) (w : V) :
    inner ℝ (rieszRepresentative functional) w = functional w := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  simp [rieszRepresentative, InnerProductSpace.toDual_symm_apply]

/-- The mixed trace, packaged as a linear functional of its frozen second input. -/
noncomputable def bilinearMixedTraceFunctional (B : V →L[ℝ] V →L[ℝ] V) : V →ₗ[ℝ] ℝ :=
  (LinearMap.trace ℝ V).comp
    ((LinearMap.toContinuousLinearMap :
      (V →ₗ[ℝ] V) ≃ₗ[ℝ] (V →L[ℝ] V)).symm.toLinearMap.comp B.flip.toLinearMap)

@[simp]
theorem bilinearMixedTraceFunctional_apply (B : V →L[ℝ] V →L[ℝ] V) (w : V) :
    bilinearMixedTraceFunctional B w = bilinearMixedTraceAgainst B w :=
  rfl

/-- The mixed input/output trace of `B`, represented intrinsically as a vector. -/
noncomputable def bilinearMixedTrace (B : V →L[ℝ] V →L[ℝ] V) : V :=
  rieszRepresentative (bilinearMixedTraceFunctional B)

/-- Testing the intrinsic mixed-trace vector recovers the scalar mixed contraction. -/
@[simp]
theorem inner_bilinearMixedTrace (B : V →L[ℝ] V →L[ℝ] V) (w : V) :
    inner ℝ (bilinearMixedTrace B) w = bilinearMixedTraceAgainst B w := by
  simp [bilinearMixedTrace]

omit [FiniteDimensional ℝ V] in
/-- Every orthonormal basis computes the mixed trace as the paired diagonal sum. -/
theorem bilinearMixedTraceAgainst_eq_sum {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℝ V) (B : V →L[ℝ] V →L[ℝ] V) (w : V) :
    bilinearMixedTraceAgainst B w = ∑ i, inner ℝ (B (basis i) w) (basis i) := by
  rw [bilinearMixedTraceAgainst, LinearMap.trace_eq_sum_inner _ basis]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

end BilinearContraction

/-! ### Traces through a metric-dual pair

A family of vectors `dual` pairing to the identity against a basis computes coordinates and
traces through the inner product. These are the linear-algebra facts behind differentiating a
frame representation of the divergence. -/

section DualPair

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem repr_eq_inner_dualPair (basis : Module.Basis ι ℝ V) (dual : ι → V)
    (hdual : ∀ i j, inner ℝ (dual i) (basis j) = if i = j then (1 : ℝ) else 0)
    (z : V) (i : ι) :
    basis.repr z i = inner ℝ (dual i) z := by
  conv_rhs => rw [← basis.sum_repr z]
  rw [inner_sum]
  simp [real_inner_smul_right, hdual, Finset.sum_ite_eq]

private theorem trace_eq_sum_inner_dualPair (basis : Module.Basis ι ℝ V) (dual : ι → V)
    (hdual : ∀ i j, inner ℝ (dual i) (basis j) = if i = j then (1 : ℝ) else 0)
    (S : V →L[ℝ] V) :
    LinearMap.trace ℝ V S.toLinearMap = ∑ i, inner ℝ (dual i) (S (basis i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ basis, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    repr_eq_inner_dualPair basis dual hdual]
  rfl

private theorem eq_sum_inner_dualPair_smul (basis : Module.Basis ι ℝ V) (dual : ι → V)
    (hdual : ∀ i j, inner ℝ (dual i) (basis j) = if i = j then (1 : ℝ) else 0)
    (z : V) :
    z = ∑ i, inner ℝ (dual i) z • basis i := by
  conv_lhs => rw [← basis.sum_repr z]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [repr_eq_inner_dualPair basis dual hdual]

end DualPair

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

noncomputable section

/-- The Riesz representative of the Ricci functional with its first slot left open:
`w ↦ Ric(w,u)`.  This is the curvature vector that appears in the constructed comparison before
Ricci symmetry is invoked. -/
def connectionRicciTransposeActionAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : TangentSpace I x) : TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rieszRepresentative ((connectionRicciFormAt I connection x regular).flip field).toLinearMap

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The transposed Ricci action represents exactly the pairing `Ric(w,u)`. -/
@[simp]
theorem inner_connectionRicciTransposeActionAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field w : TangentSpace I x) :
    inner ℝ (connectionRicciTransposeActionAt I connection x regular field) w =
      connectionRicciFormAt I connection x regular w field := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [connectionRicciTransposeActionAt, inner_rieszRepresentative]
  rfl

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- When the connection Ricci form is symmetric, the pre-Bianchi transposed Ricci action used by
the constructed Weitzenbock formula agrees with the usual raised Ricci action. -/
theorem connectionRicciTransposeActionAt_eq_connectionRicciActionAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (symmetric : ConnectionRicciSymmetricAt I connection x regular)
    (field : TangentSpace I x) :
    connectionRicciTransposeActionAt I connection x regular field =
      connectionRicciActionAt I connection x regular field := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_connectionRicciTransposeActionAt,
    connectionRicciActionAt_inner, symmetric]

omit [CompleteSpace E] [IsManifold I 2 M]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Every orthonormal frame of the tangent fiber computes the intrinsic endomorphism trace. -/
theorem tangentTrace_eq_sum_inner {x : M} {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℝ (TangentSpace I x))
    (S : TangentSpace I x →L[ℝ] TangentSpace I x) :
    tangentTrace I x S = ∑ i, inner ℝ (basis i) (S (basis i)) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  exact LinearMap.trace_eq_sum_inner _ basis

/-! ### Scalar-derivative bookkeeping

The frame proof of divergence commutation differentiates finite sums of inner products of
sections and functions that are constant near the base point. The following helpers record the
corresponding `mvfderiv` calculus. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Vector-valued manifold derivatives depend only on the germ of the function. -/
private theorem mvfderiv_congr_of_eventuallyEq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : M → F} {x : M} (h : f =ᶠ[𝓝 x] g) :
    d% f x = d% g x := by
  ext v
  show mfderiv I 𝓘(ℝ, F) f x v = mfderiv I 𝓘(ℝ, F) g x v
  rw [h.mfderiv_eq]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Differentiability and the derivative of a finite sum of scalar functions. -/
private theorem mdifferentiableAt_and_mvfderiv_fun_sum {ι : Type*}
    {h : ι → M → ℝ} {x : M} (s : Finset ι) :
    (∀ i ∈ s, MDiffAt (h i) x) →
      MDiffAt (fun y ↦ ∑ i ∈ s, h i y) x ∧
        d% (fun y ↦ ∑ i ∈ s, h i y) x = ∑ i ∈ s, d% (h i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      constructor
      · simpa using (mdifferentiableAt_const : MDiffAt (fun _ : M ↦ (0 : ℝ)) x)
      · simpa using (mvfderiv_const (I := I) (M := M) (0 : ℝ) (x := x))
  | @insert a s ha ih =>
      intro hd
      simp only [Finset.mem_insert, forall_eq_or_imp] at hd
      obtain ⟨ihd, ihe⟩ := ih hd.2
      have hrw : (fun y ↦ ∑ i ∈ insert a s, h i y) = fun y ↦ h a y + ∑ i ∈ s, h i y := by
        funext y
        rw [Finset.sum_insert ha]
      constructor
      · rw [hrw]
        exact hd.1.add ihd
      · rw [hrw, mvfderiv_fun_add hd.1 ihd, ihe, Finset.sum_insert ha]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The determinant of an entrywise-differentiable matrix field is differentiable, by the
Leibniz expansion into signed products of entries. -/
private theorem contMDiffAt_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : M → Matrix ι ι ℝ} {x : M} (hA : ∀ i j, CMDiffAt 1 (fun y ↦ A y i j) x) :
    CMDiffAt 1 (fun y ↦ (A y).det) x := by
  have hrw : (fun y ↦ (A y).det) =
      fun y ↦ ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A y (σ i) i := by
    funext y
    rw [Matrix.det_apply']
  rw [hrw]
  exact ContMDiffAt.sum fun σ _ ↦
    contMDiffAt_const.mul (ContMDiffAt.prod fun i _ ↦ hA (σ i) i)

/-! ## The constructed operators -/

/-- The pointwise rough (Bochner) Laplacian in the analysis-positive convention:

`L_rough u (x) = -tr_g ∇²u (x)`.

The trace is the intrinsic metric input contraction of the pointwise second-derivative bilinear
map, so the definition involves no choice of basis. -/
def roughLaplacianAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  Neg.neg (bilinearMetricTrace (secondCovariantDerivativeAt I connection x regular field hfield))

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The rough Laplacian tested against a vector is the negative diagonal sum of `∇²u` in any
orthonormal frame. -/
theorem inner_roughLaplacianAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ (TangentSpace I x))
    (w : TangentSpace I x) :
    inner ℝ (roughLaplacianAt I connection x regular field hfield) w =
      -∑ i, inner ℝ
        (secondCovariantDerivativeAt I connection x regular field hfield
          (basis i) (basis i)) w := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [roughLaplacianAt, inner_neg_left, inner_bilinearMetricTrace,
    bilinearMetricTraceAgainst_eq_sum basis]

omit [CompleteSpace E] [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The vector-valued rough Laplacian itself is the negative diagonal Hessian sum in every
orthonormal frame.  This is the basis-expansion bridge used by submanifold trace formulas, whose
left-hand sides are naturally written in an adapted orthonormal frame. -/
theorem roughLaplacianAt_eq_neg_sum
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    roughLaplacianAt I connection x regular field hfield =
      -∑ i, secondCovariantDerivativeAt I connection x regular field hfield
        (basis i) (basis i) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_roughLaplacianAt I connection x regular field hfield basis w,
    inner_neg_left, sum_inner]

/-- The divergence of the deformation tensor tested against `w`:

`(div_g Def u)(w) = ½ (⟨tr_g ∇²u, w⟩ + Σᵢ ⟨∇²u(eᵢ,w),eᵢ⟩)`.

Both summands are intrinsic traces of the pointwise second derivative; the theorem
`sum_deformationCovariantDerivativeAt_extend` identifies this expression with the frame sum
`Σᵢ (∇_{eᵢ} Def u)(eᵢ, w)` of covariant derivatives of the actual deformation tensor. -/
def deformationDivergenceAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) : ℝ :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  (2 : ℝ)⁻¹ *
    (inner ℝ
        (bilinearMetricTrace (secondCovariantDerivativeAt I connection x regular field hfield))
        w +
      bilinearMixedTraceAgainst
        (secondCovariantDerivativeAt I connection x regular field hfield) w)

/-- The deformation (strain) Laplacian `L_Def u = 2 Def* Def u = -2 (div_g Def u)♯` in tested
form: the value of the covector `⟨L_Def u, ·⟩` at `w`. -/
def deformationLaplacianTestedAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) : ℝ :=
  -2 * deformationDivergenceAt I connection x regular field hfield w

/-- The deformation Laplacian as an actual tangent vector.  This is the Riesz representative of
the independently constructed divergence-of-strain covector, written using its two intrinsic
trace vectors. -/
def deformationLaplacianAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  Neg.neg
    (bilinearMetricTrace (secondCovariantDerivativeAt I connection x regular field hfield) +
      bilinearMixedTrace (secondCovariantDerivativeAt I connection x regular field hfield))

omit [CompleteSpace E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The vector-valued deformation construction has exactly the established tested covector as its
metric pairing. -/
@[simp]
theorem inner_deformationLaplacianAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    inner ℝ (deformationLaplacianAt I connection x regular field hfield) w =
      deformationLaplacianTestedAt I connection x regular field hfield w := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [deformationLaplacianAt, inner_neg_left, inner_add_left,
    inner_bilinearMetricTrace, inner_bilinearMixedTrace]
  simp only [deformationLaplacianTestedAt, deformationDivergenceAt,
    inner_bilinearMetricTrace]
  ring

/-! ## The deformation tensor and its covariant derivative on raw fields -/

/-- The deformation tensor of CCD17 equation (1.2) evaluated on raw tangent fields:

`Def u (X,Y)(y) = ½ (⟨∇_X u, Y⟩ + ⟨∇_Y u, X⟩)(y)`. -/
def deformationValueAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field first second : (y : M) → TangentSpace I y) (y : M) : ℝ :=
  (2 : ℝ)⁻¹ *
    (inner ℝ (connection field y (first y)) (second y) +
      inner ℝ (connection field y (second y)) (first y))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- On a bundled `C^(k+1)` field, the raw deformation value is the bundled deformation tensor. -/
theorem deformationValueAt_eq_deformationTensor
    [Nontrivial E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (first second : (y : M) → TangentSpace I y) (y : M) :
    deformationValueAt I connection.connection field first second y =
      deformationTensor I regularity connection smooth field y (first y) (second y) := by
  rw [deformationTensor_apply]
  rfl

/-- The covariant derivative of the deformation tensor, evaluated on raw fields:

`(∇_X Def u)(Y,Z) = X (Def u (Y,Z)) - Def u (∇_X Y, Z) - Def u (Y, ∇_X Z)`. -/
def deformationCovariantDerivativeAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field direction first second : (y : M) → TangentSpace I y) (x : M) : ℝ :=
  d% (deformationValueAt I connection field first second) x (direction x) -
    deformationValueAt I connection field
      (covariantDerivativeAlong I connection direction first) second x -
    deformationValueAt I connection field first
      (covariantDerivativeAlong I connection direction second) x

/-- The workhorse expansion: the covariant derivative of the deformation tensor is the
symmetrization of the second covariant derivative in its last two slots,

`(∇_X Def u)(Y,Z) = ½ (⟨∇²u(X,Y),Z⟩ + ⟨∇²u(X,Z),Y⟩)`.

Metric compatibility converts the scalar derivative `X ⟨∇_Y u, Z⟩` into
`⟨∇_X ∇_Y u, Z⟩ + ⟨∇_Y u, ∇_X Z⟩`; the transported-slot corrections in the definition of
`∇_X Def u` remove exactly the non-second-derivative terms. -/
theorem deformationCovariantDerivativeAt_eq_secondDerivative
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field direction first second : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x)
    (hdirection : MDiffAt (T% direction) x)
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    deformationCovariantDerivativeAt I connection.connection field direction first second x =
      (2 : ℝ)⁻¹ *
        (inner ℝ
            (secondCovariantDerivativeAlong I connection.connection direction first field x)
            (second x) +
          inner ℝ
            (secondCovariantDerivativeAlong I connection.connection direction second field x)
            (first x)) := by
  have hσ₁ : MDiffAt (T% (covariantDerivativeAlong I connection.connection first field)) x :=
    regular first field hfirst hfield
  have hσ₂ : MDiffAt (T% (covariantDerivativeAlong I connection.connection second field)) x :=
    regular second field hsecond hfield
  have hf : MDiffAt (fun y ↦ inner ℝ
      (covariantDerivativeAlong I connection.connection first field y) (second y)) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _)) hσ₁ hsecond
  have hg : MDiffAt (fun y ↦ inner ℝ
      (covariantDerivativeAlong I connection.connection second field y) (first y)) x :=
    MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _)) hσ₂ hfirst
  have hfg : MDiffAt (fun y ↦ inner ℝ
      (covariantDerivativeAlong I connection.connection first field y) (second y) +
      inner ℝ (covariantDerivativeAlong I connection.connection second field y) (first y)) x :=
    hf.add hg
  -- The deformation value is half the sum of the two lowered covariant derivatives.
  have hvalue : deformationValueAt I connection.connection field first second =
      fun y ↦ (2 : ℝ)⁻¹ *
        (inner ℝ (covariantDerivativeAlong I connection.connection first field y) (second y) +
          inner ℝ (covariantDerivativeAlong I connection.connection second field y) (first y)) :=
    rfl
  -- Split the scalar derivative through constant multiplication and addition.
  have hsplit :
      d% (deformationValueAt I connection.connection field first second) x (direction x) =
        (2 : ℝ)⁻¹ *
          (d% (fun y ↦ inner ℝ
              (covariantDerivativeAlong I connection.connection first field y) (second y)) x
              (direction x) +
            d% (fun y ↦ inner ℝ
              (covariantDerivativeAlong I connection.connection second field y) (first y)) x
              (direction x)) := by
    rw [hvalue, mvfderiv_fun_mul (mdifferentiableAt_const ..) hfg, mvfderiv_fun_add hf hg]
    simp [mvfderiv_const]
    ring
  -- Metric compatibility for each lowered covariant derivative.
  have hcompat₁ := connection.metricCompatible hdirection hσ₁ hsecond
  have hcompat₂ := connection.metricCompatible hdirection hσ₂ hfirst
  rw [deformationCovariantDerivativeAt, hsplit, hcompat₁, hcompat₂]
  simp only [deformationValueAt, secondCovariantDerivativeAlong_apply, inner_sub_left,
    covariantDerivativeAlong]
  ring

/-- The intrinsic divergence of the deformation tensor is the orthonormal-frame sum of
covariant derivatives of the actual deformation tensor along canonical extensions:

`(div_g Def u)(Y(x)) = Σᵢ (∇_{Eᵢ} Def u)(Eᵢ, Y)(x)`. -/
theorem sum_deformationCovariantDerivativeAt_extend
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field second : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x) (hsecond : MDiffAt (T% second) x)
    {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ i, deformationCovariantDerivativeAt I connection.connection field
        (FiberBundle.extend E (basis i)) (FiberBundle.extend E (basis i)) second x =
      deformationDivergenceAt I connection.connection x regular field hfield (second x) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  have hterm : ∀ i,
      deformationCovariantDerivativeAt I connection.connection field
          (FiberBundle.extend E (basis i)) (FiberBundle.extend E (basis i)) second x =
        (2 : ℝ)⁻¹ *
          (inner ℝ
              (secondCovariantDerivativeAt I connection.connection x regular field hfield
                (basis i) (basis i)) (second x) +
            inner ℝ
              (secondCovariantDerivativeAt I connection.connection x regular field hfield
                (basis i) (second x)) (basis i)) := by
    intro i
    have hextend : MDiffAt (T% (FiberBundle.extend E (basis i))) x :=
      FiberBundle.mdifferentiableAt_extend ..
    have hx : FiberBundle.extend E (basis i) x = basis i := by simp
    have h1 := secondCovariantDerivativeAt_apply I connection.connection x regular field hfield
      hextend hextend
    have h2 := secondCovariantDerivativeAt_apply I connection.connection x regular field hfield
      hextend hsecond
    rw [hx] at h1 h2
    rw [deformationCovariantDerivativeAt_eq_secondDerivative I connection x regular hfield
      hextend hextend hsecond, ← h1, ← h2, hx]
  calc
    ∑ i, deformationCovariantDerivativeAt I connection.connection field
        (FiberBundle.extend E (basis i)) (FiberBundle.extend E (basis i)) second x =
        (2 : ℝ)⁻¹ *
          ((∑ i, inner ℝ
              (secondCovariantDerivativeAt I connection.connection x regular field hfield
                (basis i) (basis i)) (second x)) +
            ∑ i, inner ℝ
              (secondCovariantDerivativeAt I connection.connection x regular field hfield
                (basis i) (second x)) (basis i)) := by
      rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_add_distrib, Finset.mul_sum]
    _ = deformationDivergenceAt I connection.connection x regular field hfield (second x) := by
      rw [deformationDivergenceAt, ← bilinearMetricTraceAgainst_eq_sum basis,
        ← bilinearMixedTraceAgainst_eq_sum basis, inner_bilinearMetricTrace]

/-! ## Ricci commutation of the mixed trace -/

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Ricci commutation converts the mixed trace of `∇²u` into the trace of `∇²u(w,·)` plus the
Ricci contraction `Ric(w, u(x)) = tr(X ↦ R(X,w)u(x))`:

`Σᵢ ⟨∇²u(eᵢ,w),eᵢ⟩ = tr(∇²u(w,·)) + Ric(w, u(x))`. -/
theorem bilinearMixedTraceAgainst_secondCovariantDerivativeAt
    [IsManifold I 3 M]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (htorsion : connection.torsion = 0)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    bilinearMixedTraceAgainst
        (secondCovariantDerivativeAt I connection x regular field hfield) w =
      tangentTrace I x
          (secondCovariantDerivativeAt I connection x regular field hfield w) +
        connectionRicciFormAt I connection x regular w (field x) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  let basis := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [bilinearMixedTraceAgainst_eq_sum basis, tangentTrace_eq_sum_inner I basis,
    connectionRicciFormAt_eq_sum_inner I connection x regular basis w (field x),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hcomm := secondCovariantDerivativeAt_sub_swap I connection x regular htorsion field
    hfield (basis i) w
  rw [eq_add_of_sub_eq hcomm, inner_add_left, real_inner_comm
    (secondCovariantDerivativeAt I connection x regular field hfield w (basis i)) (basis i),
    real_inner_comm
      (connectionCurvatureTensorAt I connection x regular (basis i) w (field x)) (basis i)]
  ring

/-! ## Divergence commutation -/

/-- The scalar frame identity connecting the mixed trace of `∇²u` to the derivative of the
divergence:

`tr(v ↦ ∇²u(w,v)) = d(div u)(w)` at `x`.

This is the only ingredient of the operator comparison whose proof requires differentiating a
frame representation of the trace; `divergenceCommutationAt` below discharges it for every
Levi-Civita connection satisfying the curvature regularity bridge. -/
def DivergenceCommutationAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x) : Prop :=
  ∀ w : TangentSpace I x,
    tangentTrace I x (secondCovariantDerivativeAt I connection x regular field hfield w) =
      d% (fun y ↦ tangentTrace I y (connection field y)) x w

/-- The analytic core of divergence commutation, stated against an abstract metric-dual pair of
frame fields.

`F` is a frame of differentiable fields and `γ` its metric-dual family: the pairings `⟨γᵢ,Fⱼ⟩`
equal `δᵢⱼ` on a neighborhood of `x`, the divergence agrees near `x` with its frame
representation `Σᵢ ⟨γᵢ, ∇_{Fᵢ}u⟩`, and at `x` the pair computes expansions and traces.
Differentiating the frame representation with metric compatibility and expanding every frame
derivative in the dual pair, the non-second-derivative terms cancel in pairs against the
vanishing derivative of the constant pairing. -/
private theorem divergenceCommutation_of_dual_frame
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F γ : ι → (y : M) → TangentSpace I y)
    (hFm : ∀ i, MDiffAt (T% (F i)) x)
    (hγ : ∀ i, MDiffAt (T% (γ i)) x)
    (hdual_ev : ∀ᶠ y in 𝓝 x, ∀ i j,
      inner ℝ (γ i y) (F j y) = if i = j then (1 : ℝ) else 0)
    (hdiv_ev : (fun y ↦ tangentTrace I y (connection.connection field y)) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, inner ℝ (γ i y) (connection.connection field y (F i y)))
    (hbasis : ∀ z : TangentSpace I x, z = ∑ i, inner ℝ (γ i x) z • F i x)
    (htrace : ∀ S : TangentSpace I x →L[ℝ] TangentSpace I x,
      tangentTrace I x S = ∑ i, inner ℝ (γ i x) (S (F i x)))
    (w : TangentSpace I x) :
    tangentTrace I x
        (secondCovariantDerivativeAt I connection.connection x regular field hfield w) =
      d% (fun y ↦ tangentTrace I y (connection.connection field y)) x w := by
  have hW : MDiffAt (T% (FiberBundle.extend E w)) x :=
    FiberBundle.mdifferentiableAt_extend ..
  have hσ : ∀ i,
      MDiffAt (T% (covariantDerivativeAlong I connection.connection (F i) field)) x :=
    fun i ↦ regular (F i) field (hFm i) hfield
  -- Metric compatibility for each frame summand of the divergence.
  have hcompat : ∀ i,
      d% (fun y ↦ inner ℝ (γ i y) (connection.connection field y (F i y))) x w =
        inner ℝ (connection.connection (γ i) x w) (connection.connection field x (F i x)) +
          inner ℝ (γ i x)
            (connection.connection
              (covariantDerivativeAlong I connection.connection (F i) field) x w) := by
    intro i
    have hmc := connection.metricCompatible (X := FiberBundle.extend E w)
      (σ := γ i) (τ := covariantDerivativeAlong I connection.connection (F i) field)
      hW (hγ i) (hσ i)
    simp only [FiberBundle.extend_apply_self] at hmc
    exact hmc
  -- The derivative of the divergence through its frame representation.
  have hsummand : ∀ i ∈ (Finset.univ : Finset ι),
      MDiffAt (fun y ↦ inner ℝ (γ i y) (connection.connection field y (F i y))) x := by
    intro i _
    have hinner : MDiffAt (fun y ↦ inner ℝ (γ i y)
        (covariantDerivativeAlong I connection.connection (F i) field y)) x :=
      MDifferentiableAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
        (hγ i) (hσ i)
    exact hinner
  have hLHS : d% (fun y ↦ tangentTrace I y (connection.connection field y)) x w =
      ∑ i, (inner ℝ (connection.connection (γ i) x w)
          (connection.connection field x (F i x)) +
        inner ℝ (γ i x)
          (connection.connection
            (covariantDerivativeAlong I connection.connection (F i) field) x w)) := by
    rw [mvfderiv_congr_of_eventuallyEq I hdiv_ev,
      (mdifferentiableAt_and_mvfderiv_fun_sum I
        (h := fun i y ↦ inner ℝ (γ i y) (connection.connection field y (F i y)))
        Finset.univ hsummand).2]
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ hcompat i
  -- The mixed trace of the second derivative through the dual pair.
  have hRHS : tangentTrace I x
      (secondCovariantDerivativeAt I connection.connection x regular field hfield w) =
      ∑ i, (inner ℝ (γ i x)
          (connection.connection
            (covariantDerivativeAlong I connection.connection (F i) field) x w) -
        inner ℝ (γ i x)
          (connection.connection field x (connection.connection (F i) x w))) := by
    rw [htrace]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have happly := secondCovariantDerivativeAt_apply I connection.connection x regular field
      hfield hW (hFm i)
    rw [FiberBundle.extend_apply_self] at happly
    rw [happly, secondCovariantDerivativeAlong_apply, FiberBundle.extend_apply_self,
      inner_sub_right]
  -- Differentiating the constant duality pairing.
  have hdualderiv : ∀ i j,
      inner ℝ (connection.connection (γ i) x w) (F j x) +
        inner ℝ (γ i x) (connection.connection (F j) x w) = 0 := by
    intro i j
    have hmc := connection.metricCompatible (X := FiberBundle.extend E w)
      (σ := γ i) (τ := F j) hW (hγ i) (hFm j)
    simp only [FiberBundle.extend_apply_self] at hmc
    have hconst : (fun y ↦ inner ℝ (γ i y) (F j y)) =ᶠ[𝓝 x]
        fun _ ↦ (if i = j then (1 : ℝ) else 0) := by
      filter_upwards [hdual_ev] with y hy using hy i j
    have hzero : d% (fun y ↦ inner ℝ (γ i y) (F j y)) x = 0 := by
      rw [mvfderiv_congr_of_eventuallyEq I hconst]
      exact mvfderiv_const _
    rw [hzero] at hmc
    simpa using hmc.symm
  -- Expand each first-order term in the dual pair.
  have hexpand₁ : ∀ i,
      inner ℝ (connection.connection (γ i) x w) (connection.connection field x (F i x)) =
        ∑ j, inner ℝ (γ j x) (connection.connection field x (F i x)) *
          inner ℝ (connection.connection (γ i) x w) (F j x) := by
    intro i
    conv_lhs => rw [hbasis (connection.connection field x (F i x))]
    rw [inner_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [real_inner_smul_right, mul_comm]
  have hexpand₂ : ∀ i,
      inner ℝ (γ i x) (connection.connection field x (connection.connection (F i) x w)) =
        ∑ j, inner ℝ (γ j x) (connection.connection (F i) x w) *
          inner ℝ (γ i x) (connection.connection field x (F j x)) := by
    intro i
    have hdir : connection.connection field x (connection.connection (F i) x w) =
        ∑ j, inner ℝ (γ j x) (connection.connection (F i) x w) •
          connection.connection field x (F j x) := by
      conv_lhs => rw [hbasis (connection.connection (F i) x w)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]
    rw [hdir, inner_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [real_inner_smul_right]
  -- The pairwise cancellation of all non-second-derivative terms.
  have hAC : (∑ i, inner ℝ (connection.connection (γ i) x w)
        (connection.connection field x (F i x))) +
      (∑ i, inner ℝ (γ i x)
        (connection.connection field x (connection.connection (F i) x w))) = 0 := by
    rw [Finset.sum_congr rfl fun i _ ↦ hexpand₁ i,
      Finset.sum_congr rfl fun i _ ↦ hexpand₂ i]
    rw [show (∑ i, ∑ j, inner ℝ (γ j x) (connection.connection (F i) x w) *
        inner ℝ (γ i x) (connection.connection field x (F j x))) =
        ∑ i, ∑ j, inner ℝ (γ i x) (connection.connection (F j) x w) *
        inner ℝ (γ j x) (connection.connection field x (F i x)) from Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    calc
      inner ℝ (γ j x) (connection.connection field x (F i x)) *
          inner ℝ (connection.connection (γ i) x w) (F j x) +
        inner ℝ (γ i x) (connection.connection (F j) x w) *
          inner ℝ (γ j x) (connection.connection field x (F i x)) =
          inner ℝ (γ j x) (connection.connection field x (F i x)) *
            (inner ℝ (connection.connection (γ i) x w) (F j x) +
              inner ℝ (γ i x) (connection.connection (F j) x w)) := by ring
      _ = 0 := by rw [hdualderiv i j, mul_zero]
  rw [hRHS, hLHS, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith [hAC]

/-- Divergence commutation holds for every Levi-Civita connection satisfying the local
curvature-regularity bridge.

The metric-dual frame is constructed from the tangent trivialization at `x`: the local frame
`Fᵢ` is `C²` near `x`, its Gram matrix is invertible at `x` by positive definiteness, hence on a
neighborhood by continuity of the determinant, and the fields `γᵢ = Σⱼ (G⁻¹)ᵢⱼ Fⱼ` pair to the
identity with the frame exactly where the Gram matrix inverts. Smoothness of the inverse entries
follows from the adjugate formula, whose entries are signed products of frame inner products. -/
theorem divergenceCommutationAt_of_leviCivita
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x) :
    DivergenceCommutationAt I connection.connection x regular field hfield := by
  intro w
  classical
  letI : IsManifold I ((2 : ℕ∞ω) + 1) M := by
    norm_num
    infer_instance
  letI : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  letI : IsManifold I.tangent 2 (TangentBundle I M) := inferInstance
  set t := trivializationAt E (TangentSpace I : M → Type _) x with ht
  have x_mem : x ∈ t.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  set b := Module.Basis.ofVectorSpace ℝ E with hb
  set F : Module.Basis.ofVectorSpaceIndex ℝ E → (y : M) → TangentSpace I y :=
    t.localFrame b with hFdef
  have hF : ∀ i, CMDiffAt 2 (T% (F i)) x := fun i ↦
    contMDiffAt_localFrame_of_mem 2 t b i x_mem
  have hFm : ∀ i, MDiffAt (T% (F i)) x := fun i ↦ (hF i).mdifferentiableAt (by norm_num)
  -- Gram matrix of the frame and its determinant.
  set G : M → Matrix (Module.Basis.ofVectorSpaceIndex ℝ E)
      (Module.Basis.ofVectorSpaceIndex ℝ E) ℝ :=
    fun y ↦ Matrix.of fun i j ↦ inner ℝ (F i y) (F j y) with hGdef
  have hGentry : ∀ i j, CMDiffAt 1 (fun y ↦ G y i j) x := fun i j ↦
    ContMDiffAt.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
      ((hF i).of_le (by norm_num)) ((hF j).of_le (by norm_num))
  have hdet : CMDiffAt 1 (fun y ↦ (G y).det) x := contMDiffAt_matrix_det I hGentry
  have hbasisAtF : ∀ i, t.basisAt b x_mem i = F i x := fun i ↦
    (t.localFrame_apply_of_mem_baseSet b x_mem).symm
  -- Positive definiteness makes the Gram matrix invertible at the base point.
  have hdetx : (G x).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hz : ∀ i, inner ℝ (F i x) (∑ j, v j • F j x) = 0 := by
      intro i
      have hval := congrFun hmv i
      calc
        inner ℝ (F i x) (∑ j, v j • F j x) = ∑ j, G x i j * v j := by
          rw [inner_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by
            rw [real_inner_smul_right, mul_comm]
            rfl
        _ = (G x).mulVec v i := by
          simp [Matrix.mulVec, dotProduct]
        _ = 0 := hval
    have hzero : (∑ j, v j • F j x) = 0 := by
      have hself : inner ℝ (∑ j, v j • F j x) (∑ j, v j • F j x) = 0 := by
        rw [sum_inner]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [real_inner_smul_left, hz j, mul_zero]
      exact inner_self_eq_zero.mp hself
    refine hv0 (funext fun i ↦ ?_)
    refine Fintype.linearIndependent_iff.mp (t.basisAt b x_mem).linearIndependent v ?_ i
    calc
      ∑ j, v j • t.basisAt b x_mem j = ∑ j, v j • F j x :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hbasisAtF j]
      _ = 0 := hzero
  -- Entries of the inverse Gram matrix are differentiable at the base point.
  have hadj : ∀ i j, CMDiffAt 1 (fun y ↦ (G y).adjugate i j) x := by
    intro i j
    have hrw : (fun y ↦ (G y).adjugate i j) =
        fun y ↦ ((G y).updateRow j (Pi.single i 1)).det := by
      funext y
      rw [Matrix.adjugate_apply]
    rw [hrw]
    refine contMDiffAt_matrix_det I fun k l ↦ ?_
    by_cases hkj : k = j
    · subst hkj
      simp only [Matrix.updateRow_apply]
      exact contMDiffAt_const
    · simp only [Matrix.updateRow_apply, if_neg hkj]
      exact hGentry k l
  have hginv : ∀ i j, CMDiffAt 1 (fun y ↦ (G y)⁻¹ i j) x := by
    intro i j
    have hrw : (fun y ↦ (G y)⁻¹ i j) =
        fun y ↦ ((G y).det)⁻¹ * (G y).adjugate i j := by
      funext y
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
      simp [Matrix.smul_apply, smul_eq_mul]
    rw [hrw]
    exact (hdet.inv₀ hdetx).mul (hadj i j)
  -- The metric-dual frame.
  set γ : Module.Basis.ofVectorSpaceIndex ℝ E → (y : M) → TangentSpace I y :=
    fun i y ↦ ∑ j, (G y)⁻¹ i j • F j y with hγdef
  have hγ : ∀ i, MDiffAt (T% (γ i)) x := fun i ↦
    MDifferentiableAt.sum_section fun j _ ↦
      ((hginv i j).mdifferentiableAt (by norm_num)).smul_section (hFm j)
  -- Exact duality on the neighborhood where the Gram matrix inverts.
  have hdet_ev : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    hdet.continuousAt.eventually_ne hdetx
  have hdual_ev : ∀ᶠ y in 𝓝 x, ∀ i j,
      inner ℝ (γ i y) (F j y) = if i = j then (1 : ℝ) else 0 := by
    filter_upwards [hdet_ev] with y hy
    intro i j
    have hunit : IsUnit (G y).det := isUnit_iff_ne_zero.mpr hy
    calc
      inner ℝ (γ i y) (F j y) = ∑ k, (G y)⁻¹ i k * inner ℝ (F k y) (F j y) := by
        rw [hγdef]
        rw [sum_inner]
        exact Finset.sum_congr rfl fun k _ ↦ by rw [real_inner_smul_left]
      _ = ((G y)⁻¹ * G y) i j := by
        rw [Matrix.mul_apply]
        rfl
      _ = (1 : Matrix _ _ ℝ) i j := by rw [Matrix.nonsing_inv_mul (G y) hunit]
      _ = if i = j then 1 else 0 := Matrix.one_apply
  have hdualx : ∀ i j, inner ℝ (γ i x) (F j x) = if i = j then (1 : ℝ) else 0 :=
    hdual_ev.self_of_nhds
  have hdualBasis : ∀ i j,
      inner ℝ (γ i x) (t.basisAt b x_mem j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hbasisAtF j]
    exact hdualx i j
  -- Frame representation of the divergence near the base point.
  have hdiv_ev : (fun y ↦ tangentTrace I y (connection.connection field y)) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, inner ℝ (γ i y) (connection.connection field y (F i y)) := by
    have hbase : t.baseSet ∈ 𝓝 x := t.open_baseSet.mem_nhds x_mem
    filter_upwards [hdual_ev, hbase] with y hy hyb
    have hdualy : ∀ i j,
        inner ℝ (γ i y) (t.basisAt b hyb j) = if i = j then (1 : ℝ) else 0 := by
      intro i j
      rw [show t.basisAt b hyb j = F j y from
        (t.localFrame_apply_of_mem_baseSet b hyb).symm]
      exact hy i j
    have htracey := trace_eq_sum_inner_dualPair (t.basisAt b hyb) (fun i ↦ γ i y) hdualy
      (connection.connection field y)
    calc
      tangentTrace I y (connection.connection field y) =
          LinearMap.trace ℝ (TangentSpace I y)
            (connection.connection field y).toLinearMap := rfl
      _ = ∑ i, inner ℝ (γ i y) (connection.connection field y (t.basisAt b hyb i)) := htracey
      _ = ∑ i, inner ℝ (γ i y) (connection.connection field y (F i y)) :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [show t.basisAt b hyb i = F i y from
            (t.localFrame_apply_of_mem_baseSet b hyb).symm]
  -- Expansion and trace through the dual pair at the base point.
  have hbasisx : ∀ z : TangentSpace I x, z = ∑ i, inner ℝ (γ i x) z • F i x := by
    intro z
    have := eq_sum_inner_dualPair_smul (t.basisAt b x_mem) (fun i ↦ γ i x) hdualBasis z
    calc
      z = ∑ i, inner ℝ (γ i x) z • t.basisAt b x_mem i := this
      _ = ∑ i, inner ℝ (γ i x) z • F i x :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hbasisAtF i]
  have htracex : ∀ S : TangentSpace I x →L[ℝ] TangentSpace I x,
      tangentTrace I x S = ∑ i, inner ℝ (γ i x) (S (F i x)) := by
    intro S
    have := trace_eq_sum_inner_dualPair (t.basisAt b x_mem) (fun i ↦ γ i x) hdualBasis S
    calc
      tangentTrace I x S =
          LinearMap.trace ℝ (TangentSpace I x) S.toLinearMap := rfl
      _ = ∑ i, inner ℝ (γ i x) (S (t.basisAt b x_mem i)) := this
      _ = ∑ i, inner ℝ (γ i x) (S (F i x)) :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hbasisAtF i]
  exact divergenceCommutation_of_dual_frame I connection x regular hfield F γ hFm hγ
    hdual_ev hdiv_ev hbasisx htracex w

/-! ## The constructed comparison identities -/

/-- The constructed symmetric-gradient identity, tested pointwise:

`⟨L_Def u, w⟩ = ⟨L_rough u, w⟩ - d(div u)(w) - Ric(w, u(x))`.

This is CCD17's direct computation for `2 Def* Def` in divergence form; combined with any Hodge
realization of the Weitzenböck identity it reproduces equation (1.3). -/
theorem deformationLaplacian_rough_ricci_comparisonAt
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    deformationLaplacianTestedAt I connection.connection x regular field hfield w =
      inner ℝ (roughLaplacianAt I connection.connection x regular field hfield) w -
        d% (fun y ↦ tangentTrace I y (connection.connection field y)) x w -
        connectionRicciFormAt I connection.connection x regular w (field x) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [deformationLaplacianTestedAt, deformationDivergenceAt,
    bilinearMixedTraceAgainst_secondCovariantDerivativeAt I connection.connection x regular
      connection.torsionFree hfield w,
    divergenceCommutationAt_of_leviCivita I connection x regular hfield w,
    roughLaplacianAt, inner_neg_left, inner_bilinearMetricTrace]
  ring

/-- The constructed divergence-free comparison of CCD17 equation (1.3):

`⟨L_Def u, w⟩ = ⟨L_rough u, w⟩ - Ric(w, u(x))` for pointwise divergence-free `u`.

Given any Hodge operator satisfying the Weitzenböck identity `L_rough = L_Hodge - Ric`, this is
equivalent content to `L_Def = L_Hodge - 2 Ric` on divergence-free fields. -/
theorem deformationLaplacian_rough_ricci_comparisonAt_of_divergenceFree
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (hdiv : ∀ y, tangentTrace I y (connection.connection field y) = 0)
    (w : TangentSpace I x) :
    deformationLaplacianTestedAt I connection.connection x regular field hfield w =
      inner ℝ (roughLaplacianAt I connection.connection x regular field hfield) w -
        connectionRicciFormAt I connection.connection x regular w (field x) := by
  rw [deformationLaplacian_rough_ricci_comparisonAt I connection x regular hfield w]
  have hzero : (fun y ↦ tangentTrace I y (connection.connection field y)) =
      fun _ : M ↦ (0 : ℝ) :=
    funext hdiv
  rw [hzero, mvfderiv_const]
  simp

/-- Vector-valued form of the constructed divergence-free symmetric-gradient comparison:

`L_Def u = L_rough u - Ricᵀ(u)`,

where `Ricᵀ(u)` is the Riesz representative of `w ↦ Ric(w,u)`. -/
theorem deformationLaplacian_rough_ricci_comparisonVectorAt_of_divergenceFree
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (hdiv : ∀ y, tangentTrace I y (connection.connection field y) = 0) :
    deformationLaplacianAt I connection.connection x regular field hfield =
      roughLaplacianAt I connection.connection x regular field hfield -
        connectionRicciTransposeActionAt I connection.connection x regular (field x) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_deformationLaplacianAt, inner_sub_left,
    inner_connectionRicciTransposeActionAt,
    deformationLaplacian_rough_ricci_comparisonAt_of_divergenceFree
      I connection x regular hfield hdiv]

/-- The bundled form of the constructed divergence-free comparison, consuming an actual
`IsDivergenceFree` velocity field: for `div u = 0`,

`⟨L_Def u, w⟩ = ⟨L_rough u, w⟩ - Ric(w, u(x))` at every point.

The hypotheses are the packaged Levi-Civita properties, the local curvature-regularity bridge at
every point, and at least two derivatives of the velocity field. -/
theorem ccd17_divfree_def_rough_constructed
    [IsManifold I 3 M]
    (regularity : ℕ∞ω) (hreg : (2 : ℕ∞ω) ≤ regularity + 1)
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (regular : ∀ x, HasConnectionCurvatureRegularityAt I connection.connection x)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (hdiv : IsDivergenceFree I connection regularity smooth field)
    (x : M) (w : TangentSpace I x) :
    deformationLaplacianTestedAt I connection.connection x (regular x) field
        (field.contMDiff.contMDiffAt.of_le hreg) w =
      inner ℝ (roughLaplacianAt I connection.connection x (regular x) field
          (field.contMDiff.contMDiffAt.of_le hreg)) w -
        connectionRicciFormAt I connection.connection x (regular x) w (field x) :=
  deformationLaplacian_rough_ricci_comparisonAt_of_divergenceFree I connection x (regular x)
    (field.contMDiff.contMDiffAt.of_le hreg)
    ((isDivergenceFree_iff_pointwise I connection regularity smooth field).mp hdiv) w

end

end RiemannianFluids
