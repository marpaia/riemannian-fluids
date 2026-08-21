import RiemannianFluids.Operators.ConstructedLaplacians
import RiemannianFluids.Operators.Hodge
import RiemannianFluids.Tensors.ExteriorDerivativeConstructed

/-!
# The constructed Hodge Laplacian and the Weitzenböck identity

CCD17 (Chan--Czubak--Disconzi, arXiv:1608.05114v2, equation (1.1)) compares the rough Laplacian
with the Hodge Laplacian through the Weitzenböck identity. This module constructs the Hodge side
from the Levi-Civita connection and proves that identity, so that the full comparison
(1.1)--(1.3) holds with every operator constructed.

The analysis-positive Hodge Laplacian on the lowered field `u♭` splits into its two de Rham
halves,

    L_Hodge (u♭) = d₀ d₁* (u♭) + d₂* d₁ (u♭).

The exact half is concrete already: `d₁*(u♭) = -div u` (the sign fixed by `codifferentialOne`),
so `d₀ d₁*(u♭)` tested against `w` is `-d(div u)(w)`; `hodgeExactHalfTestedAt` records exactly
this, and `hodgeExactHalfTestedAt_eq_exactCodifferentialCorrectionOne` identifies it with the
bundled `d d*` operator of `Operators.Hodge` on bundled fields. The coexact half uses the
constructed exterior derivative of `Tensors.ExteriorDerivativeConstructed`: the degree-two
codifferential of `d₁(u♭)` is the negative metric trace over the outer slot pair,

    d₂* d₁ (u♭)(w) = -Σᵢ (∇_{eᵢ} d(u♭))(eᵢ, w),

and by the antisymmetric workhorse this equals `Σᵢ ⟨∇²u(eᵢ,w),eᵢ⟩ - Σᵢ ⟨∇²u(eᵢ,eᵢ),w⟩`.
`hodgeCoexactHalfTestedAt` takes the basis-free trace form of that expression as its
definition, and `sum_exteriorDerivativeCovariantDerivativeAt_extend` proves the
orthonormal-frame characterization tying it honestly to `d(u♭)`.

## Weitzenböck, proved

With both halves constructed, `weitzenbock_constructedAt` proves

    L_Hodge(u♭)(w) = ⟨L_rough u, w⟩ + Ric(w, u),

which is CCD17 equation (1.1) `B = H - R` in analysis-positive form. The proof is the exact
cancellation the classical argument promises: Ricci commutation converts the mixed trace of
`∇²u` into `tr ∇²u(w,·) + Ric(w,u)`, divergence commutation converts that trace into
`d(div u)(w)`, and this cancels the exact half `-d(div u)(w)`.

The sign bookkeeping is what makes the sum analysis-positive: `d₁* = -div ∘ ♯` and
`d₂* β (w) = -Σᵢ (∇_{eᵢ} β)(eᵢ, w)` carry the same relative sign, so on a flat manifold with
divergence-free `u` the constructed `L_Hodge` reduces to `∇*∇ ≥ 0`, never its negative.

## The full constructed comparison

Combining Weitzenböck with the proved divergence-form comparison
`deformationLaplacian_rough_ricci_comparisonAt` yields CCD17 equation (1.3),

    ⟨L_Def u, w⟩ = L_Hodge(u♭)(w) + d d*(u♭)(w) - 2 Ric(w, u),

with the exact correction `d d*(u♭)(w) = -d(div u)(w)`, and on divergence-free fields the
central identity `⟨L_Def u, w⟩ = L_Hodge(u♭)(w) - 2 Ric(w, u)` with every operator constructed
from the connection. The remaining hypotheses are explicit: the packaged Levi-Civita properties,
the pointwise curvature-regularity bridge, a `C³` atlas, and two derivatives of the field; the
Ricci term is the trace-of-first-slot contraction `Ric(w,u) = tr(X ↦ R(X,w)u)`.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

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

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The lowered covariant derivative decomposes into the deformation tensor and half the
constructed exterior derivative: `⟨∇_X u, Y⟩ = Def u(X,Y) + ½ d(u♭)(X,Y)`. -/
theorem covariantDerivativeTensorValueAt_eq_deformation_add_exterior
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field first second : (y : M) → TangentSpace I y) (y : M) :
    covariantDerivativeTensorValueAt I connection field first second y =
      deformationValueAt I connection field first second y +
        (2 : ℝ)⁻¹ * exteriorDerivativeValueAt I connection field first second y := by
  simp only [covariantDerivativeTensorValueAt, deformationValueAt, exteriorDerivativeValueAt]
  ring

/-! ## The bundled exterior derivative tensor

The raw-field `exteriorDerivativeValueAt` also assembles into a bundled smooth covariant
two-tensor: the difference of the metric-lowered covariant derivative and its transpose. This
mirrors `deformationTensor = symmetrize ∘ lower ∘ ∇`; the exterior derivative is twice the
complementary antisymmetrization of the same first-order tensor. -/

set_option synthInstance.maxHeartbeats 400000 in
/-- The constructed exterior derivative `d(u♭)` as a bundled smooth covariant two-tensor:

`d(u♭) = (∇u)♭ - ((∇u)♭)ᵀ`,

a first-order operator `C^(k+1)(TM) → C^k(T*M ⊗ T*M)` built from already-justified maps. Its
values are antisymmetric, and `exteriorDerivativeTensor_apply` recovers the raw-field
`exteriorDerivativeValueAt`, whose connection-independence is
`exteriorDerivativeValueAt_eq_mlieBracket`. -/
noncomputable def exteriorDerivativeTensor
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity) :
    SmoothVectorField (M := M) I (regularity + 1) →ₗ[ℝ]
      SmoothCovariantTwoTensor (M := M) I regularity :=
  -- Read right to left: form `(X,Y) ↦ ⟨∇_X u, Y⟩`, then subtract its transpose.
  (LinearMap.id - transposeCovariantTwoTensor I regularity).comp
    (covariantDerivativeTensor I regularity connection smooth)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
set_option synthInstance.maxHeartbeats 400000 in
/-- Pointwise evaluation of the bundled exterior derivative recovers the antisymmetrized
lowered covariant derivative. -/
@[simp]
theorem exteriorDerivativeTensor_apply
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (x : M) (u v : TangentSpace I x) :
    exteriorDerivativeTensor I regularity connection smooth field x u v =
      inner ℝ (connection.connection field x u) v -
        inner ℝ (connection.connection field x v) u := by
  simp [exteriorDerivativeTensor]

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
set_option synthInstance.maxHeartbeats 400000 in
/-- On a bundled field, the bundled exterior derivative tensor computes the raw-field value. -/
theorem exteriorDerivativeTensor_eq_exteriorDerivativeValueAt
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1))
    (first second : (y : M) → TangentSpace I y) (y : M) :
    exteriorDerivativeTensor I regularity connection smooth field y (first y) (second y) =
      exteriorDerivativeValueAt I connection.connection field first second y := by
  rw [exteriorDerivativeTensor_apply]
  rfl

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
set_option synthInstance.maxHeartbeats 400000 in
/-- The bundled exterior derivative is twice the antisymmetrization projection of the lowered
covariant derivative, the exact complement of `deformationTensor = symmetrize` of the same
tensor. -/
theorem exteriorDerivativeTensor_eq_two_antisymmetrize
    [Nontrivial E]
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection regularity)
    (field : SmoothVectorField (M := M) I (regularity + 1)) :
    exteriorDerivativeTensor I regularity connection smooth field =
      (2 : ℝ) • antisymmetrizeCovariantTwoTensor I regularity
        (covariantDerivativeTensor I regularity connection smooth field) := by
  -- Equality of tensor fields is pointwise on two tangent arguments.
  ext x u v
  show exteriorDerivativeTensor I regularity connection smooth field x u v =
    (2 : ℝ) * antisymmetrizeCovariantTwoTensor I regularity
      (covariantDerivativeTensor I regularity connection smooth field) x u v
  rw [exteriorDerivativeTensor_apply, antisymmetrizeCovariantTwoTensor_apply,
    covariantDerivativeTensor_apply, covariantDerivativeTensor_apply]
  -- Doubling the difference average recovers the difference.
  ring

/-! ## The two Hodge halves, tested -/

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The exact Hodge half `d₀ d₁* (u♭)` tested against `w`:

`d₀ d₁*(u♭)(w) = -d(div u)(w)`,

using `d₁*(u♭) = -div u` and the pointwise divergence `div u (y) = tr(∇u)(y)`. On bundled
fields, `hodgeExactHalfTestedAt_eq_exactCodifferentialCorrectionOne` identifies this value with
the bundled exact correction `d d*` of `Operators.Hodge`. -/
def hodgeExactHalfTestedAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field : (y : M) → TangentSpace I y) (x : M) (w : TangentSpace I x) : ℝ :=
  -d% (fun y ↦ tangentTrace I y (connection field y)) x w

/-- The exact Hodge half as an actual tangent vector, obtained by raising the independently
constructed covector `-d(div u)`. -/
def hodgeExactHalfAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field : (y : M) → TangentSpace I y) (x : M) : TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  Neg.neg (rieszRepresentative
    (d% (fun y ↦ tangentTrace I y (connection field y)) x).toLinearMap)

omit [CompleteSpace E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Testing the vector-valued exact half recovers `-d(div u)`. -/
@[simp]
theorem inner_hodgeExactHalfAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field : (y : M) → TangentSpace I y) (x : M) (w : TangentSpace I x) :
    inner ℝ (hodgeExactHalfAt I connection field x) w =
      hodgeExactHalfTestedAt I connection field x w := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [hodgeExactHalfAt, inner_neg_left, inner_rieszRepresentative]
  rfl

/-- The coexact Hodge half `d₂* d₁ (u♭)` tested against `w`, in basis-free trace form:

`d₂* d₁(u♭)(w) = Σᵢ ⟨∇²u(eᵢ,w),eᵢ⟩ - Σᵢ ⟨∇²u(eᵢ,eᵢ),w⟩`.

The definition uses the intrinsic mixed and metric traces of the pointwise second covariant
derivative, so no basis is chosen. The theorem
`sum_exteriorDerivativeCovariantDerivativeAt_extend` proves that this value is
`-Σᵢ (∇_{Eᵢ} d(u♭))(Eᵢ, w)` in every orthonormal frame, tying the operator to the constructed
exterior derivative `d(u♭)`. -/
def hodgeCoexactHalfTestedAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) : ℝ :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  bilinearMixedTraceAgainst
      (secondCovariantDerivativeAt I connection x regular field hfield) w -
    inner ℝ
      (bilinearMetricTrace (secondCovariantDerivativeAt I connection x regular field hfield)) w

/-- The coexact Hodge half as an actual tangent vector.  Its two terms are the Riesz
representatives of the mixed and metric traces of the constructed second derivative. -/
def hodgeCoexactHalfAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x :=
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  bilinearMixedTrace (secondCovariantDerivativeAt I connection x regular field hfield) -
    bilinearMetricTrace (secondCovariantDerivativeAt I connection x regular field hfield)

omit [CompleteSpace E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Testing the vector-valued coexact half recovers the constructed codifferential trace. -/
@[simp]
theorem inner_hodgeCoexactHalfAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    inner ℝ (hodgeCoexactHalfAt I connection x regular field hfield) w =
      hodgeCoexactHalfTestedAt I connection x regular field hfield w := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [hodgeCoexactHalfAt, inner_sub_left, inner_bilinearMixedTrace,
    inner_bilinearMetricTrace]
  rw [hodgeCoexactHalfTestedAt, inner_bilinearMetricTrace]

/-- The coexact half is the negative orthonormal-frame trace of the covariant derivative of the
constructed exterior derivative along canonical extensions:

`Σᵢ (∇_{Eᵢ} d(u♭))(Eᵢ, Y)(x) = -d₂* d₁(u♭)(Y(x))`.

This is the honesty theorem for `hodgeCoexactHalfTestedAt`: the intrinsic trace expression in
its definition is the codifferential of the actual constructed two-form `d(u♭)`. -/
theorem sum_exteriorDerivativeCovariantDerivativeAt_extend
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field second : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x) (hsecond : MDiffAt (T% second) x)
    {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ i, exteriorDerivativeCovariantDerivativeAt I connection.connection field
        (FiberBundle.extend E (basis i)) (FiberBundle.extend E (basis i)) second x =
      -hodgeCoexactHalfTestedAt I connection.connection x regular field hfield (second x) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  have hterm : ∀ i,
      exteriorDerivativeCovariantDerivativeAt I connection.connection field
          (FiberBundle.extend E (basis i)) (FiberBundle.extend E (basis i)) second x =
        inner ℝ
            (secondCovariantDerivativeAt I connection.connection x regular field hfield
              (basis i) (basis i)) (second x) -
          inner ℝ
            (secondCovariantDerivativeAt I connection.connection x regular field hfield
              (basis i) (second x)) (basis i) := by
    intro i
    have hextend : MDiffAt (T% (FiberBundle.extend E (basis i))) x :=
      FiberBundle.mdifferentiableAt_extend ..
    have hx : FiberBundle.extend E (basis i) x = basis i := by simp
    have h1 := secondCovariantDerivativeAt_apply I connection.connection x regular field hfield
      hextend hextend
    have h2 := secondCovariantDerivativeAt_apply I connection.connection x regular field hfield
      hextend hsecond
    rw [hx] at h1 h2
    rw [exteriorDerivativeCovariantDerivativeAt_eq_secondDerivative I connection x regular
      hfield hextend hextend hsecond, ← h1, ← h2, hx]
  calc
    ∑ i, exteriorDerivativeCovariantDerivativeAt I connection.connection field
        (FiberBundle.extend E (basis i)) (FiberBundle.extend E (basis i)) second x =
        (∑ i, inner ℝ
            (secondCovariantDerivativeAt I connection.connection x regular field hfield
              (basis i) (basis i)) (second x)) -
          ∑ i, inner ℝ
            (secondCovariantDerivativeAt I connection.connection x regular field hfield
              (basis i) (second x)) (basis i) := by
      rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib]
    _ = -hodgeCoexactHalfTestedAt I connection.connection x regular field hfield (second x) := by
      rw [hodgeCoexactHalfTestedAt, ← bilinearMetricTraceAgainst_eq_sum basis,
        ← bilinearMixedTraceAgainst_eq_sum basis, inner_bilinearMetricTrace]
      ring

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- On bundled fields, the raw exact half agrees with the bundled exact correction
`d d* (u♭)` of `Operators.Hodge`, evaluated as a one-form. -/
theorem hodgeExactHalfTestedAt_eq_exactCodifferentialCorrectionOne
    (regularity : ℕ∞ω)
    [IsContMDiffRiemannianBundle I regularity E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I (SecondOrderRegularity regularity) E
      (TangentSpace I : M → Type _)]
    (connection : LeviCivitaConnection (M := M) I)
    (smooth : LeviCivitaConnection.IsContMDiff I connection (regularity + 1))
    (field : SmoothVectorField (M := M) I (SecondOrderRegularity regularity))
    (x : M) (w : TangentSpace I x) :
    hodgeExactHalfTestedAt I connection.connection field x w =
      exactCodifferentialCorrectionOne I regularity connection smooth
        (flat I (SecondOrderRegularity regularity) field) x w := by
  -- The bundled correction is the manifold derivative of the bundled codifferential scalar.
  have hcomp : exactCodifferentialCorrectionOne I regularity connection smooth
      (flat I (SecondOrderRegularity regularity) field) =
      scalarDifferential I regularity
        (codifferentialOne I (regularity + 1) connection smooth
          (flat I (SecondOrderRegularity regularity) field)) :=
    rfl
  -- The codifferential scalar is the negative pointwise divergence.
  have hcoe : (codifferentialOne I (regularity + 1) connection smooth
      (flat I (SecondOrderRegularity regularity) field) : M → ℝ) =
      fun y ↦ -tangentTrace I y (connection.connection field y) := by
    rw [codifferentialOne_flat]
    rfl
  rw [hcomp, scalarDifferential_apply, hcoe, mvfderiv_fun_neg, hodgeExactHalfTestedAt]
  simp

/-! ## The constructed Hodge Laplacian and the Weitzenböck identity -/

/-- The analysis-positive Hodge Laplacian `L_Hodge = d₀ d₁* + d₂* d₁` on the lowered field
`u♭`, tested against `w`. Both halves are constructed from the connection; CCD17 writes the
signed operator `Δ_H = -L_Hodge`. -/
def hodgeLaplacianConstructedTestedAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) : ℝ :=
  hodgeExactHalfTestedAt I connection field x w +
    hodgeCoexactHalfTestedAt I connection x regular field hfield w

/-- The constructed Hodge Laplacian as an actual tangent-vector output.  Both de Rham halves are
raised only after their covectors have been constructed. -/
def hodgeLaplacianConstructedAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x :=
  hodgeExactHalfAt I connection field x +
    hodgeCoexactHalfAt I connection x regular field hfield

omit [CompleteSpace E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The vector-valued Hodge construction has exactly the established tested scalar as its metric
pairing. -/
@[simp]
theorem inner_hodgeLaplacianConstructedAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y) (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    inner ℝ (hodgeLaplacianConstructedAt I connection x regular field hfield) w =
      hodgeLaplacianConstructedTestedAt I connection x regular field hfield w := by
  rw [hodgeLaplacianConstructedAt, inner_add_left, inner_hodgeExactHalfAt,
    inner_hodgeCoexactHalfAt, hodgeLaplacianConstructedTestedAt]

/-- The Weitzenböck identity for the constructed operators, CCD17 equation (1.1) in
analysis-positive form:

`L_Hodge(u♭)(w) = ⟨L_rough u, w⟩ + Ric(w, u(x))`.

Ricci commutation rewrites the mixed trace in the coexact half as `tr ∇²u(w,·) + Ric(w,u)`,
divergence commutation identifies that trace with `d(div u)(w)`, and the exact half cancels it
exactly. Torsion-freeness and metric compatibility enter through the packaged Levi-Civita
connection; the curvature-regularity bridge and the `C³` atlas are the same envelope as the
deformation comparison. -/
theorem weitzenbock_constructedAt
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    hodgeLaplacianConstructedTestedAt I connection.connection x regular field hfield w =
      inner ℝ (roughLaplacianAt I connection.connection x regular field hfield) w +
        connectionRicciFormAt I connection.connection x regular w (field x) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := tangentFiniteDimensional I x
  rw [hodgeLaplacianConstructedTestedAt, hodgeExactHalfTestedAt, hodgeCoexactHalfTestedAt,
    bilinearMixedTraceAgainst_secondCovariantDerivativeAt I connection.connection x regular
      connection.torsionFree hfield w,
    divergenceCommutationAt_of_leviCivita I connection x regular hfield w,
    roughLaplacianAt, inner_neg_left, inner_bilinearMetricTrace]
  ring

/-- Vector-valued Weitzenböck identity for the independently constructed outputs:

`L_Hodge u = L_rough u + Ricᵀ(u)`,

where the transposed action represents the repository's pre-Bianchi slot order
`w ↦ Ric(w,u)`. -/
theorem weitzenbock_constructedVectorAt
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x) :
    hodgeLaplacianConstructedAt I connection.connection x regular field hfield =
      roughLaplacianAt I connection.connection x regular field hfield +
        connectionRicciTransposeActionAt I connection.connection x regular (field x) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_hodgeLaplacianConstructedAt, inner_add_left,
    inner_connectionRicciTransposeActionAt,
    weitzenbock_constructedAt I connection x regular hfield w]

/-! ## CCD17 equation (1.3), fully constructed -/

/-- CCD17 equation (1.3) with every operator constructed, in analysis-positive tested form:

`⟨L_Def u, w⟩ = L_Hodge(u♭)(w) + d d*(u♭)(w) - 2 Ric(w, u(x))`,

where the exact correction is `d d*(u♭)(w) = -d(div u)(w)`. Pure algebra combining the proved
symmetric-gradient comparison with the proved Weitzenböck identity. -/
theorem ccd17_full_constructedAt
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (w : TangentSpace I x) :
    deformationLaplacianTestedAt I connection.connection x regular field hfield w =
      hodgeLaplacianConstructedTestedAt I connection.connection x regular field hfield w +
        hodgeExactHalfTestedAt I connection.connection field x w -
        2 * connectionRicciFormAt I connection.connection x regular w (field x) := by
  rw [deformationLaplacian_rough_ricci_comparisonAt I connection x regular hfield w,
    weitzenbock_constructedAt I connection x regular hfield w, hodgeExactHalfTestedAt]
  ring

/-- The central CCD17 identity on pointwise divergence-free fields, every operator constructed:

`⟨L_Def u, w⟩ = L_Hodge(u♭)(w) - 2 Ric(w, u(x))`.

Divergence-freeness kills the exact correction `-d(div u)(w)`. -/
theorem ccd17_divfree_def_hodge_constructedAt
    [IsManifold I 3 M]
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field : (y : M) → TangentSpace I y} (hfield : CMDiffAt 2 (T% field) x)
    (hdiv : ∀ y, tangentTrace I y (connection.connection field y) = 0)
    (w : TangentSpace I x) :
    deformationLaplacianTestedAt I connection.connection x regular field hfield w =
      hodgeLaplacianConstructedTestedAt I connection.connection x regular field hfield w -
        2 * connectionRicciFormAt I connection.connection x regular w (field x) := by
  rw [ccd17_full_constructedAt I connection x regular hfield w]
  have hzero : (fun y ↦ tangentTrace I y (connection.connection field y)) =
      fun _ : M ↦ (0 : ℝ) :=
    funext hdiv
  rw [hodgeExactHalfTestedAt, hzero, mvfderiv_const]
  simp

/-- The bundled form of the constructed CCD17 identity, consuming an actual `IsDivergenceFree`
velocity field: for `div u = 0`,

`⟨L_Def u, w⟩ = L_Hodge(u♭)(w) - 2 Ric(w, u(x))` at every point,

with the deformation Laplacian, the Hodge Laplacian (both de Rham halves), and the Ricci
contraction all constructed from the packaged Levi-Civita connection. The hypotheses are the
packaged Levi-Civita properties, the local curvature-regularity bridge at every point, a `C³`
atlas, and at least two derivatives of the velocity field. -/
theorem ccd17_divfree_def_hodge_constructed
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
      hodgeLaplacianConstructedTestedAt I connection.connection x (regular x) field
          (field.contMDiff.contMDiffAt.of_le hreg) w -
        2 * connectionRicciFormAt I connection.connection x (regular x) w (field x) :=
  ccd17_divfree_def_hodge_constructedAt I connection x (regular x)
    (field.contMDiff.contMDiffAt.of_le hreg)
    ((isDivergenceFree_iff_pointwise I connection regularity smooth field).mp hdiv) w

end

end RiemannianFluids
