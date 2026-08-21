import Mathlib.Geometry.Manifold.VectorField.LieBracket
import RiemannianFluids.Geometry.Connections
import RiemannianFluids.Tensors.SecondDerivative

/-!
# The exterior derivative of a lowered vector field, constructed from the connection

The pinned Mathlib manifold API has no exterior derivative on one-forms. For the degree needed
by the CCD17 operator comparison none is required: on a Riemannian manifold with a Levi-Civita
connection, the exterior derivative of the lowered field `u♭` is the antisymmetrization of the
metric-lowered covariant derivative,

    d(u♭)(X,Y) = ⟨∇_X u, Y⟩ - ⟨∇_Y u, X⟩.

`exteriorDerivativeValueAt` takes this antisymmetrization as the definition. What makes the
definition honest is `exteriorDerivativeValueAt_eq_mlieBracket`: the same quantity equals the
connection-free bracket formula

    d(u♭)(X,Y) = X ⟨u,Y⟩ - Y ⟨u,X⟩ - ⟨u, [X,Y]⟩,

which is the intrinsic exterior derivative of the one-form `⟨u,·⟩` evaluated on vector fields.
The proof is the same two-step cancellation as the metric Lie-derivative identity: metric
compatibility rewrites both scalar derivatives, torsion-freeness rewrites the bracket as a
difference of covariant derivatives, and the terms differentiating `X` and `Y` cancel — with a
relative sign flip compared to the symmetric case. Since the right-hand side never mentions the
connection, the theorem proves that the constructed `d` is independent of the choice of
Levi-Civita connection.

## The covariant derivative of the lowered gradient

The tensor `⟨∇_X u, Y⟩` whose antisymmetric part is `½ d(u♭)` and whose symmetric part is
`Def u` is the metric-lowered covariant derivative; `covariantDerivativeTensorValueAt` is its
raw-field value, matching the bundled `covariantDerivativeTensor`. Its covariant derivative
satisfies the single clean identity

    (∇_X (∇u)♭)(Y,Z) = ⟨∇²u(X,Y), Z⟩,

proved from metric compatibility alone: the scalar derivative `X ⟨∇_Y u, Z⟩` produces
`⟨∇_X ∇_Y u, Z⟩ + ⟨∇_Y u, ∇_X Z⟩`, the transported-slot corrections remove `⟨∇_{∇_X Y} u, Z⟩`
and exactly the second summand, and what remains is the second covariant derivative of
`Tensors.SecondDerivative`. The covariant derivative of `d(u♭)` is then pure algebra:

    (∇_X d(u♭))(Y,Z) = ⟨∇²u(X,Y), Z⟩ - ⟨∇²u(X,Z), Y⟩.

These raw-field identities feed the constructed codifferential and Hodge Laplacian in
`Operators.ConstructedHodge`, where their traces produce the Weitzenböck identity.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

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

/-- The metric-lowered covariant derivative evaluated on raw tangent fields:

`(∇u)♭(X,Y)(y) = ⟨∇_X u, Y⟩(y)`.

This is the raw-field value of the bundled `covariantDerivativeTensor`; its symmetric part is
`deformationValueAt` and its antisymmetric part is `exteriorDerivativeValueAt`. -/
def covariantDerivativeTensorValueAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field first second : (y : M) → TangentSpace I y) (y : M) : ℝ :=
  inner ℝ (connection field y (first y)) (second y)

/-- The constructed exterior derivative of the lowered field `u♭`, evaluated on raw tangent
fields:

`d(u♭)(X,Y)(y) = ⟨∇_X u, Y⟩(y) - ⟨∇_Y u, X⟩(y)`.

The antisymmetrization of the lowered covariant derivative; the honesty theorem
`exteriorDerivativeValueAt_eq_mlieBracket` identifies it with the connection-free bracket
formula for the exterior derivative of the one-form `⟨u,·⟩`. -/
def exteriorDerivativeValueAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field first second : (y : M) → TangentSpace I y) (y : M) : ℝ :=
  inner ℝ (connection field y (first y)) (second y) -
    inner ℝ (connection field y (second y)) (first y)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The constructed exterior derivative is the difference of the lowered covariant derivative
and its transpose. -/
theorem exteriorDerivativeValueAt_eq_sub
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field first second : (y : M) → TangentSpace I y) (y : M) :
    exteriorDerivativeValueAt I connection field first second y =
      covariantDerivativeTensorValueAt I connection field first second y -
        covariantDerivativeTensorValueAt I connection field second first y :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The constructed exterior derivative is antisymmetric in its two arguments. -/
theorem exteriorDerivativeValueAt_swap
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field first second : (y : M) → TangentSpace I y) (y : M) :
    exteriorDerivativeValueAt I connection field first second y =
      -exteriorDerivativeValueAt I connection field second first y := by
  simp only [exteriorDerivativeValueAt]
  ring

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The honesty theorem for the constructed exterior derivative: for a Levi-Civita connection,

`d(u♭)(X,Y) = X ⟨u,Y⟩ - Y ⟨u,X⟩ - ⟨u, [X,Y]⟩` at `x`.

The right-hand side is the intrinsic exterior derivative of the one-form `⟨u,·⟩` in its
connection-free bracket characterization: it involves only manifold derivatives of scalar
functions and Mathlib's Lie bracket. Metric compatibility converts each scalar derivative into
covariant-derivative pairings, torsion-freeness converts the bracket into `∇_X Y - ∇_Y X`, and
the terms differentiating the test fields cancel. Because the bracket formula never mentions
the connection, the constructed `d` is independent of the choice of Levi-Civita connection. -/
theorem exteriorDerivativeValueAt_eq_mlieBracket
    (connection : LeviCivitaConnection (M := M) I)
    {field first second : (y : M) → TangentSpace I y} {x : M}
    (hfield : MDiffAt (T% field) x) (hfirst : MDiffAt (T% first) x)
    (hsecond : MDiffAt (T% second) x) :
    exteriorDerivativeValueAt I connection.connection field first second x =
      d% (fun y ↦ inner ℝ (field y) (second y)) x (first x) -
        d% (fun y ↦ inner ℝ (field y) (first y)) x (second x) -
        inner ℝ (field x) (VectorField.mlieBracket I first second x) := by
  -- Metric compatibility: `X ⟨u,Y⟩ = ⟨∇_X u, Y⟩ + ⟨u, ∇_X Y⟩` at `x`, and symmetrically.
  have hcompat₁ := connection.metricCompatible hfirst hfield hsecond
  have hcompat₂ := connection.metricCompatible hsecond hfield hfirst
  -- Torsion-freeness in bracket form: `[X,Y] = ∇_X Y - ∇_Y X` at `x`.
  have hbracket : VectorField.mlieBracket I first second x =
      connection.connection second x (first x) - connection.connection first x (second x) :=
    (connection.connection.torsion_eq_zero_iff.mp connection.torsionFree hfirst hsecond).symm
  rw [hcompat₁, hcompat₂, hbracket, inner_sub_right]
  simp only [exteriorDerivativeValueAt]
  ring

/-! ## The covariant derivative of the lowered gradient -/

/-- The covariant derivative of the lowered covariant derivative, evaluated on raw fields:

`(∇_X (∇u)♭)(Y,Z) = X ((∇u)♭(Y,Z)) - (∇u)♭(∇_X Y, Z) - (∇u)♭(Y, ∇_X Z)`. -/
def covariantDerivativeTensorCovariantDerivativeAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field direction first second : (y : M) → TangentSpace I y) (x : M) : ℝ :=
  d% (covariantDerivativeTensorValueAt I connection field first second) x (direction x) -
    covariantDerivativeTensorValueAt I connection field
      (covariantDerivativeAlong I connection direction first) second x -
    covariantDerivativeTensorValueAt I connection field first
      (covariantDerivativeAlong I connection direction second) x

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The unsymmetrized workhorse: the covariant derivative of the lowered covariant derivative
is the lowered second covariant derivative,

`(∇_X (∇u)♭)(Y,Z) = ⟨∇²u(X,Y), Z⟩`.

Metric compatibility converts the scalar derivative `X ⟨∇_Y u, Z⟩` into
`⟨∇_X ∇_Y u, Z⟩ + ⟨∇_Y u, ∇_X Z⟩`; the transported-slot corrections remove `⟨∇_{∇_X Y} u, Z⟩`
and exactly the second summand, leaving the second covariant derivative. The symmetrization of
this identity is the deformation workhorse
`deformationCovariantDerivativeAt_eq_secondDerivative`; the antisymmetrization is
`exteriorDerivativeCovariantDerivativeAt_eq_secondDerivative` below. -/
theorem covariantDerivativeTensorCovariantDerivativeAt_eq_secondDerivative
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field direction first second : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x)
    (hdirection : MDiffAt (T% direction) x)
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    covariantDerivativeTensorCovariantDerivativeAt I connection.connection
        field direction first second x =
      inner ℝ (secondCovariantDerivativeAlong I connection.connection direction first field x)
        (second x) := by
  have hσ : MDiffAt (T% (covariantDerivativeAlong I connection.connection first field)) x :=
    regular first field hfirst hfield
  -- The differentiated scalar is the lowered once-differentiated field.
  have hvalue : covariantDerivativeTensorValueAt I connection.connection field first second =
      fun y ↦ inner ℝ (covariantDerivativeAlong I connection.connection first field y)
        (second y) :=
    rfl
  have hcompat := connection.metricCompatible hdirection hσ hsecond
  rw [covariantDerivativeTensorCovariantDerivativeAt, hvalue, hcompat]
  simp only [covariantDerivativeTensorValueAt, secondCovariantDerivativeAlong_apply,
    inner_sub_left, covariantDerivativeAlong]
  ring

/-- The covariant derivative of the constructed exterior derivative `d(u♭)`, evaluated on raw
fields:

`(∇_X d(u♭))(Y,Z) = X (d(u♭)(Y,Z)) - d(u♭)(∇_X Y, Z) - d(u♭)(Y, ∇_X Z)`. -/
def exteriorDerivativeCovariantDerivativeAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (field direction first second : (y : M) → TangentSpace I y) (x : M) : ℝ :=
  d% (exteriorDerivativeValueAt I connection field first second) x (direction x) -
    exteriorDerivativeValueAt I connection field
      (covariantDerivativeAlong I connection direction first) second x -
    exteriorDerivativeValueAt I connection field first
      (covariantDerivativeAlong I connection direction second) x

/-- Covariant differentiation commutes with the antisymmetrization defining `d(u♭)`:

`(∇_X d(u♭))(Y,Z) = (∇_X (∇u)♭)(Y,Z) - (∇_X (∇u)♭)(Z,Y)`.

The derivative of the difference splits because each lowered summand is differentiable through
the curvature-regularity bridge; the slot corrections regroup by pure algebra. -/
theorem exteriorDerivativeCovariantDerivativeAt_eq_sub
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field direction first second : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x)
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    exteriorDerivativeCovariantDerivativeAt I connection.connection
        field direction first second x =
      covariantDerivativeTensorCovariantDerivativeAt I connection.connection
          field direction first second x -
        covariantDerivativeTensorCovariantDerivativeAt I connection.connection
          field direction second first x := by
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
  -- The constructed exterior derivative is the difference of the two lowered scalars.
  have hvalue : exteriorDerivativeValueAt I connection.connection field first second =
      fun y ↦ inner ℝ (covariantDerivativeAlong I connection.connection first field y)
          (second y) -
        inner ℝ (covariantDerivativeAlong I connection.connection second field y) (first y) :=
    rfl
  have hT₁ : covariantDerivativeTensorValueAt I connection.connection field first second =
      fun y ↦ inner ℝ (covariantDerivativeAlong I connection.connection first field y)
        (second y) :=
    rfl
  have hT₂ : covariantDerivativeTensorValueAt I connection.connection field second first =
      fun y ↦ inner ℝ (covariantDerivativeAlong I connection.connection second field y)
        (first y) :=
    rfl
  -- Split the derivative of the difference.
  have hsplit :
      d% (exteriorDerivativeValueAt I connection.connection field first second) x
          (direction x) =
        d% (fun y ↦ inner ℝ
            (covariantDerivativeAlong I connection.connection first field y) (second y)) x
            (direction x) -
          d% (fun y ↦ inner ℝ
            (covariantDerivativeAlong I connection.connection second field y) (first y)) x
            (direction x) := by
    rw [hvalue, mvfderiv_fun_sub hf hg, sub_apply]
  rw [exteriorDerivativeCovariantDerivativeAt, hsplit,
    covariantDerivativeTensorCovariantDerivativeAt,
    covariantDerivativeTensorCovariantDerivativeAt, hT₁, hT₂]
  simp only [exteriorDerivativeValueAt, covariantDerivativeTensorValueAt]
  ring

/-- The antisymmetric workhorse: the covariant derivative of the constructed exterior
derivative is the antisymmetrized lowered second covariant derivative,

`(∇_X d(u♭))(Y,Z) = ⟨∇²u(X,Y), Z⟩ - ⟨∇²u(X,Z), Y⟩`.

Its metric trace over the outer pair of slots is the constructed codifferential of `d(u♭)` in
`Operators.ConstructedHodge`. -/
theorem exteriorDerivativeCovariantDerivativeAt_eq_secondDerivative
    (connection : LeviCivitaConnection (M := M) I) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection.connection x)
    {field direction first second : (y : M) → TangentSpace I y}
    (hfield : CMDiffAt 2 (T% field) x)
    (hdirection : MDiffAt (T% direction) x)
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    exteriorDerivativeCovariantDerivativeAt I connection.connection
        field direction first second x =
      inner ℝ (secondCovariantDerivativeAlong I connection.connection direction first field x)
          (second x) -
        inner ℝ (secondCovariantDerivativeAlong I connection.connection direction second field x)
          (first x) := by
  rw [exteriorDerivativeCovariantDerivativeAt_eq_sub I connection x regular hfield
      hfirst hsecond,
    covariantDerivativeTensorCovariantDerivativeAt_eq_secondDerivative I connection x regular
      hfield hdirection hfirst hsecond,
    covariantDerivativeTensorCovariantDerivativeAt_eq_secondDerivative I connection x regular
      hfield hdirection hsecond hfirst]

end

end RiemannianFluids
