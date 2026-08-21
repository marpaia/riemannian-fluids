import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import RiemannianFluids.Geometry.Curvature

/-!
# The second covariant derivative of a vector field

One covariant derivative of a vector field `u` produces the endomorphism-valued field
`X ↦ ∇_X u`. Differentiating again does not simply iterate the connection: the outer derivative
must also account for how the inner direction was transported. The correct second covariant
derivative is

    ∇²u(X,Y) = ∇_X(∇_Y u) - ∇_{∇_X Y} u.

The correction term is exactly what makes the result tensorial in both direction slots, so that
`∇²u(X,Y)(x)` depends only on the tangent vectors `X(x)` and `Y(x)`. Tensoriality in `X` is pure
fiberwise linearity of the bundled connection. Tensoriality in `Y` is a Leibniz cancellation:
scaling `Y` by a function `f` creates the derivative term `(Xf)∇_Y u` inside `∇_X(∇_{fY}u)`,
and the same term reappears inside `∇_{∇_X(fY)}u` with the same sign, so the difference is
tensorial. That cancellation is the entire geometric content of the definition.

The tensorial packaging follows the curvature construction in `Geometry.Curvature`: the same
local regularity bridge `HasConnectionCurvatureRegularityAt` makes the once-differentiated field
`∇_Y u` differentiable, and `TensorialAt.mkHom₂` turns the two-slot operation into an actual
continuous bilinear map `secondCovariantDerivativeAt` on `T_xM`.

## Ricci commutation

The antisymmetric part of `∇²u` is curvature. Expanding both orders of differentiation,

    ∇²u(X,Y) - ∇²u(Y,X) = ∇_X∇_Yu - ∇_Y∇_Xu - ∇_{∇_XY - ∇_YX}u,

and for a torsion-free connection `∇_XY - ∇_YX = [X,Y]`, so the right side is literally the
curvature commutator `R(X,Y)u` of `connectionCurvatureAction`. This commutation identity is what
converts the mixed trace of `∇²u` into a Ricci contraction in the CCD17 operator comparison; it
is proved here at the raw-field level and at the pointwise-tensor level. Torsion-freeness enters
as an explicit hypothesis, never silently.
-/

namespace RiemannianFluids

open Bundle Filter
open scoped Bundle ContDiff Manifold Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

noncomputable section

/-- The second covariant derivative `∇²u(X,Y) = ∇_X(∇_Y u) - ∇_{∇_X Y} u` on raw tangent
fields.

The subtracted term differentiates `u` along the field `∇_X Y`, which is what makes both
direction slots tensorial. No regularity is asserted by the definition itself; each theorem
below attaches the exact differentiability it consumes. -/
def secondCovariantDerivativeAlong
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (first second field : (x : M) → TangentSpace I x) :
    (x : M) → TangentSpace I x :=
  covariantDerivativeAlong I connection first
      (covariantDerivativeAlong I connection second field) -
    covariantDerivativeAlong I connection
      (covariantDerivativeAlong I connection first second) field

/-- Pointwise unfolding of the second covariant derivative through the bundled connection. -/
theorem secondCovariantDerivativeAlong_apply
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (first second field : (x : M) → TangentSpace I x) (x : M) :
    secondCovariantDerivativeAlong I connection first second field x =
      connection (covariantDerivativeAlong I connection second field) x (first x) -
        connection field x (connection second x (first x)) :=
  rfl

section PointwiseDirections

variable [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The second covariant derivative is tensorial in its outer direction.

Both occurrences of `first` sit in the direction argument of a fiberwise continuous linear map,
so no differentiability of any field is required. -/
theorem secondCovariantDerivativeAlong_tensorial_first
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (second field : (y : M) → TangentSpace I y) :
    TensorialAt I E
      (fun first ↦ secondCovariantDerivativeAlong I connection first second field x) x where
  smul {f first} _ _ := by
    show connection (covariantDerivativeAlong I connection second field) x (f x • first x) -
        connection field x (connection second x (f x • first x)) =
      f x • (connection (covariantDerivativeAlong I connection second field) x (first x) -
        connection field x (connection second x (first x)))
    rw [map_smul, map_smul, map_smul, smul_sub]
  add {first first'} _ _ := by
    show connection (covariantDerivativeAlong I connection second field) x
          (first x + first' x) -
        connection field x (connection second x (first x + first' x)) =
      connection (covariantDerivativeAlong I connection second field) x (first x) -
          connection field x (connection second x (first x)) +
        (connection (covariantDerivativeAlong I connection second field) x (first' x) -
          connection field x (connection second x (first' x)))
    rw [map_add, map_add, map_add]
    abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The second covariant derivative is tensorial in its inner direction.

Scaling the inner direction by `f` produces the Leibniz term `(df)(X)·∇_Y u` in the outer
derivative and the identical term inside `∇_{∇_X(fY)}u`; the two cancel. The regularity bridge
supplies differentiability of the once-differentiated field so the outer Leibniz rule applies. -/
theorem secondCovariantDerivativeAlong_tensorial_second
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TensorialAt I E
      (fun second ↦ secondCovariantDerivativeAlong I connection first second field x) x where
  smul {f second} hf hsecond := by
    let derived := covariantDerivativeAlong I connection second field
    have hderived : MDiffAt (T% derived) x := regular second field hsecond hfield
    -- Scaling the inner direction scales the once-differentiated field pointwise.
    have hscaled :
        covariantDerivativeAlong I connection (f • second) field = f • derived := by
      funext y
      simp [covariantDerivativeAlong, derived]
    -- Outer Leibniz rule on the scaled once-differentiated field.
    have houter :
        connection ((f : M → ℝ) • derived) x (first x) =
          f x • connection derived x (first x) + d% f x (first x) • derived x := by
      exact DFunLike.congr_fun (connection.isCovariantDerivativeOn.leibniz hderived hf) (first x)
    -- Inner Leibniz rule on the direction being transported.
    have hdirection :
        connection (f • second) x (first x) =
          f x • connection second x (first x) + d% f x (first x) • second x := by
      exact DFunLike.congr_fun (connection.isCovariantDerivativeOn.leibniz hsecond hf) (first x)
    simp only [secondCovariantDerivativeAlong, Pi.sub_apply]
    show connection (covariantDerivativeAlong I connection (f • second) field) x (first x) -
        connection field x (connection (f • second) x (first x)) = _
    rw [hscaled, houter, hdirection, map_add, map_smul, map_smul]
    show _ = f x • (connection derived x (first x) - connection field x (connection second x (first x)))
    have hvalue : derived x = connection field x (second x) := rfl
    rw [hvalue]
    module
  add {second second'} hsecond hsecond' := by
    let derived := covariantDerivativeAlong I connection second field
    let derived' := covariantDerivativeAlong I connection second' field
    have hderived : MDiffAt (T% derived) x := regular second field hsecond hfield
    have hderived' : MDiffAt (T% derived') x := regular second' field hsecond' hfield
    have hsum :
        covariantDerivativeAlong I connection (second + second') field = derived + derived' := by
      funext y
      simp [covariantDerivativeAlong, derived, derived']
    have houter :
        connection (derived + derived') x (first x) =
          connection derived x (first x) + connection derived' x (first x) := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.add hderived hderived') (first x)
    have hdirection :
        connection (second + second') x (first x) =
          connection second x (first x) + connection second' x (first x) := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.add hsecond hsecond') (first x)
    simp only [secondCovariantDerivativeAlong, Pi.sub_apply]
    show connection (covariantDerivativeAlong I connection (second + second') field) x (first x) -
        connection field x (connection (second + second') x (first x)) = _
    rw [hsum, houter, hdirection, map_add]
    show _ = connection derived x (first x) -
        connection field x (connection second x (first x)) +
      (connection derived' x (first x) -
        connection field x (connection second' x (first x)))
    module

/-- The second covariant derivative as a continuous bilinear map on `T_xM`.

Evaluating on `X(x)` and `Y(x)` recovers the raw-field operation for any differentiable
extensions; see `secondCovariantDerivativeAt_apply`. -/
def secondCovariantDerivativeAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂
    (fun first second ↦ secondCovariantDerivativeAlong I connection first second field x) x
    (fun second _ ↦
      secondCovariantDerivativeAlong_tensorial_first I connection x second field)
    (fun first _ ↦
      secondCovariantDerivativeAlong_tensorial_second I connection x regular first field hfield)

omit [CompleteSpace E] in
/-- Applying the pointwise bilinear map recovers the field-level second covariant derivative. -/
theorem secondCovariantDerivativeAt_apply
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    {first second : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    secondCovariantDerivativeAt I connection x regular field hfield (first x) (second x) =
      secondCovariantDerivativeAlong I connection first second field x := by
  apply TensorialAt.mkHom₂_apply
  exacts [hfirst, hsecond]

omit [CompleteSpace E] in
/-- Evaluating the pointwise bilinear map on tangent vectors uses their canonical extensions. -/
theorem secondCovariantDerivativeAt_apply_extend
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    (first second : TangentSpace I x) :
    secondCovariantDerivativeAt I connection x regular field hfield first second =
      secondCovariantDerivativeAlong I connection
        (FiberBundle.extend E first) (FiberBundle.extend E second) field x :=
  rfl

/-! ## Ricci commutation -/

/-- Ricci commutation on raw fields: for a torsion-free connection,

`∇²u(X,Y) - ∇²u(Y,X) = R(X,Y)u`.

The difference of the two second derivatives is
`∇_X∇_Yu - ∇_Y∇_Xu - ∇_{∇_XY - ∇_YX}u`, and vanishing torsion identifies `∇_XY - ∇_YX` with
the Lie bracket, which is exactly the commutator defining `connectionCurvatureAction`. Only one
derivative of each direction field at the base point is needed; the differentiated field enters
purely algebraically. -/
theorem secondCovariantDerivativeAlong_sub_swap
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htorsion : connection.torsion = 0)
    {first second : (y : M) → TangentSpace I y} (field : (y : M) → TangentSpace I y) {x : M}
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    secondCovariantDerivativeAlong I connection first second field x -
        secondCovariantDerivativeAlong I connection second first field x =
      connectionCurvatureAction I connection first second field x := by
  -- Torsion-freeness in bracket form: `∇_XY - ∇_YX = [X,Y]` at `x`.
  have hbracket : VectorField.mlieBracket I first second x =
      connection second x (first x) - connection first x (second x) :=
    (connection.torsion_eq_zero_iff.mp htorsion hfirst hsecond).symm
  simp only [secondCovariantDerivativeAlong, connectionCurvatureAction, Pi.sub_apply]
  show connection (covariantDerivativeAlong I connection second field) x (first x) -
      connection field x (connection second x (first x)) -
      (connection (covariantDerivativeAlong I connection first field) x (second x) -
        connection field x (connection first x (second x))) =
    connection (covariantDerivativeAlong I connection second field) x (first x) -
      connection (covariantDerivativeAlong I connection first field) x (second x) -
      connection field x (VectorField.mlieBracket I first second x)
  rw [hbracket, map_sub]
  abel

/-- Ricci commutation at the pointwise-tensor level: the antisymmetric part of the bilinear
`secondCovariantDerivativeAt` is the connection curvature tensor applied to `u(x)`. -/
theorem secondCovariantDerivativeAt_sub_swap
    [IsManifold I 3 M] [RiemannianBundle (TangentSpace I : M → Type _)]
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (htorsion : connection.torsion = 0)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    (first second : TangentSpace I x) :
    secondCovariantDerivativeAt I connection x regular field hfield first second -
        secondCovariantDerivativeAt I connection x regular field hfield second first =
      connectionCurvatureTensorAt I connection x regular first second (field x) := by
  have hfirst : MDiffAt (T% (FiberBundle.extend E first)) x :=
    FiberBundle.mdifferentiableAt_extend ..
  have hsecond : MDiffAt (T% (FiberBundle.extend E second)) x :=
    FiberBundle.mdifferentiableAt_extend ..
  rw [secondCovariantDerivativeAt_apply_extend, secondCovariantDerivativeAt_apply_extend,
    secondCovariantDerivativeAlong_sub_swap I connection htorsion field hfirst hsecond,
    ← connectionCurvatureTensorAt_apply I connection x regular hfirst hsecond hfield]
  simp

end PointwiseDirections

end

end RiemannianFluids
