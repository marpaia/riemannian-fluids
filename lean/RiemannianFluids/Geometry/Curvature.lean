import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Curvature tensors and contractions

The curvature convention used by the fluid operators is

`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.

Mathlib's pinned manifold API supplies bundled covariant derivatives and Lie brackets, but not a
fiberwise Riemann tensor or its Ricci contraction. This module therefore separates two layers:

* `connectionCurvatureAction` constructs the field-level commutator from an actual bundled
  connection. Its defining commutator identity and alternating law are proved below.
* `RiemannianCurvatureData` still records the fiberwise Riemann, Ricci, scalar, and sectional
  observables needed downstream. Deriving those contractions from the constructed commutator
  remains an explicit formalization milestone.

This boundary matters for the CCD17 program. The construction below fixes the curvature sign and
eliminates independent data for the three differentiated terms and their commutator, but it does
not yet prove tensoriality in the differentiated-field slot or the trace results needed for the
Weitzenbock identity. Tensoriality in the two direction slots is proved below under an explicit
local connection-regularity condition.
-/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Riemann, Ricci, scalar, and sectional curvature on actual Mathlib tangent fibers.

These contractions remain interface data because the pinned Mathlib manifold API does not yet
expose their construction from a covariant derivative. The field-level curvature commutator is
constructed separately by `connectionCurvatureAction` below. -/
structure RiemannianCurvatureData where
  riemann : ∀ x : M,
    TangentSpace I x → TangentSpace I x → TangentSpace I x → TangentSpace I x
  ricciAction : ∀ x : M, TangentSpace I x → TangentSpace I x
  scalarCurvature : M → ℝ
  sectionalCurvature : ∀ x : M, TangentSpace I x → TangentSpace I x → ℝ

/-- The curvature commutator convention on actual tangent fields. -/
structure RiemannianCurvatureCommutatorData where
  firstThenSecond :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)
  secondThenFirst :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)
  bracketDerivative :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)
  curvatureAction :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) →
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)

/-- `∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y]Z = R(X,Y)Z`. -/
def HasRiemannianCurvatureCommutator
    (data : RiemannianCurvatureCommutatorData (I := I) (M := M)) : Prop :=
  ∀ first second field x,
    data.firstThenSecond first second field x -
        data.secondThenFirst first second field x -
        data.bracketDerivative first second field x =
      data.curvatureAction first second field x

/-! ## Curvature commutator constructed from a connection -/

noncomputable section

/-- Covariant differentiation of `field` along `direction`, as a raw tangent field.

No regularity conclusion is asserted here. The bundled connection can act on raw sections; later
operator constructions attach the appropriate `C^k` hypotheses and derivative loss. -/
def covariantDerivativeAlong
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (direction field : (x : M) → TangentSpace I x) :
    (x : M) → TangentSpace I x :=
  fun x ↦ connection field x (direction x)

/-- The curvature action constructed from a bundled tangent connection.

The argument order follows the displayed convention: `first` is the outer direction in the first
term and `second` is the outer direction in the second term. -/
def connectionCurvatureAction
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (first second field : (x : M) → TangentSpace I x) :
    (x : M) → TangentSpace I x :=
  covariantDerivativeAlong I connection first
      (covariantDerivativeAlong I connection second field) -
    covariantDerivativeAlong I connection second
      (covariantDerivativeAlong I connection first field) -
    covariantDerivativeAlong I connection (VectorField.mlieBracket I first second) field

/-- Populate every term of the curvature-commutator interface from one bundled connection. -/
def connectionCurvatureCommutatorData
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    RiemannianCurvatureCommutatorData (I := I) (M := M) where
  firstThenSecond first second field :=
    covariantDerivativeAlong I connection first
      (covariantDerivativeAlong I connection second field)
  secondThenFirst first second field :=
    covariantDerivativeAlong I connection second
      (covariantDerivativeAlong I connection first field)
  bracketDerivative first second field :=
    covariantDerivativeAlong I connection (VectorField.mlieBracket I first second) field
  curvatureAction := connectionCurvatureAction I connection

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The connection-derived data satisfies the curvature commutator with no additional hypothesis. -/
theorem connectionCurvatureCommutatorData_hasCommutator
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    HasRiemannianCurvatureCommutator I
      (connectionCurvatureCommutatorData I connection) := by
  intro first second field x
  rfl

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Curvature is alternating in its two direction fields for every bundled connection. -/
theorem connectionCurvatureAction_swap
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (first second field : (x : M) → TangentSpace I x) :
    connectionCurvatureAction I connection first second field =
      -connectionCurvatureAction I connection second first field := by
  rw [connectionCurvatureAction, connectionCurvatureAction,
    VectorField.mlieBracket_swap]
  funext x
  simp only [covariantDerivativeAlong, Pi.sub_apply, Pi.neg_apply,
    ContinuousLinearMap.map_neg]
  module

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Applying curvature twice in the same direction gives zero. -/
@[simp]
theorem connectionCurvatureAction_self
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _))
    (direction field : (x : M) → TangentSpace I x) :
    connectionCurvatureAction I connection direction direction field = 0 := by
  rw [connectionCurvatureAction, VectorField.mlieBracket_self]
  funext x
  simp [covariantDerivativeAlong]

/-! ## Pointwise curvature in the two direction slots

The curvature commutator is second order in the differentiated field. To make its two direction
arguments pointwise, we need the local regularity statement that differentiating a `C²` field
along a differentiable direction produces a differentiable field. The pinned Mathlib API exposes
global connection regularity but not the local consequence needed by its tensoriality criterion,
so `HasConnectionCurvatureRegularityAt` records exactly that bridge.

Under this condition, the derivative terms created by multiplying either direction by a scalar
function cancel against the corresponding Lie-bracket product rule. The resulting
`connectionCurvatureDirectionsAt` is an actual continuous bilinear map on `T_xM`, not freely
supplied curvature data. Its remaining dependence on the `C²` field is intentional: proving
tensoriality in that third slot is the next geometric step toward the fiberwise Riemann tensor.
-/

section PointwiseDirections

variable [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]

/-- The local regularity needed to form curvature from two successive covariant derivatives.

For a differentiable direction `X` and a twice differentiable field `Z`, the once differentiated
field `∇_X Z` must itself be differentiable at `x`. -/
def HasConnectionCurvatureRegularityAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M) : Prop :=
  ∀ (direction field : (y : M) → TangentSpace I y),
    MDiffAt (T% direction) x → CMDiffAt 2 (T% field) x →
      MDiffAt (T% (covariantDerivativeAlong I connection direction field)) x

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The connection curvature action is tensorial in its first direction argument. -/
theorem connectionCurvatureAction_tensorial_first
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (second field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TensorialAt I E
      (fun first ↦ connectionCurvatureAction I connection first second field x) x where
  smul {f first} hf hfirst := by
    let derived := covariantDerivativeAlong I connection first field
    have hderived : MDiffAt (T% derived) x := regular first field hfirst hfield
    have hscaled :
        covariantDerivativeAlong I connection (f • first) field = f • derived := by
      funext y
      simp [covariantDerivativeAlong, derived]
    have houter :
        covariantDerivativeAlong I connection second (f • derived) x =
          f x • covariantDerivativeAlong I connection second derived x +
            d% f x (second x) • derived x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.leibniz hderived hf) (second x)
    have hfirstTerm :
        covariantDerivativeAlong I connection (f • first)
            (covariantDerivativeAlong I connection second field) x =
          f x • covariantDerivativeAlong I connection first
            (covariantDerivativeAlong I connection second field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I (f • first) second) field x =
          -(d% f x (second x)) • derived x +
            f x • covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_smul_left hf hfirst]
      simp [derived, covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction, hscaled]
    simp only [Pi.sub_apply]
    rw [hfirstTerm, houter, hbracket]
    simp only [derived]
    module
  add {first first'} hfirst hfirst' := by
    let derived := covariantDerivativeAlong I connection first field
    let derived' := covariantDerivativeAlong I connection first' field
    have hderived : MDiffAt (T% derived) x := regular first field hfirst hfield
    have hderived' : MDiffAt (T% derived') x := regular first' field hfirst' hfield
    have hadd :
        covariantDerivativeAlong I connection (first + first') field = derived + derived' := by
      funext y
      simp [covariantDerivativeAlong, derived, derived']
    have houter :
        covariantDerivativeAlong I connection second (derived + derived') x =
          covariantDerivativeAlong I connection second derived x +
            covariantDerivativeAlong I connection second derived' x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.add hderived hderived') (second x)
    have hfirstTerm :
        covariantDerivativeAlong I connection (first + first')
            (covariantDerivativeAlong I connection second field) x =
          covariantDerivativeAlong I connection first
              (covariantDerivativeAlong I connection second field) x +
            covariantDerivativeAlong I connection first'
              (covariantDerivativeAlong I connection second field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I (first + first') second) field x =
          covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x +
            covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first' second) field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_add_left hfirst hfirst']
      simp [covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction,
      connectionCurvatureAction, hadd]
    simp only [Pi.sub_apply]
    rw [hfirstTerm, houter, hbracket]
    simp only [derived, derived']
    module

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The connection curvature action is tensorial in its second direction argument. -/
theorem connectionCurvatureAction_tensorial_second
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (first field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TensorialAt I E
      (fun second ↦ connectionCurvatureAction I connection first second field x) x where
  smul {f second} hf hsecond := by
    let derived := covariantDerivativeAlong I connection second field
    have hderived : MDiffAt (T% derived) x := regular second field hsecond hfield
    have hscaled :
        covariantDerivativeAlong I connection (f • second) field = f • derived := by
      funext y
      simp [covariantDerivativeAlong, derived]
    have houter :
        covariantDerivativeAlong I connection first (f • derived) x =
          f x • covariantDerivativeAlong I connection first derived x +
            d% f x (first x) • derived x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.leibniz hderived hf) (first x)
    have hsecondTerm :
        covariantDerivativeAlong I connection (f • second)
            (covariantDerivativeAlong I connection first field) x =
          f x • covariantDerivativeAlong I connection second
            (covariantDerivativeAlong I connection first field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I first (f • second)) field x =
          d% f x (first x) • derived x +
            f x • covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_smul_right hf hsecond]
      simp [derived, covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction, hscaled]
    simp only [Pi.sub_apply]
    rw [houter, hsecondTerm, hbracket]
    simp only [derived]
    module
  add {second second'} hsecond hsecond' := by
    let derived := covariantDerivativeAlong I connection second field
    let derived' := covariantDerivativeAlong I connection second' field
    have hderived : MDiffAt (T% derived) x := regular second field hsecond hfield
    have hderived' : MDiffAt (T% derived') x := regular second' field hsecond' hfield
    have hadd :
        covariantDerivativeAlong I connection (second + second') field = derived + derived' := by
      funext y
      simp [covariantDerivativeAlong, derived, derived']
    have houter :
        covariantDerivativeAlong I connection first (derived + derived') x =
          covariantDerivativeAlong I connection first derived x +
            covariantDerivativeAlong I connection first derived' x := by
      exact DFunLike.congr_fun
        (connection.isCovariantDerivativeOn.add hderived hderived') (first x)
    have hsecondTerm :
        covariantDerivativeAlong I connection (second + second')
            (covariantDerivativeAlong I connection first field) x =
          covariantDerivativeAlong I connection second
              (covariantDerivativeAlong I connection first field) x +
            covariantDerivativeAlong I connection second'
              (covariantDerivativeAlong I connection first field) x := by
      simp [covariantDerivativeAlong]
    have hbracket :
        covariantDerivativeAlong I connection
            (VectorField.mlieBracket I first (second + second')) field x =
          covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second) field x +
            covariantDerivativeAlong I connection
              (VectorField.mlieBracket I first second') field x := by
      rw [covariantDerivativeAlong, VectorField.mlieBracket_add_right hsecond hsecond']
      simp [covariantDerivativeAlong]
    rw [connectionCurvatureAction, connectionCurvatureAction,
      connectionCurvatureAction, hadd]
    simp only [Pi.sub_apply]
    rw [houter, hsecondTerm, hbracket]
    simp only [derived, derived']
    module

/-- The curvature action as a continuous bilinear map in the two tangent directions at `x`.

Evaluating this map on `X(x)` and `Y(x)` recovers the connection commutator for any differentiable
extensions `X` and `Y`; see `connectionCurvatureDirectionsAt_apply`. -/
def connectionCurvatureDirectionsAt
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂
    (fun first second ↦ connectionCurvatureAction I connection first second field x) x
    (fun second _ ↦
      connectionCurvatureAction_tensorial_first I connection x regular second field hfield)
    (fun first _ ↦
      connectionCurvatureAction_tensorial_second I connection x regular first field hfield)

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- Applying the pointwise direction map recovers the field-level connection commutator. -/
theorem connectionCurvatureDirectionsAt_apply
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    {first second : (y : M) → TangentSpace I y}
    (hfirst : MDiffAt (T% first) x) (hsecond : MDiffAt (T% second) x) :
    connectionCurvatureDirectionsAt I connection x regular field hfield
        (first x) (second x) =
      connectionCurvatureAction I connection first second field x := by
  apply TensorialAt.mkHom₂_apply
  exacts [hfirst, hsecond]

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The pointwise direction map is alternating. -/
theorem connectionCurvatureDirectionsAt_swap
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    (first second : TangentSpace I x) :
    connectionCurvatureDirectionsAt I connection x regular field hfield first second =
      -connectionCurvatureDirectionsAt I connection x regular field hfield second first := by
  rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend,
    TensorialAt.mkHom₂_apply_eq_extend]
  exact congrFun
    (connectionCurvatureAction_swap I connection
      (FiberBundle.extend E first) (FiberBundle.extend E second) field) x

omit [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The pointwise direction map vanishes on a repeated direction. -/
@[simp]
theorem connectionCurvatureDirectionsAt_self
    (connection : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (regular : HasConnectionCurvatureRegularityAt I connection x)
    (field : (y : M) → TangentSpace I y)
    (hfield : CMDiffAt 2 (T% field) x)
    (direction : TangentSpace I x) :
    connectionCurvatureDirectionsAt I connection x regular field hfield direction direction = 0 := by
  rw [connectionCurvatureDirectionsAt, TensorialAt.mkHom₂_apply_eq_extend]
  exact congrFun
    (connectionCurvatureAction_self I connection (FiberBundle.extend E direction) field) x

end PointwiseDirections

end

/-- Constant sectional curvature on all nondegenerate tangent two-planes. -/
def HasRiemannianConstantSectionalCurvature
    (data : RiemannianCurvatureData (I := I) (M := M)) (curvature : ℝ) : Prop :=
  ∀ x first second,
    LinearIndependent ℝ ![first, second] →
      data.sectionalCurvature x first second = curvature

/-- Pointwise pinching `-b² ≤ K_M ≤ -a²` on every nondegenerate tangent two-plane.

Unlike `HasPinchedNegativeCurvature` in `Geometry.SpaceForms`, this declaration is tied
to Mathlib's actual dependent tangent fibers.  The weaker profile-level version remains
useful for source statements which have not yet selected a concrete manifold model. -/
def HasRiemannianPinchedSectionalCurvature
    (data : RiemannianCurvatureData (I := I) (M := M)) (a b : ℝ) : Prop :=
  0 < a ∧ a ≤ b ∧
    ∀ x first second,
      LinearIndependent ℝ ![first, second] →
        -(b ^ 2) ≤ data.sectionalCurvature x first second ∧
          data.sectionalCurvature x first second ≤ -(a ^ 2)

/-- A pointwise lower bound for the quadratic form of the Ricci endomorphism.

The metric pairing is supplied explicitly because the curvature package records the Ricci
endomorphism while Mathlib owns the tangent fibers and their inner products. -/
def HasRiemannianRicciLowerBound
    (data : RiemannianCurvatureData (I := I) (M := M)) (bound : ℝ) : Prop :=
  ∀ x vector,
    bound * ‖vector‖ ^ 2 ≤ inner ℝ (data.ricciAction x vector) vector

/-- A pointwise upper bound for the quadratic form of the Ricci endomorphism. -/
def HasRiemannianRicciUpperBound
    (data : RiemannianCurvatureData (I := I) (M := M)) (bound : ℝ) : Prop :=
  ∀ x vector,
    inner ℝ (data.ricciAction x vector) vector ≤ bound * ‖vector‖ ^ 2

/-- In intrinsic dimension two, Ricci is Gaussian curvature times the identity. -/
def HasRiemannianSurfaceRicciIdentity
    (data : RiemannianCurvatureData (I := I) (M := M))
    (gaussianCurvature : M → ℝ) : Prop :=
  ∀ x vector,
    data.ricciAction x vector = gaussianCurvature x • vector

/-- Carrier-polymorphic curvature observables retained for source statements made before a
concrete manifold realization is selected. -/
structure CurvatureData (Vector : Type*) where
  riemann : Vector → Vector → Vector → Vector
  ricciAction : Vector → Vector
  scalarCurvature : ℝ
  sectionalCurvature : Vector → Vector → ℝ

/-- The curvature commutator convention used in CCD17 and CCG25. -/
structure CurvatureCommutatorData (Derivative Vector : Type*) where
  firstThenSecond : Vector → Vector → Vector → Derivative
  secondThenFirst : Vector → Vector → Vector → Derivative
  bracketDerivative : Vector → Vector → Vector → Derivative
  curvatureAction : Vector → Vector → Vector → Derivative

def HasCurvatureCommutator
    {Derivative Vector : Type*} [AddCommGroup Derivative]
    (data : CurvatureCommutatorData Derivative Vector) : Prop :=
  ∀ X Y Z,
    data.firstThenSecond X Y Z - data.secondThenFirst X Y Z -
        data.bracketDerivative X Y Z = data.curvatureAction X Y Z

/-- Constant sectional curvature `K` in arbitrary dimension. -/
def HasConstantSectionalCurvature
    {Vector : Type*} (data : CurvatureData Vector) (K : ℝ) : Prop :=
  ∀ X Y, data.sectionalCurvature X Y = K

/-- In dimension two, the Ricci endomorphism is multiplication by Gaussian curvature. -/
structure SurfaceRicciData (Vector : Type*) where
  gaussianCurvature : ℝ
  ricciAction : Vector → Vector

def HasSurfaceRicciIdentity
    {Vector : Type*} [AddCommGroup Vector] [Module ℝ Vector]
    (data : SurfaceRicciData Vector) : Prop :=
  ∀ vector, data.ricciAction vector = data.gaussianCurvature • vector

end RiemannianFluids
