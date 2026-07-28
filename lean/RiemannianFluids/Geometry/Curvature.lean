import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Curvature tensors and contractions -/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Riemann, Ricci, scalar, and sectional curvature on actual Mathlib tangent fibers.  These
operations are repository scaffolding because the pinned Mathlib manifold API does not yet expose
their construction from a covariant derivative. -/
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
