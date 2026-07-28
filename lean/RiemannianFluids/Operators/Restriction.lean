import RiemannianFluids.Geometry.Submanifolds

/-! # Ambient-to-intrinsic restriction of differential operators -/

namespace RiemannianFluids

open Bundle
open scoped Bundle ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

/-- Tangential restriction of an actual ambient vector field along an immersion. -/
def tangentialRestriction
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientField : (y : N) → TangentSpace I' y) :
    (x : M) → TangentSpace I x :=
  fun x => splitting.tangentProjection x (ambientField (immersion.toFun x))

/-- An ambient field extends a tangent field when its restriction equals the immersed tangent
vector, before applying projection. -/
def ExtendsTangentField
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (ambientField : (y : N) → TangentSpace I' y)
    (surfaceField : (x : M) → TangentSpace I x) : Prop :=
  ∀ x,
    ambientField (immersion.toFun x) =
      mfderiv I I' immersion.toFun x (surfaceField x)

/-- Tangency of an ambient field along the immersed submanifold. -/
def IsTangentialAlongImmersion
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (ambientField : (y : N) → TangentSpace I' y) : Prop :=
  ∀ x, splitting.normalProjection x (ambientField (immersion.toFun x)) = 0

/-- A concrete ambient-to-intrinsic operator formula on Mathlib tangent fields. -/
def HasProjectedAmbientOperatorFormula
    (immersion : SmoothImmersionData (I := I) (I' := I') (M := M) (N := N))
    (splitting : SubmanifoldSplittingData immersion)
    (extension : ((x : M) → TangentSpace I x) → ((y : N) → TangentSpace I' y))
    (ambientOperator : ((y : N) → TangentSpace I' y) → ((y : N) → TangentSpace I' y))
    (intrinsicOperator correction :
      ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x)) : Prop :=
  ∀ field,
    tangentialRestriction immersion splitting (ambientOperator (extension field)) =
      fun x => intrinsicOperator field x + correction field x

/-- Carrier-polymorphic restriction observables retained for sources that state the problem
abstractly before choosing a manifold realization. -/
structure OperatorRestrictionData (AmbientField SurfaceField AmbientValue SurfaceValue : Type*) where
  extension : SurfaceField → AmbientField
  restrictValue : AmbientValue → SurfaceValue
  ambientOperator : AmbientField → AmbientValue
  intrinsicOperator : SurfaceField → SurfaceValue
  correction : SurfaceField → SurfaceValue

def HasOperatorRestrictionFormula
    {AmbientField SurfaceField AmbientValue SurfaceValue : Type*}
    [AddCommGroup SurfaceValue]
    (data : OperatorRestrictionData AmbientField SurfaceField AmbientValue SurfaceValue) : Prop :=
  ∀ field,
    data.restrictValue (data.ambientOperator (data.extension field)) =
      data.intrinsicOperator field + data.correction field

/-- The restriction formula is extension-independent on an admissible class. -/
def IsExtensionIndependent
    {AmbientField SurfaceField AmbientValue SurfaceValue : Type*}
    (restrictValue : AmbientValue → SurfaceValue)
    (ambientOperator : AmbientField → AmbientValue)
    (restrictsTo : AmbientField → SurfaceField → Prop)
    (admissible : AmbientField → Prop) : Prop :=
  ∀ field first second,
    restrictsTo first field → restrictsTo second field →
    admissible first → admissible second →
      restrictValue (ambientOperator first) = restrictValue (ambientOperator second)

end

end RiemannianFluids
