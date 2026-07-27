import Mathlib.Algebra.Group.Defs

/-! # Ambient-to-intrinsic restriction of differential operators -/

namespace RiemannianFluids

/-- Pullback/restriction observables before a Gauss formula identifies correction terms. -/
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

end RiemannianFluids
