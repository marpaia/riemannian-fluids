import RiemannianFluids.Geometry.SpaceForms
import RiemannianFluids.Operators.Viscosity
import RiemannianFluids.PDE.LerayHopf

/-!
# CC13: Leray--Hopf nonuniqueness on the hyperbolic plane

The proposition below is the source-scoped target from Theorem 1.2.  It deliberately remains a
definition rather than a postulated theorem: M1 fixes the quantifiers, geometry, viscosity model,
common initial datum, and solution class; a later M4 theorem must inhabit this proposition.
-/

namespace RiemannianFluids.Literature.CC13

/-- Source signature for CC13 Theorem 1.2. -/
def leray_hopf_nonuniqueness_statement
    {Point Initial Solution : Type*}
    (geometry : RiemannianGeometryProfile Point)
    (framework : LerayHopfFramework Initial Solution)
    (viscosityModel : ViscosityModel) (a : ℝ) : Prop :=
  IsHyperbolicSpaceForm geometry 2 a →
    viscosityModel = ViscosityModel.deformation →
      ∃ initial solution₁ solution₂,
        IsLerayHopfSolution framework initial solution₁ ∧
          IsLerayHopfSolution framework initial solution₂ ∧
          solution₁ ≠ solution₂

end RiemannianFluids.Literature.CC13
