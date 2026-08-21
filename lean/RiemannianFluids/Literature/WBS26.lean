import RiemannianFluids.Viscosity.BoundarySelection

/-!
# WBS26: wall-selected thin-shell viscosity

Only the convention and endpoint crosswalk is source-facing here.  Mosco convergence and the
operator-convergence package remain open and therefore have no theorem aliases in this module.
-/

namespace RiemannianFluids.Literature.WBS26

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Translation of the paper's signed local interpolating family to analysis-positive convention. -/
abbrev local_interpolating_family_analysisPositive
    (signedDeformation ricci shapeSquare : V →ₗ[ℝ] V) (a : ℝ) :=
  _root_.RiemannianFluids.wbs26_analysisPositive_crosswalk
    signedDeformation ricci shapeSquare a

end RiemannianFluids.Literature.WBS26
