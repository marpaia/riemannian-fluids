import RiemannianFluids.Geometry.Instances.HyperbolicPlaneCensus

/-!
# CZ24: viscosity-operator census

Stable, source-facing entry points for the claims indexed under `CZ24`.  The theorem below is the
concrete hyperbolic witness closing the survey's general inequivalence claim; its name records that
this is a witness, not a classification of all curved manifolds.
-/

namespace RiemannianFluids.Literature.CZ24

/-- A concrete hyperbolic witness for the pairwise inequivalence of the three viscosity outputs. -/
abbrev operator_census_hyperbolic_witness :=
  _root_.RiemannianFluids.HyperbolicPlane.cz24_census_hyperbolic

end RiemannianFluids.Literature.CZ24
