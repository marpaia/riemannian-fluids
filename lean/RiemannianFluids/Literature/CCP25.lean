import RiemannianFluids.FunctionSpaces.HyperbolicCCP25

/-!
# CCP25: Sobolev Hodge decomposition on noncompact space forms

The declaration below is the completed `N = 2`, `k = 1`, `a = 1` specialization.  The arbitrary
dimension, degree, and curvature-scale theorem remains a separate open corpus node.
-/

namespace RiemannianFluids.Literature.CCP25

/-- The source-normalized `H¹` Hodge decomposition for one-forms on `H²(-1)`. -/
abbrev h2_oneForm_h1_decomposition :=
  _root_.RiemannianFluids.HyperbolicPlane.hyperbolicH1_exact_add_coexact_add_actualHarmonic

end RiemannianFluids.Literature.CCP25
