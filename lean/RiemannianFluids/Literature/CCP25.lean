import RiemannianFluids.FunctionSpaces.HyperbolicCCP25
import RiemannianFluids.FunctionSpaces.HodgeDecomposition
import RiemannianFluids.Geometry.SpaceForms

/-!
# CCP25: Sobolev Hodge decomposition on noncompact space forms

The proved declaration below is the completed `N = 2`, `k = 1`, `a = 1` specialization.  The
arbitrary-dimension, degree, and curvature-scale theorem now has a separate source signature but
remains an open proof node.
-/

namespace RiemannianFluids.Literature.CCP25

/-- Source realization data for one degree of the general nonpositive-space-form theorem.
The four predicates in `hodge` denote the source `H¹` exact/coexact closures, its actual `L²`
harmonic sector, and the source `H¹` orthogonality relation. -/
structure SpaceFormH1HodgeData (Form : Type*) where
  geometry : RiemannianNonpositiveSpaceFormData
  degree : ℕ
  hodge : H1HodgeData Form

/-- Source signature for CCP25 Theorem 1.3 at arbitrary dimension, form degree, and curvature
scale (including the Euclidean case `a = 0`).  Universality is expressed by the arbitrary
`geometry`, `degree`, and concrete form carrier parameters of this declaration. -/
def h1_noncompact_decomposition_statement
    {Form : Type*} [AddCommGroup Form]
    (data : SpaceFormH1HodgeData Form) : Prop :=
  data.geometry.hasExpectedGeometry →
    data.degree ≤ data.geometry.dimension →
      HasH1HodgeDecomposition data.hodge

/-- The source-normalized `H¹` Hodge decomposition for one-forms on `H²(-1)`. -/
abbrev h2_oneForm_h1_decomposition :=
  _root_.RiemannianFluids.HyperbolicPlane.hyperbolicH1_exact_add_coexact_add_actualHarmonic

end RiemannianFluids.Literature.CCP25
