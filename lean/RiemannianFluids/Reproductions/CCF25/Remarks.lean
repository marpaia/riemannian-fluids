import RiemannianFluids.Reproductions.CCF25.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CCF25 numbered remarks -/

namespace RiemannianFluids

/-- All eight numbered remarks in CCF25, arXiv:2511.10579v1. -/
def ccf25NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.2"
    #[.mathematicalClaim, .equivalence, .interpretation]
    "The Navier scaling formula is the deformation Laplacian plus two curvature-coefficient terms, while the Hodge formula is the Hodge Laplacian plus a Lie-derivative correction."
    .statementPending
    (affects := #[``RiemannianFluids.ccf25_theorem_1_1,
      ``RiemannianFluids.ccf25_theorem_1_3]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.4"
    #[.hypothesisScope, .interpretation]
    "Theorem 1.1 follows the tangential-field assumptions used by rigorous averaging and asymptotic expansion, whereas Theorem 1.3 follows the Gauss-formula extension setup."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccf25_theorem_1_1,
      ``RiemannianFluids.ccf25_theorem_1_3]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.5"
    #[.mathematicalClaim, .specialization]
    "For the round sphere the coefficient c_13^3 vanishes, so the Navier formulas reduce to the deformation Laplacian and the Hodge formulas to the Hodge Laplacian."
    .formalized
    (affects := #[``RiemannianFluids.ccf25_theorem_1_1,
      ``RiemannianFluids.ccf25_theorem_1_3])
    (formalDeclarations := #[``RiemannianFluids.ccf25_remark_1_5_four_candidates_on_sphere]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.7"
    #[.hypothesisScope, .specialization, .provenance]
    "The heuristic normal-direction Hodge result agrees with the rigorous sphere result and is insensitive to the alternative tangency and divergence-free assumptions discussed for scaling."
    .statementPending
    (affects := #[``RiemannianFluids.ccf25_theorem_1_6_normal_hodge]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.8"
    #[.mathematicalClaim, .specialization]
    "The normal-direction calculation with the Navier boundary condition produces the deformation Laplacian."
    .formalized
    (formalDeclarations := #[``RiemannianFluids.ccf25_section_6_normal_navier]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.10"
    #[.convention, .proofRoute]
    "The boundary-condition assertions of Theorem 1.9 are made precise after the geometric notation is introduced."
    .metadataOnly
    (affects := #[``RiemannianFluids.ccf25_theorem_1_9_geometric_boundary_conditions]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 1.11"
    #[.mathematicalClaim, .hypothesisScope]
    "The geometric Navier statement extends to the Navier slip condition with a friction coefficient."
    .statementPending
    (affects := #[``RiemannianFluids.ccf25_theorem_1_9_geometric_boundary_conditions]),
  literatureRemark "CCF25" "arXiv:2511.10579v1" "Remark 3.3"
    #[.mathematicalClaim, .equivalence, .proofRoute]
    "The relation between Lie derivatives of a form and its metric-dual vector field gives an alternative derivation of the Navier boundary formula."
    .statementPending
    (affects := #[``RiemannianFluids.ccf25_proposition_3_1_navier_lie_bracket])
]

end RiemannianFluids
