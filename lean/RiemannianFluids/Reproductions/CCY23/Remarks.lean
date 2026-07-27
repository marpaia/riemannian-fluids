import RiemannianFluids.Reproductions.CCY23.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CCY23 numbered remarks -/

namespace RiemannianFluids

/-- Both numbered remarks in CCY23, arXiv:2203.16050v1. -/
def ccy23NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CCY23" "arXiv:2203.16050v1" "Remark 1.2"
    #[.mathematicalClaim, .equivalence, .convention]
    "For divergence-free fields, twice Def-star-Def equals the Hodge Laplacian minus twice the Ricci operator."
    .statementPending
    (affects := #[``RiemannianFluids.ccy23_theorem_1_1]),
  literatureRemark "CCY23" "arXiv:2203.16050v1" "Remark 1.3"
    #[.mathematicalClaim, .specialization]
    "The ellipsoid restriction formula reduces to the previously obtained sphere formula when the ellipsoid is round."
    .statementPending
    (affects := #[``RiemannianFluids.ccy23_theorem_1_1])
]

end RiemannianFluids
