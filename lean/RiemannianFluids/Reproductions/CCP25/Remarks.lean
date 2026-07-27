import RiemannianFluids.Reproductions.CCP25.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CCP25 numbered remarks -/

namespace RiemannianFluids

/-- The sole numbered remark in CCP25, arXiv:1812.11764v1. -/
def ccp25NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CCP25" "arXiv:1812.11764v1" "Remark 2.8"
    #[.mathematicalClaim, .specialization]
    "For vector fields on Euclidean three-space, the integrated Weitzenbock identity reduces to the familiar curl--div decomposition."
    .statementPending
    (affects := #[``RiemannianFluids.ccp25_corollary_2_2_integrated_weizenbock])
]

end RiemannianFluids
