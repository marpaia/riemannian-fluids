import RiemannianFluids.Reproductions.CC21.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CC21 numbered remarks -/

namespace RiemannianFluids

/-- The sole numbered remark in CC21, arXiv:1708.05134v1. -/
def cc21NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CC21" "arXiv:1708.05134v1" "Remark 1.1"
    #[.mathematicalClaim, .specialization, .provenance]
    "In Euclidean space, both -Delta v + v = grad p and -Delta v = grad p have only trivial solutions."
    .statementPending
    (affects := #[``RiemannianFluids.cc21_theorem_1_2])
]

end RiemannianFluids
