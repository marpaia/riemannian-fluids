import RiemannianFluids.Reproductions.CC15.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CC15 numbered remarks -/

namespace RiemannianFluids

/-- Both numbered remarks in CC15, arXiv:1501.04928v1. -/
def cc15NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CC15" "arXiv:1501.04928v1" "Remark 1.2"
    #[.interpretation, .provenance]
    "Euclidean stationary solutions are smooth, and decay plus smoothness explains the boundedness hypothesis in the stated dimensions."
    .metadataOnly
    (affects := #[``RiemannianFluids.cc15_theorem_1_1]),
  literatureRemark "CC15" "arXiv:1501.04928v1" "Remark 2.6"
    #[.proofRoute, .limitation]
    "The higher-dimensional proof follows the two-dimensional route except that Hodge star no longer identifies two-forms with functions and the harmonic complement vanishes."
    .metadataOnly
    (affects := #[``RiemannianFluids.cc15_theorem_2_5_solenoidal_h1_decomposition])
]

end RiemannianFluids
