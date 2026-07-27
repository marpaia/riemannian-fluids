import RiemannianFluids.Reproductions.CC13.Core
import RiemannianFluids.Reproductions.Inventory

/-! # CC13 numbered remarks -/

namespace RiemannianFluids

/-- All five numbered remarks in CC13, arXiv:1006.2819v1. -/
def cc13NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "CC13" "arXiv:1006.2819v1" "Remark 1.3"
    #[.interpretation, .limitation, .openQuestion]
    "Leray--Hopf solutions may be an inadequate foundation on the hyperbolic plane; the three-dimensional case remains open."
    .metadataOnly
    (affects := #[``RiemannianFluids.cc13_theorem_1_2]),
  literatureRemark "CC13" "arXiv:1006.2819v1" "Remark 1.5"
    #[.proofRoute, .interpretation]
    "Corollaries 1.4 and 1.7 follow directly from their theorem constructions and do not use the delicate estimates."
    .metadataOnly
    (affects := #[``RiemannianFluids.cc13_corollary_1_4_hyperbolic_liouville_failure,
      ``RiemannianFluids.cc13_corollary_1_7_pinched_liouville_failure]),
  literatureRemark "CC13" "arXiv:1006.2819v1" "Remark 1.8"
    #[.hypothesisScope]
    "The pinching hypothesis b / 2 < a required by Theorem 1.6 is not required by Corollary 1.7."
    .formalized
    (affects := #[``RiemannianFluids.cc13_theorem_1_6_pinched_modified_nonuniqueness,
      ``RiemannianFluids.cc13_corollary_1_7_pinched_liouville_failure])
    (formalDeclarations := #[``RiemannianFluids.cc13_corollary_1_7_pinched_liouville_failure]),
  literatureRemark "CC13" "arXiv:1006.2819v1" "Remark 3.2"
    #[.convention]
    "The generic constant C0 may change from line to line but depends only on a, b, and the dimension."
    .metadataOnly,
  literatureRemark "CC13" "arXiv:1006.2819v1" "Remark 4.2"
    #[.interpretation]
    "Lemma 4.1 is the stated bounded-radius geodesic-ball covering of a sufficiently distant annulus."
    .metadataOnly
    (affects := #[``RiemannianFluids.cc13_lemma_4_1_covering])
]

end RiemannianFluids
