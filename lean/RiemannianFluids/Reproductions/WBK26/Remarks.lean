import RiemannianFluids.Reproductions.WBK26.Core
import RiemannianFluids.Reproductions.Inventory

/-! # WBK26 numbered remarks -/

namespace RiemannianFluids

/-- All three numbered remarks in WBK26, arXiv:2605.17502v2. -/
def wbk26NumberedRemarks : Array LiteratureRemarkRef := #[
  literatureRemark "WBK26" "arXiv:2605.17502v2" "Remark 4.1"
    #[.mathematicalClaim, .interpretation]
    "The Lie-derivative strain rate is material-frame indifferent because adding a Killing field does not change it; vorticity lacks this invariance."
    .formalized
    (affects := #[``RiemannianFluids.wbk26_lie_strain_selection])
    (formalDeclarations := #[``RiemannianFluids.wbk26_metric_rate_is_twice_deformation]),
  literatureRemark "WBK26" "arXiv:2605.17502v2" "Remark 4.2"
    #[.provenance, .interpretation]
    "The individual kinematic and constitutive ingredients are classical; their assembly as a viscosity-selection principle is the claimed novelty."
    .metadataOnly
    (affects := #[``RiemannianFluids.wbk26_lie_strain_selection]),
  literatureRemark "WBK26" "arXiv:2605.17502v2" "Remark 6.2"
    #[.mathematicalClaim, .proofRoute]
    "The global weak solution is unique by the two-dimensional difference-energy estimate and Gronwall's lemma."
    .formalized
    (affects := #[``RiemannianFluids.wbk26_theorem_6_1])
    (formalDeclarations := #[``RiemannianFluids.wbk26_weak_solution_unique])
]

end RiemannianFluids
