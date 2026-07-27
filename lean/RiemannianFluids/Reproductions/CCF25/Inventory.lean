import RiemannianFluids.Reproductions.CCF25.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CCF25 source inventory -/

namespace RiemannianFluids

def ccf25NamedResults : Array LiteratureItemRef := #[
  literatureItem "CCF25" "arXiv:2511.10579v1" "Theorem 1.1" .theorem
    ``RiemannianFluids.ccf25_theorem_1_1,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Theorem 1.3" .theorem
    ``RiemannianFluids.ccf25_theorem_1_3,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Theorem 1.6" .theorem
    ``RiemannianFluids.ccf25_theorem_1_6_normal_hodge,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Theorem 1.9" .theorem
    ``RiemannianFluids.ccf25_theorem_1_9_geometric_boundary_conditions,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Proposition 3.1" .proposition
    ``RiemannianFluids.ccf25_proposition_3_1_navier_lie_bracket,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Proposition 3.2" .proposition
    ``RiemannianFluids.ccf25_proposition_3_2_hodge_lie_derivative,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Theorem 4.1" .theorem
    ``RiemannianFluids.ccf25_theorem_4_1_gauss_laplacian,
  literatureItem "CCF25" "arXiv:2511.10579v1" "Lemma 4.2" .lemma
    ``RiemannianFluids.ccf25_lemma_4_2_coefficient_identity
]

/-- Numbered definitions in CCF25; populated separately when the source has any. -/
def ccf25NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for CCF25. -/
theorem ccf25NamedResultCount : ccf25NamedResults.size = 8 := by
  native_decide

/-- Source-audited numbered-remark count for CCF25. -/
theorem ccf25NumberedRemarkCount : ccf25NumberedRemarks.size = 8 := by
  native_decide

end RiemannianFluids
