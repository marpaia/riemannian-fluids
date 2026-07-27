import RiemannianFluids.Reproductions.CC15.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CC15 source inventory -/

namespace RiemannianFluids

def cc15NamedResults : Array LiteratureItemRef := #[
  literatureItem "CC15" "arXiv:1501.04928v1" "Theorem 1.1" .theorem
    ``RiemannianFluids.cc15_theorem_1_1,
  literatureItem "CC15" "arXiv:1501.04928v1" "Corollary 1.3" .corollary
    ``RiemannianFluids.cc15_corollary_1_3_alternative_viscosities,
  literatureItem "CC15" "arXiv:1501.04928v1" "Lemma 2.1" .lemma
    ``RiemannianFluids.cc15_lemma_2_1_from_dirichlet_to_l2,
  literatureItem "CC15" "arXiv:1501.04928v1" "Lemma 2.2" .lemma
    ``RiemannianFluids.cc15_lemma_2_2_deformation_identity,
  literatureItem "CC15" "arXiv:1501.04928v1" "Lemma 2.3" .lemma
    ``RiemannianFluids.cc15_lemma_2_3_interpolation,
  literatureItem "CC15" "arXiv:1501.04928v1" "Lemma 2.4" .lemma
    ``RiemannianFluids.cc15_lemma_2_4_current_criterion,
  literatureItem "CC15" "arXiv:1501.04928v1" "Theorem 2.5" .theorem
    ``RiemannianFluids.cc15_theorem_2_5_solenoidal_h1_decomposition,
  literatureItem "CC15" "arXiv:1501.04928v1" "Corollary 4.1" .corollary
    ``RiemannianFluids.cc15_corollary_4_1_negative_ricci_l2_control,
  literatureItem "CC15" "arXiv:1501.04928v1" "Corollary 4.2" .corollary
    ``RiemannianFluids.cc15_corollary_4_2_negative_ricci_deformation_inequality
]

/-- Numbered definitions in CC15; populated separately when the source has any. -/
def cc15NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for CC15. -/
theorem cc15NamedResultCount : cc15NamedResults.size = 9 := by
  native_decide

/-- Source-audited numbered-remark count for CC15. -/
theorem cc15NumberedRemarkCount : cc15NumberedRemarks.size = 2 := by
  native_decide

end RiemannianFluids
