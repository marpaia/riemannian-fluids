import RiemannianFluids.Reproductions.WBS26.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # WBS26 source inventory -/

namespace RiemannianFluids

def wbs26NamedResults : Array LiteratureItemRef := #[
  literatureItem "WBS26" "arXiv:2605.20589v3" "Lemma 3.1" .lemma
    ``RiemannianFluids.wbs26_lemma_3_1_wall_reduction,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Proposition 3.2" .proposition
    ``RiemannianFluids.wbs26_proposition_3_2_profile_terminal,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Theorem 3.3" .theorem
    ``RiemannianFluids.wbs26_theorem_3_3_formal_selection,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Theorem 4.1" .theorem
    ``RiemannianFluids.wbs26_theorem_4_1_uniform_korn,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Lemma 4.2" .lemma
    ``RiemannianFluids.wbs26_lemma_4_2_uniform_gaffney,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Theorem 4.3" .theorem
    ``RiemannianFluids.wbs26_theorem_4_3_exact_limit_densities,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Theorem 4.4" .theorem
    ``RiemannianFluids.wbs26_theorem_4_4_ricci_shift,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Theorem 4.5" .theorem
    ``RiemannianFluids.wbs26_theorem_4_5,
  literatureItem "WBS26" "arXiv:2605.20589v3" "Corollary 4.6" .corollary
    ``RiemannianFluids.wbs26_corollary_4_6
]

/-- Numbered definitions in WBS26; populated separately when the source has any. -/
def wbs26NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for WBS26. -/
theorem wbs26NamedResultCount : wbs26NamedResults.size = 9 := by
  native_decide

/-- Source-audited numbered-remark count for WBS26. -/
theorem wbs26NumberedRemarkCount : wbs26NumberedRemarks.size = 0 := by
  native_decide

end RiemannianFluids
