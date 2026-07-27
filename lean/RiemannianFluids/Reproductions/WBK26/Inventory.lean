import RiemannianFluids.Reproductions.WBK26.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # WBK26 source inventory -/

namespace RiemannianFluids

def wbk26NamedResults : Array LiteratureItemRef := #[
  literatureItem "WBK26" "arXiv:2605.17502v2" "Theorem 6.1" .theorem
    ``RiemannianFluids.wbk26_theorem_6_1
]

/-- Numbered definitions in WBK26; populated separately when the source has any. -/
def wbk26NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for WBK26. -/
theorem wbk26NamedResultCount : wbk26NamedResults.size = 1 := by
  native_decide

/-- Source-audited numbered-remark count for WBK26. -/
theorem wbk26NumberedRemarkCount : wbk26NumberedRemarks.size = 3 := by
  native_decide

end RiemannianFluids
