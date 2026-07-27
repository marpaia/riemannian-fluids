import RiemannianFluids.Reproductions.CCY23.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CCY23 source inventory -/

namespace RiemannianFluids

def ccy23NamedResults : Array LiteratureItemRef := #[
  literatureItem "CCY23" "arXiv:2203.16050v1" "Theorem 1.1" .theorem
    ``RiemannianFluids.ccy23_theorem_1_1
]

/-- Numbered definitions in CCY23; populated separately when the source has any. -/
def ccy23NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for CCY23. -/
theorem ccy23NamedResultCount : ccy23NamedResults.size = 1 := by
  native_decide

/-- Source-audited numbered-remark count for CCY23. -/
theorem ccy23NumberedRemarkCount : ccy23NumberedRemarks.size = 2 := by
  native_decide

end RiemannianFluids
