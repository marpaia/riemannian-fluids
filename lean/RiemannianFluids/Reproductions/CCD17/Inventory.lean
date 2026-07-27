import RiemannianFluids.Reproductions.CCD17.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CCD17 source inventory -/

namespace RiemannianFluids

def ccd17NamedResults : Array LiteratureItemRef := #[
  literatureItem "CCD17" "arXiv:1608.05114v2" "Theorem 3.2" .theorem
    ``RiemannianFluids.ccd17_theorem_3_2,
  literatureItem "CCD17" "arXiv:1608.05114v2" "Theorem 3.3" .theorem
    ``RiemannianFluids.ccd17_theorem_3_3,
  literatureItem "CCD17" "arXiv:1608.05114v2" "Theorem 3.6" .theorem
    ``RiemannianFluids.ccd17_theorem_3_6
]

/-- Numbered definitions in CCD17; populated separately when the source has any. -/
def ccd17NamedDefinitions : Array LiteratureItemRef := #[]

/-- Source-audited named-result count for CCD17. -/
theorem ccd17NamedResultCount : ccd17NamedResults.size = 3 := by
  native_decide

/-- Source-audited numbered-remark count for CCD17. -/
theorem ccd17NumberedRemarkCount : ccd17NumberedRemarks.size = 6 := by
  native_decide

end RiemannianFluids
