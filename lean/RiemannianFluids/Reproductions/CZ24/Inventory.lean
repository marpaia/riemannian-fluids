import RiemannianFluids.Reproductions.CZ24.Remarks
import RiemannianFluids.Reproductions.Inventory

/-! # CZ24 source inventory -/

namespace RiemannianFluids

/-- The CZ24 survey has no numbered theorem-like results. -/
def cz24NamedResults : Array LiteratureItemRef := #[]

/-- The CZ24 survey has no numbered definitions. -/
def cz24NamedDefinitions : Array LiteratureItemRef := #[]

/-- The CZ24 survey has no numbered theorem-like results. -/
theorem cz24NamedResultCount : cz24NamedResults.size = 0 := by
  native_decide

/-- The CZ24 survey has no numbered remarks. -/
theorem cz24NumberedRemarkCount : cz24NumberedRemarks.size = 0 := by
  native_decide

end RiemannianFluids
