import RiemannianFluids.Reproductions.CC13.Inventory
import RiemannianFluids.Reproductions.CC15.Inventory
import RiemannianFluids.Reproductions.CC21.Inventory
import RiemannianFluids.Reproductions.CCD17.Inventory
import RiemannianFluids.Reproductions.CCF25.Inventory
import RiemannianFluids.Reproductions.CCG25.Inventory
import RiemannianFluids.Reproductions.CCP25.Inventory
import RiemannianFluids.Reproductions.CCY23.Inventory
import RiemannianFluids.Reproductions.CZ24.Inventory
import RiemannianFluids.Reproductions.WBK26.Inventory
import RiemannianFluids.Reproductions.WBS26.Inventory

/-!
# Lean-native literature inventory

This is the executable completeness boundary for the version-pinned paper corpus.  Each
paper package owns its named-item and numbered-remark inventories.  This module only
assembles those checked local inventories and proves corpus-wide cardinality, uniqueness,
classification, and coverage invariants.
-/

namespace RiemannianFluids

/-- All 104 numbered theorem-like source results, in corpus and source order. -/
def namedLiteratureResults : Array LiteratureItemRef :=
  ccd17NamedResults ++ ccy23NamedResults ++ ccg25NamedResults ++
    ccf25NamedResults ++ wbk26NamedResults ++ wbs26NamedResults ++
    cc13NamedResults ++ cc15NamedResults ++ cc21NamedResults ++ ccp25NamedResults

/-- All six explicitly numbered source definitions. -/
def namedLiteratureDefinitions : Array LiteratureItemRef :=
  ccd17NamedDefinitions ++ ccy23NamedDefinitions ++ ccg25NamedDefinitions ++
    ccf25NamedDefinitions ++ wbk26NamedDefinitions ++ wbs26NamedDefinitions ++
    cc13NamedDefinitions ++ cc15NamedDefinitions ++ cc21NamedDefinitions ++
    ccp25NamedDefinitions ++ cz24NamedDefinitions

/-- All 51 numbered remarks, including source packages with an empty remark list. -/
def numberedLiteratureRemarks : Array LiteratureRemarkRef :=
  ccd17NumberedRemarks ++ ccy23NumberedRemarks ++ ccg25NumberedRemarks ++
    ccf25NumberedRemarks ++ wbk26NumberedRemarks ++ wbs26NumberedRemarks ++
    cc13NumberedRemarks ++ cc15NumberedRemarks ++ cc21NumberedRemarks ++
    ccp25NumberedRemarks ++ cz24NumberedRemarks

/-- The theorem-like inventory has the source-audited cardinality 104. -/
theorem namedLiteratureResultCount : namedLiteratureResults.size = 104 := by
  native_decide

/-- The 104-result total decomposes into the four source result kinds. -/
theorem namedLiteratureResultKindCounts :
    (namedLiteratureResults.filter (fun item => item.kind == .theorem)).size = 38 ∧
    (namedLiteratureResults.filter (fun item => item.kind == .lemma)).size = 38 ∧
    (namedLiteratureResults.filter (fun item => item.kind == .proposition)).size = 9 ∧
    (namedLiteratureResults.filter (fun item => item.kind == .corollary)).size = 19 := by
  native_decide

/-- A paper ID and source label identify at most one named result. -/
theorem namedLiteratureResultKeysAreUnique :
    (namedLiteratureResults.map (fun item => item.paperId ++ ":" ++ item.label)).toList.Nodup := by
  native_decide

/-- Adding the six numbered definitions gives 110 mandatory named source nodes. -/
theorem mandatoryNamedLiteratureItemCount :
    (namedLiteratureResults ++ namedLiteratureDefinitions).size = 110 := by
  native_decide

/-- The pinned corpus contains exactly 51 numbered remarks. -/
theorem numberedLiteratureRemarkCount : numberedLiteratureRemarks.size = 51 := by
  native_decide

/-- Paper ID and source label uniquely identify every numbered remark. -/
theorem numberedLiteratureRemarkKeysAreUnique :
    (numberedLiteratureRemarks.map (fun item => item.paperId ++ ":" ++ item.label)).toList.Nodup := by
  native_decide

/-- Every remark has at least one explicit semantic role. -/
theorem numberedLiteratureRemarksAreClassified :
    numberedLiteratureRemarks.all (fun item => !item.roles.isEmpty) = true := by
  native_decide

/-- Current extraction status for the 51 source remark containers. -/
theorem numberedLiteratureRemarkCoverageCounts :
    (numberedLiteratureRemarks.filter (fun item => item.coverage == .formalized)).size = 5 ∧
    (numberedLiteratureRemarks.filter (fun item => item.coverage == .statementPending)).size = 27 ∧
    (numberedLiteratureRemarks.filter (fun item => item.coverage == .metadataOnly)).size = 19 := by
  native_decide

/-- No remark marked formalized is allowed to omit its checked Lean declaration. -/
theorem formalizedRemarksHaveDeclarations :
    (numberedLiteratureRemarks.filter (fun item => item.coverage == .formalized)).all
      (fun item => !item.formalDeclarations.isEmpty) = true := by
  native_decide

end RiemannianFluids
