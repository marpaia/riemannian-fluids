/-!
# Source inventory types

Common Lean-native locators for the version-pinned literature corpus.  Paper packages
use these records for both named source items and numbered remarks.  A remark may affect
several declarations and may contain zero, one, or several formal statements.
-/

namespace RiemannianFluids

/-- The kinds of numbered mathematical source items represented by the formal graph. -/
inductive LiteratureItemKind where
  | theorem
  | lemma
  | proposition
  | corollary
  | definition
  deriving DecidableEq, BEq, Repr

/-- A source locator whose `declaration` is checked by Lean name resolution. -/
structure LiteratureItemRef where
  paperId : String
  sourceVersion : String
  label : String
  kind : LiteratureItemKind
  declaration : Lean.Name
  deriving Repr

/-- Construct a checked locator for a named source item. -/
def literatureItem
    (paperId sourceVersion label : String)
    (kind : LiteratureItemKind) (declaration : Lean.Name) : LiteratureItemRef :=
  { paperId, sourceVersion, label, kind, declaration }

/-- Semantic roles played by numbered remarks in the pinned papers. -/
inductive LiteratureRemarkRole where
  | mathematicalClaim
  | specialization
  | equivalence
  | hypothesisScope
  | convention
  | proofRoute
  | interpretation
  | provenance
  | limitation
  | openQuestion
  deriving DecidableEq, BEq, Repr

/-- Honest status of the formal content extracted from a numbered remark. -/
inductive LiteratureRemarkCoverage where
  | formalized
  | statementPending
  | metadataOnly
  deriving DecidableEq, BEq, Repr

/--
A numbered remark as a source container.  `affects` points to named declarations whose
scope or interpretation the remark changes.  `formalDeclarations` points only to Lean
declarations that state the remark's own mathematical atoms.
-/
structure LiteratureRemarkRef where
  paperId : String
  sourceVersion : String
  label : String
  roles : Array LiteratureRemarkRole
  summary : String
  affects : Array Lean.Name := #[]
  formalDeclarations : Array Lean.Name := #[]
  coverage : LiteratureRemarkCoverage
  deriving Repr

/-- Construct a source-ordered numbered-remark locator. -/
def literatureRemark
    (paperId sourceVersion label : String)
    (roles : Array LiteratureRemarkRole)
    (summary : String)
    (coverage : LiteratureRemarkCoverage)
    (affects : Array Lean.Name := #[])
    (formalDeclarations : Array Lean.Name := #[]) : LiteratureRemarkRef :=
  { paperId, sourceVersion, label, roles, summary, affects, formalDeclarations, coverage }

end RiemannianFluids
