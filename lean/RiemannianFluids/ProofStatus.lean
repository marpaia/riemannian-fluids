import Lean

/-!
# Proof-status metadata

The main library elaborates source-faithful theorem statements before all of their proofs are available. Three tag attributes make that boundary
machine-readable:

* `proof_obligation` marks a source step whose own proof is intentionally unfinished; it may
  depend on earlier paper steps;
* `proof_assembly` marks a sorry-free internal node assembled from earlier declarations in
  the order used by the cited proof;
* `literature_terminal` marks a literature-facing theorem whose transitive axiom set determines whether the full route is complete.

The literature modules use the paper, not Lean proof convenience, as the primary decomposition:
each named definition, lemma, proposition, theorem, displayed equation, or explicit proof step
needed by a registered result receives its own declaration.  Lean-only helper lemmas may refine
one of those declarations, but must remain subordinate implementation details and must not replace
or merge source steps.

The attributes add no assumptions. `make lean/progress` discovers tagged declarations from the library import closure and asks Lean for their axiom
dependencies. A terminal theorem is complete only when its transitive dependency set no longer contains `sorryAx`.
-/

namespace RiemannianFluids

initialize proofObligationAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `proof_obligation "an unfinished source proof step which may contain direct sorry"

initialize proofAssemblyAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `proof_assembly "a sorry-free paper-ordered proof-graph node assembled from named dependencies"

initialize literatureTerminalAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `literature_terminal "a literature-facing terminal declaration whose transitive proof status is audited"

end RiemannianFluids
