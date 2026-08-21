# Claims and evidence

The `claims/` directory connects the literature, Lean declarations, and Python evidence through stable claim identifiers.

## `registry.json`

`registry.json` is the source-provenance ledger.  Each paper record contains bibliographic metadata and version information.  Each claim contains:

- a stable ID;
- a source locator;
- the mathematical statement;
- geometric and analytic assumptions;
- sign and notation conventions;
- the required evidence class; and
- the status of available computational evidence.

The Python literature adapters generate the same registry data from typed declarations.  `make claims/check` verifies exact agreement between those declarations and `registry.json`.

## `corpus.json`

`corpus.json` is the control plane for the Czubak Formal Corpus program.  It classifies every registry node along four independent axes:

- `origin`: a statement made by a source, a source theorem specialized by this project, or a project-created result;
- `assertion_kind`: theorem, identity, heuristic, constructed example, or evidence gate;
- `verification_target`: source proof, specialization proof, heuristic reconstruction, project proof, or computational validation; and
- `atomicity`: an atomic claim or a compound claim that must be split before formal completion.

This classification prevents a concrete specialization, numerical gate, or formalized heuristic from being counted as a proof of a broader source theorem.  Non-source nodes carry parent links back into the source-facing graph.  The current `geometric-fluids-v1` release covers the eleven pinned papers and 26 claims already present in the registry; it is explicitly the first release boundary, not yet the author's complete publication record.

`make claims/check` requires exact claim coverage, validates the vocabulary and parent links, and rejects `formally-reproduced` status for a non-proof target or an unsplit compound claim.

## `obligations.json`

`obligations.json` decomposes every `compound-needs-split` node into atomic conclusions before theorem work begins. The seven current compound parents produce 26 independently trackable obligations: source Gauss formulas, the four conclusions of the negatively curved weak-solution theorem, canonical-torus smooth-recovery properties, the separate Mosco and operator-convergence conclusions, the three dimensional cases of the Liouville theorem, and existence versus nonpotentiality for the two exterior-flow theorems.

Each obligation has its own stable ID, source locator, verification target, and state. `specified` fixes the source conclusion; `contract-checked` additionally names a Lean statement whose scope has been reviewed; `proved` names a checked proof. The validator requires complete coverage of all compound parents and prevents an obligation from inheriting the wrong evidence standard.

## `lean-contracts.json`

`lean-contracts.json` records formal connections between atomic corpus proof units and reusable Lean declarations. Those units may be registry claims or obligations split from compound parents. Stable public mappings point through paper-namespaced modules under `RiemannianFluids.Literature`; implementation modules remain free to evolve underneath them. Each connection identifies:

- the intellectual thread;
- the owning Lean module and declaration;
- the logical relationship between the declaration and source claim; and
- the mathematical scope of the formal result.

The relationship field takes one of four validated values:

- `proved-core`: Lean proves the mathematical core of the source claim outright; the limitation records any remaining interpretive gap between the proved statement and the source phrasing.
- `conditional-theorem`: Lean proves the source conclusion from hypotheses displayed in the theorem type whose own formalization remains open.
- `interface-theorem`: Lean proves the source deduction over interface data, receiving the named geometric or analytic identities as explicit arguments.
- `signed-to-analysis-positive-crosswalk`: Lean checks the algebraic conversion between the source paper's signed operator convention and the repository's analysis-positive convention.

`make claims/check` rejects any other value.  `make lean/check` verifies declaration ownership and audits each mapped declaration against the explicit standard axiom allowlist `propext`, `Classical.choice`, and `Quot.sound`.

## `formalization.json`

`formalization.json` is the corpus-wide proof-status ledger. It covers every atomic formal target: atomic registry claims plus the obligations replacing compound parents. The present release therefore tracks 42 proof units rather than only the nine registry nodes labeled `analytic-theorem`.

- `specified`: the exact atomic conclusion and verification target are recorded, but no Lean contract is claimed.
- `contract-checked`: a source-scoped Lean statement exists and is declaration-ownership and axiom audited.
- `proved-fragment`: Lean proves a conditional, interface-level, or otherwise strictly scoped fragment; the selective crosswalk records the remaining gap.
- `project-proved`: Lean proves an atomic project theorem, which still does not become a source result.
- `formally-reproduced`: Lean realizes the source setting, discharges the intermediate hypotheses, and proves the exact atomic source conclusion.

`formally-reproduced` satisfies the formal evidence gate for that exact atomic corpus node. It does not automatically close a parent claim with broader dimension, geometry, degree, solution class, or convergence conclusion.

## Validation

```sh
make claims/check
make lean/check
```

Together these commands verify the pinned PDF bytes and metadata, source provenance, corpus classification, atomic proof-status coverage, Python agreement, Lean declaration ownership, and the formal trust boundary.
