# Claim registry

`registry.json` is the language-neutral source of truth for paper metadata, claim IDs, locators, assumptions, conventions, required evidence kinds, and current evidence status.

`lean-contracts.json` is the total claim-to-Lean map. Every claim, including computational claims, must name one declaration in its permanent
`RiemannianFluids.Reproductions.<paper>.<source-part>` module. Each paper's
`Inventory` module is its complete package import endpoint. This means statement design
is reviewable in Lean without pretending that computational evidence is a formal proof.

`formalization.json` tracks analytic claims through four states:

- `catalogued`
- `contract-checked`
- `interface-proved`
- `formally-reproduced`

Only `formally-reproduced` satisfies an `analytic-theorem` evidence gate. `contract-checked` means the source statement elaborates and is mapped, not
that its proof is complete. Every non-catalogued analytic record maps both its
statement and its `literature_terminal` endpoint. `lean_module` owns the statement;
`terminal_module` records the endpoint owner when it differs. Mathematical statements
remain in typed Lean; JSON summaries do not generate theorem statements.

The registries are evidence ledgers, not substitutes for mathematical exposition. The current proof boundary is computed by `make lean/progress`,
which inspects `proof_obligation` and `literature_terminal` declarations with Lean's axiom printer. A status change must agree with that audit.
