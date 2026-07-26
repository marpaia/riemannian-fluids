# Claim registry

`registry.json` is the language-neutral source of truth for paper metadata, claim IDs, locators, assumptions, conventions, required evidence kinds, and current evidence status.

`formalization.json` tracks analytic claims through four states:

- `catalogued`
- `contract-checked`
- `interface-proved`
- `formally-reproduced`

Only `formally-reproduced` satisfies an `analytic-theorem` evidence gate. Such an entry must identify a compiled Lean module and declaration. Mathematical statements remain in typed Lean; JSON summaries do not generate theorem statements.

The registry is an evidence ledger, not a substitute for mathematical exposition. [`docs/claim-to-proof.md`](../docs/claim-to-proof.md) records the reusable proof dependencies, explains their order, and identifies the route for each analytic claim. A status change should be justified by the declaration and completion criteria described there.
