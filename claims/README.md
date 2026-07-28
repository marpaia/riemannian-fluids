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

## `lean-contracts.json`

`lean-contracts.json` records formal connections between source claims and reusable Lean declarations.  Each connection identifies:

- the intellectual thread;
- the owning Lean module and declaration;
- the logical relationship between the declaration and source claim; and
- the mathematical scope of the formal result.

The relationship field distinguishes a definition, a proved core identity, a conditional theorem, and an interface theorem.  `make lean/check` verifies declaration ownership and audits each mapped declaration for `sorryAx`.

## `formalization.json`

`formalization.json` records the status of every claim whose evidence class is `analytic-theorem`.

- `catalogued`: the source theorem and formal target are recorded.
- `contract-checked`: the Lean theorem statement, source assumptions, and conventions are fixed.
- `interface-proved`: Lean proves the conclusion from explicit intermediate hypotheses.
- `formally-reproduced`: Lean realizes the source setting, discharges the intermediate hypotheses, and proves the source conclusion.

`formally-reproduced` satisfies the analytic evidence gate.

## Validation

```sh
make claims/check
make lean/check
```

Together these commands verify source provenance, analytic-status coverage, Python agreement, Lean declaration ownership, and the formal trust boundary.
