# Riemannian Fluids

This is a research repository for formal and computational analysis of fluid equations on Riemannian manifolds, with an initial focus on Navier--Stokes equations and viscosity operators on surfaces.

There are two independently buildable implementations:

- `lean/` supplies machine-checked definitions and proofs for analytic claims.
- `python/` supplies executable geometry, numerical studies, manufactured solutions, discretizations, and convergence evidence.

Shared paper and claim provenance lives in `claims/`. Neither implementation may silently redefine a paper claim or its mathematical convention.

## Research program

The authoritative dependency structure is executable rather than prose-only:

- [`claims/registry.json`](claims/registry.json) owns source wording, locators, assumptions, and evidence classes;
- [`claims/lean-contracts.json`](claims/lean-contracts.json) maps every registered claim to a declaration in its permanent Lean module;
- [`lean/RiemannianFluids.lean`](lean/RiemannianFluids.lean) imports the complete codebase layout;
- each `lean/RiemannianFluids/Reproductions/<paper>/` package follows the paper's source and proof sections, owns its numbered-item and remark inventory, and is re-exported by a stable `<paper>.lean` facade;
- `make lean/progress` computes the current direct and transitive proof frontier.

[`docs/claim-to-proof.md`](docs/claim-to-proof.md) remains an explanatory guide to why the project constructs geometry before comparing Laplacians and develops weak Stokes theory before nonlinear evolution, but it is not the progress ledger.

The companion [`docs/formal-analysis.md`](docs/formal-analysis.md) explains how to read the Lean development as executable mathematical exposition: it gives the CCD17 notation crosswalk, sign translation, proof order, and current concrete/interface boundary.

The companion [`docs/literature.md`](docs/literature.md) gives the paper corpus, current evidence, and next missing gate for each source. Together these documents answer two different questions: what the literature claims, and what must be proved or computed for this repository to reproduce it.

## Expository formal analysis

The Lean code is written as an annotated mathematical essay, not merely to obtain a green theorem declaration. The opening narrative of each substantive module develops the idea and proof in ordinary mathematical language. Lean declarations then bookend that explanation with precise statements; declaration documentation explains representation and regularity choices, and comments inside nontrivial proofs translate formal steps back into mathematics. Definitions proved by `rfl` are documented as representation choices, since the definition itself is their proof.

The intended reading experience is therefore:

1. locate the paper statement in `claims/registry.json` and its declaration in `claims/lean-contracts.json`;
2. read its convention and notation crosswalk in `docs/formal-analysis.md`;
3. follow the actual import/declaration graph in a Lean IDE;
4. read the module narrative as the proof, then inspect the Lean comments to see where mathematics ends and library adaptation begins;
5. run `make lean/progress` and check the formal-status boundary before treating the result as a reproduction.

## Evidence boundary

Computational evidence can validate pointwise identities, manufactured solutions, and stated numerical convergence gates. It cannot validate an analytic theorem. A compiled statement with open obligations is only `contract-checked`; an analytic claim is reproduced only when its terminal Lean declaration has no transitive `sorryAx` dependency and the formalization ledger records the stronger state.

## Layout

```text
claims/     language-neutral paper and claim registry
docs/       literature census and research documentation
lean/       theorem-based Riemannian geometry and fluid analysis
python/     JAX, NumPy, FEniCSx, experiments, and computational reproductions
tools/      cross-language provenance and evidence audits
```

## Validation

```sh
make lean/sync
make lean/check
make lean/progress
make python/sync
make python/check
make claims/check
make check
```

The Lean and Python environments remain separately pinned by `lean/lake-manifest.json` and `python/uv.lock`.
