# Executable literature

This repository is a claim-driven computational laboratory for Riemannian fluids.  A paper belongs here when it studies geometric viscosity, Stokes or Navier--Stokes equations, Hodge structure, or a thin-domain mechanism that selects a surface operator.  Czubak papers on unrelated PDE families are not silently folded into this library.

Each source has exactly one lean Python adapter in `reproductions/`.  The adapter records paper metadata, locates each registered claim in the source, states its assumptions and evidence class, and invokes reusable mathematics in `riemannian_fluids/`.  Paper files must not implement reusable geometry, operators, discretizations, or solvers.

## Evidence language

- **validated**: the repository currently runs the evidence gate stated by the claim and tests its acceptance criterion.
- **executable**: a computational analogue runs, but the full reproduction gate has not yet passed.
- **catalogued**: the claim is represented and its missing capability is known.
- **analytic-only**: the source claim is a theorem.  Computation may illustrate it or test a discrete analogue, but does not prove it.

Pointwise identities, manufactured PDE solutions, mesh convergence, spectra, and thin-domain limits are different evidence classes.  Passing one never promotes a claim in another class.

For the mathematical dependencies behind the analytic claims, see [`claim-to-proof.md`](claim-to-proof.md). That document explains how the shared geometry, operator, function-space, and PDE layers lead to the claim-specific Lean theorems.

For a source-to-Lean reading of those dependencies, see [`formal-analysis.md`](formal-analysis.md). It records the notation and sign translations and distinguishes concrete constructions from interface hypotheses and derived theorems.

## Corpus and live formal map

The corpus contains `CZ24`, `CCD17`, `CCY23`, `CCG25`, `CCF25`, `WBK26`, `WBS26`, `CC13`, `CC15`, `CC21`, and `CCP25`. The source list below is
stable, but a hand-maintained coverage table is not: it becomes stale as soon as an obligation is discharged.

The current map is therefore executable. [`../claims/registry.json`](../claims/registry.json) owns exact source claims and hypotheses;
[`../claims/lean-contracts.json`](../claims/lean-contracts.json) maps all 23 claims to typed statements; and `make lean/progress` prints every open proof
obligation and the transitive status of each literature-facing terminal theorem.

## Sources

Version-pinned PDFs are stored in [`../literature/pdfs/`](../literature/pdfs/). [`../literature/manifest.json`](../literature/manifest.json) records their retrieval URLs, sizes, page counts, and SHA-256 digests.

- `CZ24`: [local PDF](../literature/pdfs/CZ24-notices-71-1.pdf) · [DOI](https://doi.org/10.1090/noti2840)
- `CCD17`: [local PDF](../literature/pdfs/CCD17-arxiv-1608.05114v2.pdf) · [arXiv](https://arxiv.org/abs/1608.05114v2)
- `CCY23`: [local PDF](../literature/pdfs/CCY23-arxiv-2203.16050v1.pdf) · [arXiv](https://arxiv.org/abs/2203.16050v1)
- `CCG25`: [local PDF](../literature/pdfs/CCG25-arxiv-2212.11928v2.pdf) · [arXiv](https://arxiv.org/abs/2212.11928v2)
- `CCF25`: [local PDF](../literature/pdfs/CCF25-arxiv-2511.10579v1.pdf) · [arXiv](https://arxiv.org/abs/2511.10579v1)
- `WBK26`: [local PDF](../literature/pdfs/WBK26-arxiv-2605.17502v2.pdf) · [arXiv](https://arxiv.org/abs/2605.17502v2)
- `WBS26`: [local PDF](../literature/pdfs/WBS26-arxiv-2605.20589v3.pdf) · [arXiv](https://arxiv.org/abs/2605.20589v3)
- `CC13`: [local PDF](../literature/pdfs/CC13-arxiv-1006.2819v1.pdf) · [arXiv](https://arxiv.org/abs/1006.2819v1)
- `CC15`: [local PDF](../literature/pdfs/CC15-arxiv-1501.04928v1.pdf) · [arXiv](https://arxiv.org/abs/1501.04928v1)
- `CC21`: [local PDF](../literature/pdfs/CC21-arxiv-1708.05134v1.pdf) · [arXiv](https://arxiv.org/abs/1708.05134v1)
- `CCP25`: [local PDF](../literature/pdfs/CCP25-arxiv-1812.11764v1.pdf) · [arXiv](https://arxiv.org/abs/1812.11764v1)

The version and locator stored next to each executable claim are authoritative for a run.  If a source version changes, it is a new provenance event rather than an invisible metadata edit.
