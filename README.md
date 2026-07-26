# Riemannian Fluids

This is a research repository for formal and computational analysis of fluid equations on Riemannian manifolds, with an initial focus on Navier--Stokes equations and viscosity operators on surfaces.

There are two independently buildable implementations:

- `lean/` supplies machine-checked definitions and proofs for analytic claims.
- `python/` supplies executable geometry, numerical studies, manufactured solutions, discretizations, and convergence evidence.

Shared paper and claim provenance lives in `claims/`. Neither implementation may silently redefine a paper claim or its mathematical convention.

## Research program

The mathematical dependency structure is described in [`docs/claim-to-proof.md`](docs/claim-to-proof.md). It explains why the project constructs geometry before comparing Laplacians, develops weak Stokes theory before nonlinear evolution, and treats operator selection as a theorem with hypotheses rather than a global default.

The companion [`docs/literature.md`](docs/literature.md) gives the paper corpus, current evidence, and next missing gate for each source. Together these documents answer two different questions: what the literature claims, and what must be proved or computed for this repository to reproduce it.

## Evidence boundary

Computational evidence can validate pointwise identities, manufactured solutions, and stated numerical convergence gates. It cannot validate an analytic theorem. An analytic claim is reproduced only by a checked Lean declaration with a source-faithful statement and an accepted axiom audit.

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
make python/sync
make python/check
make claims/check
make check
```

The Lean and Python environments remain separately pinned by `lean/lake-manifest.json` and `python/uv.lock`.
