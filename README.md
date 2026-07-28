# Riemannian Fluids

Riemannian Fluids is a research library for incompressible viscous flow on Riemannian manifolds.  It develops the geometric operators, function spaces, weak equations, and limiting arguments that give Navier-Stokes equations their meaning on curved spaces.

The scientific program has four parts:

1. construct covariant differential operators on vector fields and differential forms;
2. compare the rough, Hodge, and deformation viscosity operators through curvature identities;
3. derive surface operators from intrinsic kinematics, ambient restriction, boundary laws, and thin-domain limits; and
4. formulate stationary and evolving incompressible flow on compact, noncompact, and negatively curved manifolds.

The repository contains a formal implementation in Lean and a computational implementation in Python.  They share mathematical conventions and literature provenance.

## Lean

[`lean/`](lean/) is the formal mathematical development.  It gives definitions and theorems precise types, tracks regularity loss, exposes every geometric hypothesis, and verifies proofs with Lean and Mathlib.

The formal development contains:

- smooth scalar fields, vector fields, one-forms, differential forms, and covariant tensors;
- Levi-Civita connection data, musical maps, covariant differentiation, gradient, divergence, and deformation strain;
- rough, Hodge, and deformation viscosity operators with analysis-positive signs;
- curvature and codifferential corrections relating those operators;
- incompressibility, Stokes, pressure, Navier--Stokes, Leray--Hopf, and stationary-flow formulations;
- Sobolev, evolution, Hodge-decomposition, bounded-geometry, submanifold, and thin-shell structures; and
- variational language for Mosco, resolvent, semigroup, and spectral convergence.

Lean declarations have three semantic roles:

- **construction**: Lean builds the mathematical object from the available geometric data;
- **conditional theorem**: Lean proves a conclusion from hypotheses displayed in the theorem type; and
- **source theorem**: Lean realizes the source setting and discharges its geometric and analytic hypotheses.

The compiled library is free of `sorry`, `admit`, project `axiom`, and project `constant`.  [`lean/RiemannianFluids/AxiomAudit.lean`](lean/RiemannianFluids/AxiomAudit.lean) audits representative results for hidden proof assumptions.

The formal entrance is [`lean/RiemannianFluids.lean`](lean/RiemannianFluids.lean).  [`lean/README.md`](lean/README.md) gives the mathematical reading order, and [`docs/formal-analysis.md`](docs/formal-analysis.md) gives the detailed notation and convention crosswalk.

## Python

[`python/`](python/) is the executable scientific implementation.  It evaluates geometric identities, constructs reference discretizations, solves model equations, and measures numerical evidence.

The Python package provides:

- intrinsic and embedded geometry for surfaces and space forms;
- tensor calculus, differential forms, and Hodge diagnostics;
- rough, Hodge, deformation, Stokes, and Navier--Stokes operators;
- Fermi coordinates, wall profiles, transverse averaging, and finite-thickness shell fields;
- vector-spherical-harmonic, mixed, nonlinear, transient, and generalized spectral solvers;
- an explicit FEniCSx backend for finite-element studies; and
- validation tools for residuals, refinement studies, spectra, constraints, and literature claim gates.

Python evidence is identified by its mathematical kind: pointwise identity, manufactured solution, discrete solve, mesh refinement, spectral comparison, or thin-domain study.  Each experiment reports the claim, geometry, parameters, observable, and acceptance criterion that determine its meaning.

[`python/README.md`](python/README.md) documents the package and executable studies.

## Literature and provenance

The literature supplies the definitions, comparison principles, examples, and analytic theorems developed by the repository.  [`literature/manifest.json`](literature/manifest.json) identifies the version-pinned source archive.  [`claims/registry.json`](claims/registry.json) records claim IDs, source locators, assumptions, conventions, evidence classes, and computational status.

[`claims/lean-contracts.json`](claims/lean-contracts.json) links source claims to formal declarations that implement part of their mathematics.  [`claims/formalization.json`](claims/formalization.json) records the formal status of analytic theorems.  [`docs/literature.md`](docs/literature.md) explains how the sources contribute to the common research program.

Formal proof and computational evidence answer different scientific questions.  Lean establishes logical consequences of explicit hypotheses.  Python establishes measured behavior of explicit models and discretizations.  The claim registry keeps both forms of evidence attached to the same source conventions.

## Mathematical architecture

```text
geometry and smooth tensors
  -> intrinsic differential operators
  -> viscosity comparison and selection
  -> function spaces and weak formulations
  -> stationary and evolving Navier--Stokes equations

submanifold and tubular geometry
  -> boundary-selected operators
  -> quadratic forms on thin domains
  -> variational and operator convergence

noncompact geometry and Hodge structure
  -> harmonic sectors and solenoidal closures
  -> hyperbolic Stokes and Navier--Stokes phenomena
```

[`docs/claim-to-proof.md`](docs/claim-to-proof.md) records this dependency structure and the formal milestones associated with each analytic claim.

## Layout

```text
lean/        formal definitions, constructions, and proofs
python/      executable geometry, operators, solvers, and studies
claims/      source claims and evidence status
literature/  version-pinned papers and retrieval metadata
docs/        mathematical exposition and research architecture
tools/       provenance and trust-boundary validation
```

## Validation

Pixi is the development environment and task runner.  Its single locked environment contains JAX, DOLFINx, PETSc, SLEPc, MPI, and the validation tools.

```sh
pixi install --locked
make lean/sync
make lean/check
make python/sync
make python/check
make claims/check
make check
```

`make lean/check` builds the formal library, audits its source closure, checks the literature crosswalk, and runs the axiom audit.  `make python/check` runs static analysis, tests, provenance adapters, the JAX reference studies, and the native DOLFINx study.  `make claims/check` verifies agreement among the shared registry, Python declarations, formal-status ledger, and Lean crosswalk.
