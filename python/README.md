# The Python implementation

The Python package is the executable scientific layer of Riemannian Fluids.  It implements geometric models, differential operators, reference solvers, and validation studies for incompressible flow on curved manifolds.

The package follows the chain

```text
geometry -> tensors -> operators -> function spaces -> discretization -> solver -> evidence
```

The backend and evidence boundaries are specified in [`../docs/computational-architecture.md`](../docs/computational-architecture.md).

## Package structure

```text
riemannian_fluids/
  discrete.py        typed semidiscrete velocity-pressure flow contract
  geometry/          metrics, connections, curvature, domains, embeddings, normal geometry
  tensors/           covariant calculus, musical maps, tensor operations, differential forms
  operators/         viscosity, Stokes, and Navier--Stokes operators
  function_spaces/   constraints, Sobolev diagnostics, and Hodge decompositions
  shells/            Fermi geometry, wall profiles, transverse averaging, shell problems
  symbolic/          exact SymPy backend: charts, covariant kernel, energy integrals, thin-shell limits
  discretization/    backend capabilities, spherical spectra, and FEniCSx
  solvers/           mixed, nonlinear, transient, and generalized spectral solvers
  validation/        residuals, provenance, evidence classes, and refinement diagnostics

experiments/          parameter studies and report-producing entry points
reproductions/        source claim metadata and executable evidence adapters
tests/                mathematical and software verification
```

The top-level `calculus`, `viscosity`, `thin_shell`, and `fenics` modules provide compatibility imports for the domain packages.

## Mathematical content

The implementation supports:

- round spheres, spheroids, tori of revolution, perturbed spheres, hyperbolic models, and embedded submanifolds;
- metric, inverse metric, Christoffel symbols, curvature, Ricci action, shape operators, and Gauss identities;
- intrinsic gradient, divergence, strain, covariant advection, and differential-form operations;
- rough, Hodge, and deformation viscosity operators with analysis-positive signs;
- incompressibility constraints, pressure gauges, Hodge decompositions, and harmonic sectors;
- vector-spherical-harmonic Stokes spectra and mixed saddle systems;
- constrained stationary and implicit-transient semidiscrete Navier--Stokes reference solves;
- Fermi-coordinate shell fields, two-wall profiles, divergence corrections, and transverse averages; and
- mixed Taylor--Hood surface Stokes and resolved three-dimensional shell solves through native, pinned DOLFINx.

## The symbolic backend

`riemannian_fluids.symbolic` is the exact companion to the numeric layer.  It implements the same charts, conventions, and operators in SymPy and cross-checks every operator against the JAX implementation at sampled points in float64.

The backend provides:

- symbolic charts with declared positive parameters and validated volume densities (sphere, hyperbolic geodesic-polar, torus of revolution, spheroid);
- the covariant kernel: Christoffel symbols, curvature, musical maps, deformation strain, and the rough, Hodge, and deformation viscosity operators;
- structured fields whose properties hold by construction (coexact stream fields, gradient fields, rotation Killing fields) in a closed, type-checked hierarchy;
- the energy-integral solver: symmetry reduction to radial integrals with tiered certificates (exact closed form, proven finiteness or divergence by endpoint comparison, or an honest unresolved verdict), a derivation ledger, and mpmath quadrature verification;
- the identity engine: the divergence form of the deformation energy with its explicit boundary flux, and chart-level verification of `L_Def = L_Hodge - 2 Ric` for a generic stream function; and
- the thin-shell solver: truncation-tracked epsilon-series, sphere tube charts in the numeric `det(I - sigma S)` convention, two-wall rotational profiles, and transverse-averaged pairing eigenvalues that recover the interpolating family `L_Def + 2 alpha Ric + 4 alpha (1 - alpha) S^2` with the rotational eigenvalue `6 alpha - 4 alpha^2`.

[`examples/`](examples/) contains worked, narrated computations for both solvers; `pixi run --locked symbolic-examples` runs them.

## Evidence produced by Python

Every result belongs to a declared evidence class:

- **pointwise identity**: evaluates a geometric or operator residual on sampled points;
- **manufactured solution**: verifies a prescribed field against a differential equation and boundary data;
- **discrete solve**: solves a stated finite-dimensional variational or algebraic problem;
- **spectral comparison**: compares eigenvalues, multiplicities, kernels, or mode decompositions;
- **refinement study**: measures an observable across mesh or resolution scales; and
- **thin-domain study**: varies thickness, mesh size, and their ratio while tracking wall, divergence, pressure, and averaging diagnostics.

The evidence record identifies the geometry, parameters, convention, observable, tolerance, and claim ID.

## Reference studies

`surface-viscosity` evaluates divergence, the metric-rate identity, Gauss and Weitzenbock relations, deformation/Hodge comparison, wall-selected operators, and ellipsoid candidates on the supported surfaces.

`thin-shell` constructs finite-thickness two-wall fields, evaluates their asymptotic coefficients, and measures raw and corrected divergence across thickness values.

The spherical Stokes implementation uses vector spherical harmonics.  It represents exact and coexact modes, the three viscosity spectra, incompressibility, pressure recovery, the pressure gauge, and the Killing-field kernel of deformation viscosity.

`surface-stokes` solves a mixed P2/P1 resolvent-deformation Stokes problem on successively refined polyhedral spheres.  Its target is a degree-one coexact rotational Killing mode from the spherical spectral implementation.  The study reports velocity error, surface divergence, normal leakage, and pressure gauge diagnostics.

`navier-stokes` exercises the general semidiscrete contract with nonzero energy-preserving quadratic convection.  It recovers a manufactured stationary velocity-pressure state with constrained Newton and advances an unforced flow with implicit Euler while checking incompressibility and energy decay.  This is solver-level finite-dimensional evidence, not yet a spatially resolved surface Navier--Stokes simulation.

`resolved-shell` constructs a genuine tetrahedral three-dimensional spherical shell with independently tagged inner and outer walls.  A mixed P2/P1 manufactured Stokes solve tracks velocity, pressure, divergence, no-slip wall-trace geometry error, transverse-average error, thickness, tangential mesh size, normal layers, and \(h/\varepsilon\).  The current no-slip study establishes the volume-mesh and diagnostics path; it does not establish the paper's Navier/Hodge wall-selected thin-shell convergence theorem.

`wall-selection` solves the Navier deformation form, Hodge div--curl form, and signed-curvature intermediate wall forms on the resolved shell.  It compares transverse averages with exact spherical rotational resolvents, first at fixed thickness under mesh refinement and then along a coupled sequence with constant \(h/\varepsilon\).  This is proof-oriented numerical evidence for one mode; [`../docs/thin-shell-convergence.md`](../docs/thin-shell-convergence.md) records the remaining continuous Mosco proof obligations.

All FEniCSx studies run natively from the single default Pixi environment with DOLFINx 0.11 and MUMPS-backed PETSc factorization.  The image defined by `Dockerfile.fenicsx` realizes that same locked Pixi environment on Linux; it remains an explicit reference path, not the macOS development default.

## Active validation targets

The remaining computational program includes:

- multi-mode and non-spherical Navier, Hodge, and partial-slip volume-shell comparisons beyond the current rotational sphere mode;
- proof-quality separated limits in mesh size \(h\), thickness \(\varepsilon\), and \(h/\varepsilon\);
- FEEC realizations and convergence for noncompact Hodge decompositions;
- expanding-domain hyperbolic Stokes and Navier--Stokes studies; and
- spatially resolved curved-surface Navier--Stokes simulations beyond the current surface Stokes and dense nonlinear references.

Backend capability records identify which observables and validation gates each implementation supplies.

## Conventions

All Laplacians use the analysis-positive convention.  Intrinsic dimension, ambient dimension, and codimension are explicit model data.  The wall-parameter family records its Ricci and shape-square coefficients explicitly.  Solvers report their mass-space interpretation, pressure gauge, nullspace handling, and convergence observable.

## Run

The repository-root `pixi.toml` is the development manifest.  One Pixi environment contains the JAX reference implementation, the native FEniCSx backend, and all validation tools.  Run these commands from the repository root.

```sh
pixi install --locked
pixi run --locked check
pixi run --locked literature
pixi run --locked literature WBS26
pixi run --locked surface-viscosity
pixi run --locked surface-stokes
pixi run --locked navier-stokes
pixi run --locked thin-shell
pixi run --locked finite-elements
pixi run --locked resolved-shell
pixi run --locked wall-selection
pixi run --locked fenicsx-check
pixi run --locked finite-elements-mpi
```

`make check` runs Ruff, the test suite, all literature adapters, the reference surface-viscosity and thin-shell studies, and the native DOLFINx study.

On macOS, `pixi shell` exposes JAX, DOLFINx, UFL, PETSc, and MPI together to an interactive shell or editor.  `pixi run --locked fenicsx-check` runs the normal-fibre, surface, and volume-shell finite-element gates, while the container reference remains available as `make -C python finite-elements/check/docker`.
