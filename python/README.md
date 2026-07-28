# The Python implementation

The Python package is the executable scientific layer of Riemannian Fluids.  It implements geometric models, differential operators, reference solvers, and validation studies for incompressible flow on curved manifolds.

The package follows the chain

```text
geometry -> tensors -> operators -> function spaces -> discretization -> solver -> evidence
```

## Package structure

```text
riemannian_fluids/
  geometry/          metrics, connections, curvature, domains, embeddings, normal geometry
  tensors/           covariant calculus, musical maps, tensor operations, differential forms
  operators/         viscosity, Stokes, and Navier--Stokes operators
  function_spaces/   constraints, Sobolev diagnostics, and Hodge decompositions
  shells/            Fermi geometry, wall profiles, transverse averaging, shell problems
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
- nonlinear and transient reference solves;
- Fermi-coordinate shell fields, two-wall profiles, divergence corrections, and transverse averages; and
- finite-element manufactured solutions through a pinned DOLFINx container.

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

The FEniCSx study runs in the image defined by `Dockerfile.fenicsx` and verifies a manufactured finite-element problem with the pinned DOLFINx environment.

## Active validation targets

The computational program is extending toward:

- a resolved curved three-dimensional volume shell with two tagged walls;
- independent refinement in mesh size \(h\), thickness \(\varepsilon\), and \(h/\varepsilon\);
- FEEC realizations and convergence for noncompact Hodge decompositions;
- expanding-domain hyperbolic Stokes and Navier--Stokes studies; and
- global curved-surface Navier--Stokes simulations.

Backend capability records identify which observables and validation gates each implementation supplies.

## Conventions

All Laplacians use the analysis-positive convention.  Intrinsic dimension, ambient dimension, and codimension are explicit model data.  The wall-parameter family records its Ricci and shape-square coefficients explicitly.  Solvers report their mass-space interpretation, pressure gauge, nullspace handling, and convergence observable.

## Run

The environment is locked to Python 3.12 with `uv`.

```sh
uv sync --frozen --extra dev
make check
make literature
uv run --frozen python -m reproductions WBS26
make surface-viscosity
make thin-shell
make finite-elements/check
```

`make check` runs Ruff, the test suite, all literature adapters, and the reference surface-viscosity and thin-shell studies.
