# Riemannian fluids

A minimal, mathematics-first research codebase for making the Riemannian-fluid literature executable.  Reusable differential geometry, fluid operators, function spaces, discretizations, and solvers live in `riemannian_fluids/`. Every paper is represented by one lean Python adapter in `reproductions/`.

The organizing chain is:

```text
source paper -> located claim -> reusable mathematical API -> evidence gate
```

The claim census and present coverage are in [`literature.md`](literature.md).

## Structure

```text
riemannian_fluids/
  geometry/          metrics, connections, curvature, embeddings, normal bundles
  tensors/           covariant calculus, musical maps, and differential forms
  operators/         rough, Hodge, deformation, Stokes, and Navier--Stokes operators
  function_spaces/   constraints, Sobolev diagnostics, and Hodge decomposition
  shells/            Fermi geometry, wall profiles, averaging, and shell problems
  discretization/    explicit backend capabilities and the optional FEniCSx path
  solvers/           mixed, nonlinear, transient, and generalized spectral references
  validation/        claims, provenance, evidence classes, and refinement diagnostics

reproductions/       exactly one lean Python file per paper
experiments/         cross-paper parameter studies and reports
literature.md        human-readable research census
```

The old top-level `calculus`, `viscosity`, `thin_shell`, and `fenics` imports are small compatibility shims.  New code should use the domain packages above.

## Run it

The host path is locked to Python 3.12 with `uv`:

```sh
uv sync --frozen --extra dev
make check
make literature
uv run --frozen python -m reproductions WBS26
```

The existing studies remain available:

```sh
make surface-viscosity
make thin-shell
```

FEniCSx is isolated in the official pinned DOLFINx container rather than silently replaced by a NumPy calculation:

```sh
make finite-elements/check
```

## Mathematical conventions

All reported Laplacians use the analysis-positive convention.  The 2026 interpolating family is

\[
L_\alpha=L_{\mathrm{Def}}+2\alpha\operatorname{Ric}
  +4\alpha(1-\alpha)S^2.
\]

Intrinsic dimension, ambient dimension, and codimension are separate explicit contracts.  Bare embedding callables remain accepted for small calculations; new work should use `RiemannianManifold` or `EmbeddedSubmanifold` so dimensional and ambient assumptions are visible.

## What the evidence currently establishes

The repository validates local curvature/operator identities, the four 2025 ellipsoid candidates on their stated geometry, the 2026 wall-selected family, finite-thickness two-wall polynomial fields, and a manufactured FEniCSx PDE on the normal fibre.  It also supplies tested reference APIs for differential forms, discrete Hodge decomposition, incompressible saddle systems, mass-matrix generalized eigenproblems, nonlinear solves, and time stepping.

The global Stokes reference is a vector-spherical-harmonic Galerkin model on the round sphere.  It handles exact/coexact modes, all three viscosity spectra, incompressibility, pressure recovery, the pressure gauge, and deformation's three Killing modes without hiding the mass-space interpretation.

The repository does **not** yet claim a resolved curved volume-shell reproduction, FEEC convergence, an expanding-domain hyperbolic theorem reproduction, or a global curved-surface Navier--Stokes simulation.  The backend capability object records those limits explicitly.  In particular, the local shell identity and the normal-fibre manufactured solution are not thin-shell PDE convergence.

For `WBS26-resolved-volume-shell`, success requires a curved 3D volume mesh, two independently tagged walls, a mixed incompressible solve, transverse averaging, wall/divergence/pressure diagnostics, and separate studies of mesh size \(h\), thickness \(\varepsilon\), and \(h/\varepsilon\).
