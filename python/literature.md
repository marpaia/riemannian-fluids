# Computational literature map

The Python implementation attaches executable evidence to located claims in the Riemannian-fluid literature.  Each adapter in `reproductions/` records source metadata, assumptions, conventions, evidence class, acceptance criterion, and the reusable computation that evaluates the claim.

Reusable geometry, tensor calculus, operators, discretizations, solvers, and diagnostics live in `riemannian_fluids/`.  The adapters bind those capabilities to source claims.

## Evidence status

- **validated**: the declared acceptance criterion passes in the repository test workflow.
- **executable**: the model or analogue runs and produces its declared observables.
- **catalogued**: the source claim and validation target are recorded.
- **analytic-only**: the claim's evidence gate is a formal analytic proof; Python supplies source data, illustrations, and discrete analogues.

## Corpus

| ID | Scientific contribution | Executable evidence | Next validation target |
| --- | --- | --- | --- |
| `CZ24` | viscosity-operator ambiguity on curved manifolds | source and operator-census specification | explicit curved witness study |
| `CCD17` | rough/Hodge/deformation comparison | pointwise Bochner, Hodge, deformation, and equation residuals | global hyperbolic witness and weak-form study |
| `CCY23` | invariant ambient restriction to an ellipsoid | ellipsoid geometry and restriction APIs | invariant formula and eccentricity expansion |
| `CCG25` | Gauss formulas for submanifold Laplacians | arbitrary intrinsic-dimension and codimension geometry APIs | normal-connection and ambient-curvature identity suite |
| `CCF25` | four ellipsoid viscosity candidates | all four candidates on sphere and spheroid | symbolic eccentricity comparison |
| `WBK26` | kinematic deformation viscosity and curvature decay | intrinsic metric-rate identity and nonlinear equation APIs | hyperbolic coercivity and weak-solution decay study |
| `WBS26` | wall-selected operator family and thin-shell convergence | local family, two-wall fields, normal-fibre PDE, thickness study | curved three-dimensional mixed shell solve and averaging convergence |
| `CC13` | hyperbolic Leray--Hopf nonuniqueness | hyperbolic metrics and claim specification | expanding-domain harmonic-field witness |
| `CC15` | hyperbolic stationary Liouville theorem | claim and function-space specification | weighted noncompact truncation study |
| `CC21` | hyperbolic exterior Stokes and Navier--Stokes flows | claim, domain, and solver specification | exterior-domain mixed Stokes solve |
| `CCP25` | Sobolev Hodge decomposition on nonpositive space forms | smooth and discrete de Rham/Hodge APIs | FEEC mesh realization and harmonic-dimension convergence |

## Provenance

The shared [`../claims/registry.json`](../claims/registry.json) is generated from the Python adapter declarations and checked for exact agreement.  Source versions and locators define the provenance of every run.  A source-version update creates a new recorded provenance event.

The version-pinned PDFs and retrieval metadata live under [`../literature/`](../literature/).
