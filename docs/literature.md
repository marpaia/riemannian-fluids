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

## Corpus

| ID | Source | Executable coverage | Next missing gate |
|---|---|---|---|
| `CCD17` | Chan--Czubak--Disconzi (2017), *The formulation of the Navier--Stokes equations on Riemannian manifolds* | Bochner/Hodge/deformation identities and equation API | Global hyperbolic witness, weak forms, relativistic asymptotics |
| `CCY23` | Chan--Czubak--Yoneda (2023), ellipsoid restriction | Claims catalogued; ellipsoid geometry and ambient restriction APIs available | Paper's invariant formula, exact eccentricity expansion, and global weak solve |
| `CCG25` | Chan--Czubak, Gauss formulas for submanifolds | Arbitrary intrinsic dimension and codimension geometry API | Normal connection and general ambient-curvature identity suite |
| `CCF25` | Chan--Czubak--Fuster Aguilera (2025), ellipsoid candidates | All four candidates on sphere and spheroid | Symbolic eccentricity comparison |
| `WBK26` | Wang--Braunstein (2026), kinematic model | Intrinsic strain and nonlinear equation API | Hyperbolic coercivity and weak-solution decay study |
| `WBS26` | Wang--Braunstein (2026), thin shell | Local restriction identity, two-wall fields, normal-fibre PDE | Curved 3D mixed shell solve, averaging, and separate mesh/thickness convergence |
| `CC13` | Chan--Czubak (2013), hyperbolic nonuniqueness | Hyperbolic metrics and claim contract | Expanding-domain harmonic-field witness |
| `CC15` | Chan--Czubak (2015), hyperbolic Liouville theorem | Claim contract | Weighted noncompact weak spaces and truncation study |
| `CC21` | Chan--Czubak (2021), hyperbolic Stokes problem | Claim contract | Exterior-domain mixed Stokes solve |
| `CCP25` | Chan--Czubak--Pinilla Suarez (published 2025), Hodge decomposition | Smooth and discrete de Rham/Hodge APIs | FEEC mesh realization and harmonic-dimension convergence |

## Sources

- <https://arxiv.org/abs/1608.05114>
- <https://arxiv.org/abs/2203.16050>
- <https://arxiv.org/abs/2212.11928>
- <https://arxiv.org/abs/2511.10579>
- <https://arxiv.org/abs/2605.17502>
- <https://arxiv.org/html/2605.20589v3>
- <https://arxiv.org/abs/1006.2819>
- <https://arxiv.org/abs/1501.04928>
- <https://arxiv.org/abs/1708.05134>
- <https://arxiv.org/abs/1812.11764>

The version and locator stored next to each executable claim are authoritative for a run.  If a source version changes, it is a new provenance event rather than an invisible metadata edit.
