# Literature program

The literature collected by Riemannian Fluids develops a common scientific question: how do curvature, topology, embeddings, boundaries, and noncompact geometry determine incompressible viscous flow?

This document describes the first versioned Czubak Formal Corpus release, `geometric-fluids-v1`: eleven pinned papers selected around that scientific question. It does not purport to inventory Magdalena Czubak's full publication record. Corpus expansion is a separate roadmap capability so completing proofs for this release cannot be mistaken for completing the whole literature.

The repository organizes that question into three connected research threads.

## Intrinsic viscosity and curvature

### CCD17: formulation on Riemannian manifolds

Chan--Czubak--Disconzi identify the rough, Hodge, and deformation constructions of vector viscosity and derive the curvature and divergence corrections relating them.  This work supplies the operator conventions and comparison identities at the center of the formal library.

Formal implementation: smooth strain, codifferential cancellation, Hodge data, Ricci action, Weitzenbock and symmetric-gradient hypotheses, and the divergence-free deformation/Hodge comparison.

### CZ24: viscosity operator survey

Czubak synthesizes the geometric ambiguity of vector viscosity and emphasizes the role of curvature and physical derivation.  This work supplies the operator-census question and the curved-witness criterion.

Formal implementation: pairwise inequivalence of the three intrinsic candidates from a divergence-free field with nonzero Ricci action.

### CCY23: invariant restriction to an ellipsoid

Chan--Czubak--Yoneda study the relationship between ambient differential operators and intrinsic surface operators.  Extension, tangent projection, and geometric correction terms determine the restriction problem.

Formal implementation: the exact axisymmetric-ellipsoid parametrization and coefficients, both components of the projected ambient Hodge restriction formula, and the eccentricity expansion with an explicit fourth-order remainder bound. The remaining source-setting work is to extract the coordinate jet from a smooth neighborhood field and formalize the paper's construction of a simultaneous ambient/surface divergence-free extension; the paper does not claim extension independence.

### CCG25: Gauss formulas for Laplacians

Chan--Czubak develop Laplacian restriction formulas for submanifolds, including ambient curvature, the second fundamental form, the normal connection, and higher-codimension Ricci terms.

Formal implementation: finite-dimensional tangent/normal Gauss geometry, shape operators and mean curvature constructed by Riesz duality and trace, arbitrary-codimension Bochner and Hodge trace theorems, and adapters to actual Mathlib tangent and kernel-normal fibers. The remaining gate is to derive the differentiated jets and Gauss--Codazzi identities from an isometric immersion and its connections.

### CCF25: ellipsoid candidates and thin-shell derivation

Chan--Czubak--Fuster Aguilera compare surface operators produced by ambient restriction, scaling, normal-direction analysis, and averaging.  Their work makes the derivation procedure part of the operator specification.

Formal implementation: all four candidate formulas and the exact sphere collapse of Remark 1.5. Computational implementation: the candidates on the sphere and spheroid, with parameterized comparisons and source-linked validation gates. The thin-shell derivations remain source-labeled heuristics.

## Kinematic and boundary selection

### WBK26: kinematic selection

Wang--Braunstein derive deformation viscosity from the infinitesimal rate of metric strain and connect negative curvature with coercivity, uniqueness, and energy decay.

Formal implementation: the intrinsic infinitesimal metric-rate tensor and its identity with twice the deformation tensor.

Analytic target: weak deformation-viscosity evolution on negatively curved surfaces, including coercivity, existence, pressure recovery, uniqueness, and exponential decay.

### WBS26: boundary-selected thin-shell limits

Wang--Braunstein derive a wall-parameter family of effective surface operators and formulate a variational thin-shell convergence theorem for selected geometries and wall conditions.

Formal implementation: the boundary-selected operator family, endpoint algebra, tubular geometry, varying quadratic-form data, and Hilbert-space Mosco and operator-convergence interfaces.

Computational implementation: two-wall finite-thickness profiles, divergence corrections, wall diagnostics, thickness studies, the closed-integral Navier regression mode, and an exact smooth-core recovery construction for every solenoidal stream-plus-flux field on the canonical torus at both rigorous endpoints.

Analytic target: concrete weighted carriers and closed forms, the form-domain extension of recovery, the liminf theorem, and then strong resolvent, semigroup, and scoped spectral convergence.

## Noncompact and hyperbolic flow

### CC13: Leray--Hopf nonuniqueness

Chan--Czubak connect finite-energy harmonic fields on the hyperbolic plane with nonuniqueness of Leray--Hopf solutions.  The theorem depends on the choice of solenoidal closure and harmonic sector.

Formal target: hyperbolic harmonic fields, weak trajectories, energy inequalities, and distinct solutions in the source energy class.

### CC15: stationary Liouville theorem

Chan--Czubak study stationary finite-Dirichlet Navier--Stokes flow on hyperbolic space through cutoff arguments, decay, and noncompact integration by parts.

Formal target: the finite-Dirichlet function space, stationary weak equation, cutoff estimates, and Liouville conclusion.

### CC21: hyperbolic exterior-domain flows

Chan--Czubak construct nontrivial stationary Stokes and Navier--Stokes flows in exterior domains of the hyperbolic plane.  Linear Stokes solvability and pressure recovery support the nonlinear construction.

Formal target: exterior-domain Sobolev spaces, nonzero Stokes solution, pressure, nonlinear correction, and stationary Navier--Stokes verification.

### CCP25: noncompact Sobolev Hodge decomposition

Chan--Czubak--Pinilla Suarez develop the Hodge decomposition of \(H^1\) differential forms on nonpositively curved space forms.  Exact, coexact, and harmonic sectors provide the function-space structure used throughout the hyperbolic fluid program.

Formal implementation: the canonical complete measured Poincare half-plane, concrete scalar and one-form `L²` carriers, the source-normalized one-form `H¹` completion, closed exact/coexact sectors, shifted-core dense range, the actual harmonic `L²` identification and recovery map, and the compatible Hodge--Stokes form domain.

Formal status: the `N=2`, `k=1`, `a=1` specialization is formally reproduced with an exact harmonic norm and no project axioms. The general theorem for arbitrary dimension, degree, and curvature scale remains specified.

## Evidence vocabulary

The repository records the following evidence classes:

- **formal theorem**: Lean proves the proposition from its displayed assumptions;
- **constructive witness**: exact construction proves every stated property for one explicitly scoped family;
- **pointwise identity**: numerical evaluation bounds a local residual;
- **manufactured solution**: a prescribed field satisfies a PDE and boundary residual gate;
- **discrete solve**: a finite-dimensional system satisfies algebraic and constraint diagnostics;
- **refinement study**: an observable exhibits its specified behavior across resolutions; and
- **thin-domain study**: thickness and mesh parameters vary independently with wall, divergence, pressure, and averaging diagnostics.

Claim IDs connect every evidence record to a source version, locator, convention, and acceptance criterion.

## Source archive

[`../literature/manifest.json`](../literature/manifest.json) records retrieval URLs, sizes, page counts, and SHA-256 digests for the version-pinned PDFs in [`../literature/pdfs/`](../literature/pdfs/).

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
