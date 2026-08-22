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

Formal implementation: the exact axisymmetric-ellipsoid parametrization and coefficients, the Section 4 radial coefficient (4.6) with its surface trace, smooth positive-radius flux law, and exact divergence cancellation on every angular ray, both components of the projected ambient Hodge restriction formula, and the eccentricity expansion with an explicit fourth-order remainder bound. The remaining source-setting work is joint angular-radial smoothness and extraction of the coordinate jet from the constructed neighborhood field; the paper does not claim extension independence.

### CCG25: Gauss formulas for Laplacians

Chan--Czubak develop Laplacian restriction formulas for submanifolds, including ambient curvature, the second fundamental form, the normal connection, and higher-codimension Ricci terms.

Formal implementation: a canonical adjoint-based orthogonal splitting for isometric immersions; tangent and normal covariant derivatives constructed by extending, differentiating, and projecting; proved Gauss--Weingarten decompositions; a continuous bilinear kernel-normal second fundamental form and continuous trilinear `∇ᴮ II`; a general theorem that Lie brackets preserve germ-local `f`-relatedness for arbitrary smooth maps between boundaryless manifolds; an induced Levi--Civita connection proved metric-compatible, torsion-free, and independent of compatible extension choices on differentiable germs; germ-local ambient Levi--Civita restriction locality; symmetry of `II` and `∇ᴮ II`; source-sign-correct uncontracted and contracted Codazzi; shape operators and mean curvature by Riesz duality and trace; vector, scalar, and flat-ambient Euclidean Gauss equations on actual fibers; a paper-facing codimension-two Ricci contraction on `Fin 2` frames; an adapted ambient basis with proved Ricci trace splitting; Levi--Civita first Bianchi and curvature metric-skewness with Ricci symmetry as their contraction; and actual-fiber Bochner and Hodge Gauss formulas. Mathlib immersion normal-form charts now construct a genuine local retraction and compatible scalar, tangent, and along-field extensions with germ agreement and both differentiability and arbitrary finite-order regularity preservation. They directly construct a symmetric continuous bilinear `II` in the kernel-normal fiber, independently of chart choice. A pointwise family of those packages constructs a genuine induced covariant derivative; for an isometric embedding it is proved metric-compatible and torsion-free, Levi--Civita uniqueness identifies it with the intrinsic source connection on differentiable germs, and the corresponding local Gauss formula is proved. A smooth-extension theorem in the older engine proves that field-level `∇ᴮ II` on arbitrary `C²` tangent fields is pointwise in all three slots. A general connection theorem explicitly corrects the canonical tangent-bundle trivialization by chart-affine connection coefficients, producing a `C²` frame with any prescribed orthonormal value and vanishing full covariant derivative at the evaluation point. From one ordinary `C²` source field and pointwise tangent/normal bases, Lean constructs this geodesic frame, traces `II` to construct the mean-curvature normal field, and proves its first normal derivative and bracket--Weingarten. The intrinsic Bochner value is the immersion differential of the constructed rough Laplacian, the constructed ambient rough operator is expanded in the adapted frame, and canonical normal extensions identify its complete normal Hessian trace. The tangent trace is proved by twice differentiating Gauss for the actual varying field and identifying its derivative-sensitive term through Codazzi. Consequently the strongest paper-facing Bochner and Hodge theorems require no geodesic-frame field, mean-curvature jet, Hessian identity, Laplacian identity, or Ricci-symmetry premise. Exact reproduction now requires differentiating the fixed-chart Gauss germ and migrating `∇ᴮ II`, Codazzi, and the trace routes from the older global interface, plus the concrete Euclidean flatness specialization for the codimension-two result.

### CCF25: ellipsoid candidates and thin-shell derivation

Chan--Czubak--Fuster Aguilera compare surface operators produced by ambient restriction, scaling, normal-direction analysis, and averaging.  Their work makes the derivation procedure part of the operator specification.

Formal implementation: all four candidate formulas and the exact sphere collapse of Remark 1.5. Computational implementation: the candidates on the sphere and spheroid, with parameterized comparisons and source-linked validation gates. The thin-shell derivations remain source-labeled heuristics.

## Kinematic and boundary selection

### WBK26: kinematic selection

Wang--Braunstein derive deformation viscosity from the infinitesimal rate of metric strain and connect negative curvature with coercivity, uniqueness, and energy decay.

Formal implementation: the intrinsic infinitesimal metric-rate tensor; the manifold chain rule for the metric pairing along an actual particle integral curve; and the identification of a Lie-dragged connecting-pair jet's material rate with twice the deformation tensor. Constructing the connecting fields as pushforwards by a generated local flow remains open.

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
