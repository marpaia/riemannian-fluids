# RiemannianFluids

A narrow Lean research library for theorem-based analysis of incompressible Navier–Stokes equations on intrinsic Riemannian surfaces.

The project builds on mathlib's manifold, tangent-bundle, Riemannian-bundle, and covariant-derivative APIs. It does not attempt to replace mathlib with a general differential-geometry library.

The module layout intentionally follows the executable project in `../python/riemannian_fluids`:

| Lean module | Executable counterpart |
| --- | --- |
| `RiemannianFluids.Geometry.Manifolds` | `geometry/manifolds.py` |
| `RiemannianFluids.Geometry.Connections` | `geometry/manifolds.py` |
| `RiemannianFluids.Geometry.Musical` | `geometry/manifolds.py`, `tensors/calculus.py` |
| `RiemannianFluids.Tensors.SmoothSections` | `tensors/calculus.py` |
| `RiemannianFluids.Tensors.ScalarCalculus` | `tensors/calculus.py` |
| `RiemannianFluids.Tensors.Contraction` | `tensors/calculus.py` |
| `RiemannianFluids.Tensors.Symmetry` | `tensors/calculus.py` |
| `RiemannianFluids.Tensors.VectorCalculus` | `tensors/calculus.py` |
| `RiemannianFluids.Tensors.DifferentialForms` | degree-indexed weak `d`, `d*`, harmonic, exact, and coexact definitions |
| `RiemannianFluids.Tensors.ExteriorCalculus` | graded `d`, `d*`, Hodge-star, and Hodge-Laplacian leaf API |
| `RiemannianFluids.Analysis.AbstractEnergy` | analytic interfaces used across operator modules |
| `RiemannianFluids.Analysis.ExhaustionCompactness` | WBK26 equations (46)--(48) compactness gates |
| `RiemannianFluids.Analysis.VariationalConvergence` | Mosco, resolvent, semigroup, and spectral contracts |
| `RiemannianFluids.FunctionSpaces.Constraints` | `function_spaces/constraints.py` |
| `RiemannianFluids.FunctionSpaces.Evolution` | solenoidal closures and Bochner evolution spaces |
| `RiemannianFluids.FunctionSpaces.HodgeDecomposition` | Sobolev Hodge-decomposition contract |
| `RiemannianFluids.FunctionSpaces.SobolevForms` | CCP25 weak derivatives, `H1`, and current definitions |
| `RiemannianFluids.Geometry.BoundedGeometry` | WBK26 completeness, injectivity radius, curvature, and derivative bounds |
| `RiemannianFluids.Geometry.Curvature` | curvature commutator, Ricci contraction, and surface Ricci API |
| `RiemannianFluids.Geometry.SpaceForms` | hyperbolic, pinched-curvature, cutoff, and harmonic-potential profiles |
| `RiemannianFluids.Geometry.Submanifolds` | Gauss/Weingarten, normal connection, and contracted Codazzi API |
| `RiemannianFluids.Geometry.ThinShells` | tubular/Fermi geometry and separated mesh/thickness limits |
| `RiemannianFluids.PDE.LerayHopf` | Leray--Hopf solution contract |
| `RiemannianFluids.PDE.PressureRecovery` | distributional de Rham pressure gate |
| `RiemannianFluids.PDE.Stationary` | exterior stationary-flow contracts |
| `RiemannianFluids.PDE.WeakNavierStokes` | weak evolution equation, trace, uniqueness, and pressure contracts |
| `RiemannianFluids.Operators.FormalAdjoints` | rough and deformation formal-adjoint constructions |
| `RiemannianFluids.Operators.Restriction` | ambient-to-intrinsic restriction and extension independence |
| `RiemannianFluids.Operators.Viscosity` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.Hodge` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.GeometricIdentities` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.Stokes` | `operators/stokes.py` |
| `RiemannianFluids.Operators.NavierStokes` | `operators/navier_stokes.py` |
| `RiemannianFluids.Reproductions.<paper>.*` | source sections, main-result assembly, numbered remarks, and local inventory for that paper |
| `RiemannianFluids.Reproductions.<paper>.Inventory` | complete import endpoint for one version-pinned paper package |
| `RiemannianFluids.Reproductions.Inventory` | common checked source-locator and remark-classification types |
| `RiemannianFluids.LiteratureInventory` | corpus-wide assembly of 104 results, 6 definitions, and 51 numbered remarks |

The correspondence is semantic, not a claim that numerical JAX functions have already been verified by Lean.

For an equation-by-equation guide to the formal development, including the CCD17 notation and sign-convention crosswalk, see [`formal-analysis.md`](../docs/formal-analysis.md). The Lean source is written as an annotated mathematical essay: each substantive module first presents the idea and proof in prose, then uses declarations as checked bookends. Comments inside nontrivial proofs explain how each mathematical movement is adapted to Lean.

## Current proved kernel

The current kernel formalizes:

1. the analysis-positive operator convention;
2. an intrinsic dimension-two surface-model predicate;
3. regularity-indexed smooth vector fields, one-forms, differential forms, tangent-valued one-forms, and covariant two-tensors;
4. an explicit metric-compatible, torsion-free tangent-connection witness;
5. covariant differentiation as a linear map from `C^(k+1)` vector fields to `C^k` tangent-valued one-forms, using mathlib's native connection regularity;
6. smooth metric lowering and raising on sections, proved mutually inverse;
7. a regularity-losing scalar differential and metric gradient, with the characterization $g(\operatorname{grad}f,X) = df(X)$;
8. coordinate-invariant smooth trace of tangent endomorphisms, intrinsic divergence, and a pointwise characterization of divergence-free fields;
9. coordinate-natural transpose and symmetrization of covariant two-tensors, giving the concrete formula for $\operatorname{Def}u$;
10. the one-form codifferential $d^*\alpha = -\operatorname{div}(\alpha^\sharp)$, the exact correction $(d d^*(u^\flat))^\sharp$, and its vanishing on divergence-free fields;
11. construction of the positive Hodge Laplacian from explicit degree-one de
    Rham data and pointwise action of an explicit smooth Ricci endomorphism;
12. separately stated positive Weitzenböck and symmetric-gradient identities;
13. the conditional full CCD17 identity and its proved divergence-free specialization $L_{\mathrm{Def}}u = L_{\mathrm{Hodge}}u - 2\operatorname{Ric}(u)$;
14. distinct rough, Hodge, and deformation viscosity candidates;
15. operator agreement modulo a vanishing correction;
16. incompressibility and pressure-gradient/divergence duality;
17. energy-conserving advection;
18. separate stationary Stokes and instantaneous Navier–Stokes predicates;
19. equivalence of Navier–Stokes formulations when their viscosity operators agree on incompressible fields;
20. the instantaneous energy identity and its unforced dissipation corollary.

The connection is chosen data: its existence and uniqueness have not yet been proved. Tensor transposition, $\operatorname{Def}u$, and the one-form codifferential are concrete. The degree-one exterior derivative, degree-two codifferential, Ricci endomorphism derived from curvature, and the formal-adjoint construction $2\operatorname{Def}^*\operatorname{Def}$ remain explicit inputs. Accordingly, `ccd17_divfree_def_hodge` is an interface theorem from visible Weitzenböck and symmetric-gradient hypotheses, not yet an end-to-end formal reproduction of CCD17. The kernel also does not prove PDE existence, regularity, uniqueness, or time evolution.

The abstract energy interfaces live under `RiemannianFluids.Analysis.AbstractEnergy`, so downstream theorems cannot be mistaken for a concrete Riemannian calculus implementation.

The repository-wide [`claim-to-proof`](../docs/claim-to-proof.md) document places this kernel in the full dependency graph for the registered literature claims. In particular, it distinguishes an abstract consequence proved from visible hypotheses from a paper theorem whose geometric and analytic hypotheses have been discharged.

## Operator-choice policy

There is no default vector Laplacian. Rough/Bochner, Hodge, and deformation operators remain distinct until a geometric or physical derivation supplies a proof. Comparison identities carry their correction term explicitly; a later theorem may show that term vanishes on a specified admissible space.

## Development and proof status

The package has one root: `RiemannianFluids.lean`. It imports completed proofs and unfinished source-facing theorem routes together. A placeholder is
legal only inside a declaration tagged `proof_obligation`; an untagged `sorry`, any `admit`, or a project `axiom`/`constant` fails the source audit.
Sorry-free internal composition nodes carry `proof_assembly`; the validator prints their explicit
source-level dependency edges. Paper-facing endpoints carry `literature_terminal`, so their
transitive axiom sets report whether a whole route is complete.

The graph is expository before it is proof-engineering-oriented.  In a literature route, the
primary nodes are the source's definitions, named results, displayed equations, and explicit
proof steps, in source order.  A Lean-specific helper may sit below one of those nodes, but it
does not replace a source node, merge several named lemmas, or become the public explanation of
why the paper's theorem follows.  This keeps the unfinished code readable as a formal rendering
of the proof rather than merely as a dependency graph optimized for the prover.  The source
validator rejects an unfinished declaration whose name merges multiple named lemmas or theorems;
registered endpoints may still package several final conclusions when the claim registry calls
for that combined contract.

Each `RiemannianFluids.Reproductions.<paper>.Inventory` module owns that paper's named-result,
numbered-definition, and numbered-remark census.  `RiemannianFluids.LiteratureInventory`
assembles those local inventories, uses Lean name quotation for declaration-backed items, and
proves the corpus-wide totals, per-kind counts, unique `(paper, source label)` keys, and remark
coverage split.  A missing or renamed mapped declaration therefore fails elaboration; Markdown
documentation is only a guide to that executable inventory.

```sh
lake update
lake exe cache get
make -C .. lean/check
make -C .. lean/progress
```

`lean/check` builds the library, verifies all 23 claim-to-declaration mappings, rejects unauthorized placeholders, and audits representative completed
kernel declarations. `lean/progress` additionally prints the direct and transitive `sorryAx`
frontier and explicit dependency edges of every tagged obligation, assembly, and terminal theorem.
`lean/statements` remains a compatibility alias for `lean/check`. The project is pinned to Lean and mathlib `v4.32.1`.
