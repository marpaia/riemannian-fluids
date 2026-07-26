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
| `RiemannianFluids.Analysis.AbstractEnergy` | analytic interfaces used across operator modules |
| `RiemannianFluids.FunctionSpaces.Constraints` | `function_spaces/constraints.py` |
| `RiemannianFluids.Operators.Viscosity` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.Hodge` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.GeometricIdentities` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.Stokes` | `operators/stokes.py` |
| `RiemannianFluids.Operators.NavierStokes` | `operators/navier_stokes.py` |

The correspondence is semantic, not a claim that numerical JAX functions have already been verified by Lean.

## Current proved kernel

The current kernel formalizes:

1. the analysis-positive operator convention;
2. an intrinsic dimension-two surface-model predicate;
3. regularity-indexed smooth vector fields, one-forms, differential forms,
   tangent-valued one-forms, and covariant two-tensors;
4. an explicit metric-compatible, torsion-free tangent-connection witness;
5. covariant differentiation as a linear map from `C^(k+1)` vector fields to
   `C^k` tangent-valued one-forms, using mathlib's native connection regularity;
6. smooth metric lowering and raising on sections, proved mutually inverse;
7. a regularity-losing scalar differential and metric gradient, with the
   characterization `g(grad f, X) = df(X)`;
8. coordinate-invariant smooth trace of tangent endomorphisms, intrinsic
   divergence, and a pointwise characterization of divergence-free fields;
9. coordinate-natural transpose and symmetrization of covariant two-tensors,
   giving the concrete formula for `Def u`;
10. the one-form codifferential `d* α = -div (α♯)`, the exact correction
    `(d d*(u♭))♯`, and its vanishing on divergence-free fields;
11. construction of the positive Hodge Laplacian from explicit degree-one de
    Rham data and pointwise action of an explicit smooth Ricci endomorphism;
12. separately stated positive Weitzenböck and symmetric-gradient identities;
13. the conditional full CCD17 identity and its proved divergence-free
    specialization `L_Def u = L_Hodge u - 2 Ric(u)`;
14. distinct rough, Hodge, and deformation viscosity candidates;
15. operator agreement modulo a vanishing correction;
16. incompressibility and pressure-gradient/divergence duality;
17. energy-conserving advection;
18. separate stationary Stokes and instantaneous Navier–Stokes predicates;
19. equivalence of Navier–Stokes formulations when their viscosity operators agree on incompressible fields;
20. the instantaneous energy identity and its unforced dissipation corollary.

The connection is chosen data: its existence and uniqueness have not yet been
proved. Tensor transposition, `Def u`, and the one-form codifferential are
concrete. The degree-one exterior derivative, degree-two codifferential, Ricci
endomorphism derived from curvature, and the formal-adjoint construction
`2 Def* Def` remain explicit inputs. Accordingly,
`ccd17_divfree_def_hodge` is an interface theorem from visible Weitzenböck and
symmetric-gradient hypotheses, not yet an end-to-end formal reproduction of
CCD17. The kernel also does not prove PDE existence, regularity, uniqueness,
or time evolution.

The abstract energy interfaces live under
`RiemannianFluids.Analysis.AbstractEnergy`, so downstream theorems cannot be
mistaken for a concrete Riemannian calculus implementation.

The repository-wide [`claim-to-proof`](../docs/claim-to-proof.md) document places this kernel in the full dependency graph for the registered literature claims. In particular, it distinguishes an abstract consequence proved from visible hypotheses from a paper theorem whose geometric and analytic hypotheses have been discharged.

## Operator-choice policy

There is no default vector Laplacian. Rough/Bochner, Hodge, and deformation operators remain distinct until a geometric or physical derivation supplies a proof. Comparison identities carry their correction term explicitly; a later theorem may show that term vanishes on a specified admissible space.

## Build

```sh
lake update
lake exe cache get
make -C .. lean/check
```

The check builds the library with warnings treated as failures, prints the
axiom dependencies of representative declarations, and rejects project source
containing proof placeholders or new axiom declarations. The project is pinned
to Lean and mathlib `v4.32.1`.
