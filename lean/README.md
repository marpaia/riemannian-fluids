# RiemannianFluids

A narrow Lean research library for theorem-based analysis of incompressible Navier–Stokes equations on intrinsic Riemannian surfaces.

The project builds on mathlib's manifold, tangent-bundle, Riemannian-bundle, and covariant-derivative APIs. It does not attempt to replace mathlib with a general differential-geometry library.

The module layout intentionally follows the executable project in `../python/riemannian_fluids`:

| Lean module | Executable counterpart |
| --- | --- |
| `RiemannianFluids.Geometry.Manifolds` | `geometry/manifolds.py` |
| `RiemannianFluids.Tensors.Calculus` | `tensors/calculus.py` |
| `RiemannianFluids.FunctionSpaces.Constraints` | `function_spaces/constraints.py` |
| `RiemannianFluids.Operators.Viscosity` | `operators/viscosity.py` |
| `RiemannianFluids.Operators.Stokes` | `operators/stokes.py` |
| `RiemannianFluids.Operators.NavierStokes` | `operators/navier_stokes.py` |

The correspondence is semantic, not a claim that numerical JAX functions have already been verified by Lean.

## Current proved kernel

The first milestone formalizes:

1. the analysis-positive operator convention;
2. an intrinsic dimension-two surface-model predicate;
3. an explicit metric-compatible, torsion-free connection witness;
4. distinct rough, Hodge, and deformation viscosity candidates;
5. operator agreement modulo a vanishing correction;
6. incompressibility and pressure-gradient/divergence duality;
7. energy-conserving advection;
8. separate stationary Stokes and instantaneous Navier–Stokes predicates;
9. equivalence of Navier–Stokes formulations when their viscosity operators agree on incompressible fields;
10. the instantaneous energy identity and its unforced dissipation corollary.

These are abstract analysis theorems. They do not yet construct the geometric operators or prove PDE existence, regularity, uniqueness, or time evolution.

The repository-wide [`claim-to-proof`](../docs/claim-to-proof.md) document places this kernel in the full dependency graph for the registered literature claims. In particular, it distinguishes an abstract consequence proved from visible hypotheses from a paper theorem whose geometric and analytic hypotheses have been discharged.

## Operator-choice policy

There is no default vector Laplacian. Rough/Bochner, Hodge, and deformation operators remain distinct until a geometric or physical derivation supplies a proof. Comparison identities carry their correction term explicitly; a later theorem may show that term vanishes on a specified admissible space.

## Build

```sh
lake update
lake exe cache get
lake build
```

The project is pinned to Lean and mathlib `v4.32.1`.
