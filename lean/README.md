# The Lean development

The Lean library formalizes the geometry and analysis of incompressible viscous flow on Riemannian manifolds.  It is written as checked mathematical exposition: module narratives introduce the construction, declarations state it precisely, and proofs certify the advertised dependencies.

The library uses Lean 4 and Mathlib's manifold, vector-bundle, Riemannian-bundle, and covariant-derivative infrastructure.  [`RiemannianFluids.lean`](RiemannianFluids.lean) is the complete import root.

## Mathematical layers

### Geometry and tensors

`Geometry/` defines manifold conventions, connections, curvature data, bounded geometry, space forms, immersed submanifolds, surfaces of revolution, and tubular geometry.

`Tensors/` defines smooth sections, musical maps, scalar and vector calculus, tensor contraction and symmetry, differential forms, and exterior-calculus interfaces.  First-order operators display their regularity loss in their types.

### Function spaces and analysis

`FunctionSpaces/` defines solenoidal constraints, Sobolev forms, evolution spaces, and Hodge-decomposition data.

`Analysis/` defines energy identities, compactness routes, harmonic and real-analytic function data, and variational convergence on fixed and varying Hilbert spaces.

### Fluid operators and equations

`Operators/` defines the rough, Hodge, and deformation viscosity candidates; their curvature and codifferential corrections; ambient restriction; formal-adjoint interfaces; Stokes operators; and Navier--Stokes operators.

`PDE/` defines weak Navier--Stokes frameworks, pressure recovery, Leray--Hopf solutions, stationary equations, uniqueness, and energy statements.

`Viscosity/` contains the high-level formal synthesis:

- `IntrinsicStrain` constructs the infinitesimal metric-rate tensor from `Def`;
- `CurvatureComparison` proves pairwise operator inequivalence from a curved divergence-free witness; and
- `BoundarySelection` defines the wall-parameter operator family and proves its endpoint algebra.

## Reading order

### Intrinsic viscosity

```text
Geometry.Manifolds
  -> Geometry.Connections
  -> Geometry.Musical
  -> Tensors.Symmetry
  -> Tensors.VectorCalculus
  -> Operators.Hodge
  -> Operators.GeometricIdentities
  -> Viscosity.IntrinsicStrain
  -> Viscosity.CurvatureComparison
```

### Weak fluid equations

```text
FunctionSpaces.Constraints
  -> Analysis.AbstractEnergy
  -> Operators.Stokes
  -> Operators.NavierStokes
  -> PDE.PressureRecovery
  -> PDE.Stationary
  -> PDE.LerayHopf
  -> PDE.WeakNavierStokes
```

### Submanifolds and thin domains

```text
Geometry.Submanifolds
  -> Operators.Restriction
  -> Operators.SubmanifoldConstraints
  -> Viscosity.BoundarySelection
  -> Geometry.ThinShells
  -> Analysis.VariationalConvergence
```

### Noncompact and negatively curved geometry

```text
Geometry.SpaceForms
  -> Geometry.BoundedGeometry
  -> FunctionSpaces.SobolevForms
  -> FunctionSpaces.HodgeDecomposition
  -> Analysis.HarmonicFunctions
  -> Analysis.ExhaustionCompactness
  -> PDE.Stationary / PDE.WeakNavierStokes
```

## Meaning of declarations

Every public theorem states its mathematical commitment in its type.

- A **constructed object** is defined from Mathlib structures and explicit input data.
- A **conditional theorem** proves a conclusion from named geometric or analytic hypotheses.
- A **source theorem** instantiates the source geometry and function spaces and proves the source conclusion.

For example, `deformationTensor_apply` is a construction theorem.  It expands intrinsic strain into

```math
\mathrm{Def}\,u(X,Y)
=\frac12\bigl(g(\nabla_Xu,Y)+g(\nabla_Yu,X)\bigr).
```

`ccd17_divfree_def_hodge` is a conditional theorem.  Its hypotheses contain the Weitzenbock and symmetric-gradient identities, while its proof constructs the divergence-free cancellation and verifies

```math
L_{\mathrm{Def}}u=L_{\mathrm{Hodge}}u-2\,\mathrm{Ric}(u).
```

The distinction is recorded by theorem types and the formalization ledger.

## Operator conventions

Names beginning with `L_` denote analysis-positive operators.  The library keeps the following constructions individually named:

```math
L_{\mathrm{rough}}=\nabla^*\nabla,
\qquad
L_{\mathrm{Hodge}}=d d^*+d^*d,
\qquad
L_{\mathrm{Def}}=2\,\mathrm{Def}^*\mathrm{Def}.
```

Comparison theorems display Ricci, grad-div, shape, and boundary corrections explicitly.  Admissibility hypotheses identify the fields on which a correction vanishes.

## Trust boundary

The compiled root contains zero `sorry`, `admit`, project `axiom`, and project `constant` declarations.  [`RiemannianFluids/AxiomAudit.lean`](RiemannianFluids/AxiomAudit.lean) applies `#print axioms` to representative milestones.  Accepted output consists of Lean and Mathlib foundations such as `propext`, `Classical.choice`, and `Quot.sound`.

The claim crosswalk records the exact relationship between literature claims and Lean declarations, including each declaration's mathematical scope.

## Build

```sh
lake update
lake exe cache get
make -C .. lean/check
```

The project is pinned to Lean and Mathlib `v4.32.1`.
