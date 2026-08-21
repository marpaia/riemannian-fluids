# The Lean development

The Lean library formalizes the geometry and analysis of incompressible viscous flow on Riemannian manifolds.  It is written as checked mathematical exposition: module narratives introduce the construction, declarations state it precisely, and proofs certify the advertised dependencies.

The library uses Lean 4 and Mathlib's manifold, vector-bundle, Riemannian-bundle, and covariant-derivative infrastructure.  [`RiemannianFluids.lean`](RiemannianFluids.lean) is the complete import root.

## Mathematical layers

### Geometry and tensors

`Geometry/` defines manifold conventions, connections, curvature data, bounded geometry, space forms, immersed submanifolds, surfaces of revolution, and tubular geometry.

`Tensors/` defines smooth sections, musical maps, scalar and vector calculus, tensor contraction and symmetry, differential forms, and exterior-calculus interfaces.  First-order operators display their regularity loss in their types.

### Function spaces and analysis

`FunctionSpaces/` defines solenoidal constraints, Sobolev forms, evolution spaces, and Hodge-decomposition data. The hyperbolic modules supply concrete scalar and intrinsic one-form `L²` spaces over the invariant volume, dense compact smooth cores, closed first-order operators, the source-normalized one-form `H¹` completion, and the `H¹` and `L²` Hodge sectors. `CanonicalTorusL2` supplies the actual normalized weighted shell `L²` family, the surface `L²` carrier, uniformly equivalent fixed-cylinder measures, and bounded lift/flux-identification maps used by the thin-shell Mosco program. `Analysis/LpMultipliers` turns measurable uniformly bounded fiberwise maps into continuous operators on Bochner `Lp` quotients.

`Analysis/` defines energy identities, compactness routes, harmonic and real-analytic function data, variational convergence on fixed and varying Hilbert spaces, and reusable closed-operator machinery. `ResolventGeneratedOperator` proves once that an injective symmetric bounded resolvent generates a densely defined closed self-adjoint operator by the graph equation `R(u+v)=u` and the maximal adjoint-domain argument.

### Fluid operators and equations

`Operators/` defines the rough, Hodge, and deformation viscosity candidates; their curvature and codifferential corrections; ambient restriction; formal-adjoint interfaces; Stokes operators; and Navier--Stokes operators. `Operators/HyperbolicHodgeStokes` constructs the concrete divergence-free hyperbolic form domain, Lax--Milgram resolvent, and densely defined closed nonnegative self-adjoint Hodge--Stokes operator with its exact harmonic kernel.

`PDE/` defines weak Navier--Stokes frameworks, pressure recovery, Leray--Hopf solutions, stationary equations, uniqueness, and energy statements.

`Viscosity/` contains the high-level formal synthesis:

- `IntrinsicStrain` constructs the infinitesimal metric-rate tensor from `Def`;
- `CurvatureComparison` proves both the bundled interface comparison and the constructed
  pointwise census from a curved divergence-free witness; and
- `BoundarySelection` defines the wall-parameter operator family and proves its endpoint algebra.

`Geometry/Instances/HyperbolicPlaneCensus` realizes the constructed census on the Poincaré
half-plane with no hypotheses beyond the chosen point.

`Geometry/Instances/HyperbolicPlaneMeasure` packages that same carrier with Mathlib's genuine Poincaré distance, properness/completeness, and invariant measure `dx dy / y²`. One-form `L²` uses norm-preserving coefficients in the proved orthonormal frame rather than the Euclidean coordinate-covector norm.

`Literature/` is the stable public façade for the Czubak Formal Corpus. Modules are named by paper ID and expose aliases whose scope matches the claim crosswalk. Geometry, analysis, and operator modules own the reusable implementations underneath this layer.

## Reading order

```mermaid
flowchart TD
  subgraph intrinsic [intrinsic viscosity]
    A1[Geometry.Manifolds] --> A2[Geometry.Connections]
    A2 --> A3[Geometry.Musical]
    A3 --> A4[Tensors.Symmetry]
    A4 --> A5[Tensors.VectorCalculus]
    A5 --> A6[Operators.Hodge]
    A6 --> A7[Operators.GeometricIdentities]
    A7 --> A8[Viscosity.IntrinsicStrain]
    A8 --> A9[Viscosity.CurvatureComparison]
    A9 --> A10[Geometry.Instances.HyperbolicPlaneCensus]
  end
  subgraph weak [weak fluid equations]
    B1[FunctionSpaces.Constraints] --> B2[Analysis.AbstractEnergy]
    B2 --> B3[Operators.Stokes]
    B3 --> B4[Operators.NavierStokes]
    B4 --> B5[PDE.PressureRecovery]
    B5 --> B6[PDE.Stationary]
    B6 --> B7[PDE.LerayHopf]
    B7 --> B8[PDE.WeakNavierStokes]
  end
  subgraph shells [submanifolds and thin domains]
    C1[Geometry.Submanifolds] --> C2[Operators.Restriction]
    C2 --> C3[Operators.SubmanifoldConstraints]
    C3 --> C4[Viscosity.BoundarySelection]
    C4 --> C5[Geometry.ThinShells]
    C5 --> C6[FunctionSpaces.CanonicalTorusL2]
    C6 --> C7[Analysis.VariationalConvergence]
  end
  subgraph noncompact [noncompact and negatively curved geometry]
    D1[Geometry.Instances.HyperbolicPlaneMeasure] --> D2[FunctionSpaces.HyperbolicL2]
    D2 --> D3[FunctionSpaces.HyperbolicFirstOrder]
    D3 --> D4[FunctionSpaces.HyperbolicH1]
    D4 --> D5[FunctionSpaces.HyperbolicHodgeDecomposition]
    D2 --> D6[FunctionSpaces.HyperbolicL2HodgeDecomposition]
    D5 --> D7[Operators.HyperbolicHodgeStokes]
    D6 --> D7
    D4 --> D8[proved shifted complete-manifold energy]
    D8 --> D9[exact CCP25 source identification]
    D7 --> D10["hyperbolic PDEs and thin-shell operator limits"]
    D9 --> D11[Hodge-Stokes/source domain equivalence]
    D11 --> D10
    D9 --> D10
  end
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

`ccd17_divfree_def_hodge` is a conditional theorem on bundled section operators.  Its hypotheses contain the Weitzenbock and symmetric-gradient identities, while its proof constructs the divergence-free cancellation and verifies

```math
L_{\mathrm{Def}}u=L_{\mathrm{Hodge}}u-2\,\mathrm{Ric}(u).
```

`ccd17_divfree_def_hodge_constructed` is the constructed counterpart: `Operators.ConstructedHodge` builds the exterior derivative on lowered fields as the antisymmetrized lowered covariant derivative — proving the connection-free bracket formula

```math
d(u^\flat)(X,Y)=X\,g(u,Y)-Y\,g(u,X)-g(u,[X,Y])
```

so the construction is honestly the intrinsic `d` — assembles the analysis-positive Hodge Laplacian from its two de Rham halves, proves the Weitzenbock identity `weitzenbock_constructedAt`

```math
L_{\mathrm{Hodge}}(u^\flat)(w)=\langle L_{\mathrm{rough}}u,w\rangle+\mathrm{Ric}(w,u),
```

and derives the same divergence-free identity with every operator constructed from the packaged Levi-Civita connection.  Its remaining hypotheses are the packaged Levi-Civita properties, the pointwise curvature-regularity bridge, and a `C³` atlas.

The tested deformation and Hodge covectors are raised by finite-dimensional Riesz duality to
canonical tangent-vector outputs.  Their pairing theorems recover the independently constructed
tested definitions, and `constructedCandidateOutputs_pairwiseDistinct_of_ricciWitness` uses the
proved comparison identities to show that a nonzero Ricci pairing separates the rough, Hodge,
and deformation outputs.  The concrete source theorem
`Literature.CZ24.operator_census_hyperbolic_witness` exposes the stable source-facing alias for `HyperbolicPlane.cz24_census_hyperbolic`, which applies the comparison to the
divergence-free horizontal field on the Poincaré half-plane, where

```math
\mathrm{Ric}(\partial_x,\partial_x)=-y^{-2}\ne0.
```

It proves pairwise distinction of the three fully constructed tangent-vector outputs at every
point.  This is the curved witness required to show that the differential constructions are not
universally equal.  The bundled section-operator predicate remains a separate interface statement
because its arbitrary-two-form `OneFormHodgeData` representation is not populated.

The distinction is recorded by theorem types and the selective Lean claim crosswalk.

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
