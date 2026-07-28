# Reading the formal analysis

The Lean development is a checked mathematical exposition of geometric fluid mechanics.  It formalizes the objects and deductions that connect Riemannian geometry with incompressible viscosity, Stokes equations, and Navier--Stokes equations.

## What a module communicates

Each substantive module presents four layers of information.

1. **Mathematical object.** The opening narrative defines the construction and explains its role in fluid mechanics.
2. **Representation.** Lean types record the manifold model, bundle, regularity, scalar field, and domain of every operator.
3. **Dependencies.** The theorem type lists the geometric and analytic hypotheses used by the conclusion.
4. **Proof.** The proof verifies coordinate naturality, algebraic identities, regularity changes, and logical composition.

Declaration comments explain representation choices.  Proof comments describe the mathematical movement performed by each formal step.

## Semantic roles

The library uses three roles for formal declarations.

### Construction

A construction builds an object from Mathlib structures and explicit input data.  Examples include:

- smooth musical maps;
- covariant differentiation;
- the field-level curvature commutator of a bundled connection;
- its continuous pointwise trilinear realization in all three curvature slots;
- the pointwise Ricci trace and metric-raised Ricci endomorphism;
- the global smooth Ricci form, raised Ricci action, and scalar trace under an explicit
  contraction-regularity contract;
- the normalized pointwise sectional-curvature contraction;
- gradient and divergence;
- tensor transposition and symmetrization;
- the deformation tensor;
- the one-form codifferential; and
- the exact codifferential correction.

### Conditional theorem

A conditional theorem proves a conclusion from hypotheses displayed in its type.  This role captures mathematical reductions whose geometric or analytic inputs have an independent formalization path.

`ccd17_positive_full`, for example, derives the full deformation/Hodge identity from `WeitzenbockIdentity` and `SymmetricGradientIdentity`.

### Source theorem

A source theorem instantiates the geometry, function spaces, boundary conditions, and analytic estimates of a literature result and proves its stated conclusion.  The formalization ledger records progress toward this role for analytic claims.

## The CCD17 operator comparison

Chan--Czubak--Disconzi provide the central operator comparison developed by the library.

| CCD17 notation | Lean declaration | Formal representation |
| --- | --- | --- |
| vector field \(v\) | `SmoothVectorField` | regularity-indexed section of \(TM\) |
| metric dual \(v^\flat\) | `flat` | smooth section of \(T^*M\) |
| \(\nabla v\) | `covariantDerivative` | first-order tangent-valued one-form |
| \(\operatorname{Def}v\) | `deformationTensor` | symmetrized metric-lowered covariant derivative |
| \(d^*\) on one-forms | `codifferentialOne` | \(-\operatorname{div}\circ\sharp\) |
| \(d d^*+d^*d\) | `OneFormHodgeData.hodgeLaplacian` | second-order linear map |
| \(\operatorname{Ric}(v)\) | `RicciData.action` | pointwise smooth Ricci endomorphism action |
| Weitzenbock identity | `WeitzenbockIdentity` | equality of rough and Hodge operators with Ricci correction |
| symmetric-gradient identity | `SymmetricGradientIdentity` | equality defining the deformation correction |
| full comparison | `ccd17_positive_full` | algebraic combination of the two identities |
| incompressible comparison | `ccd17_divfree_def_hodge` | evaluation on a divergence-free field |

The repository uses analysis-positive operators:

\[
L_{\mathrm{rough}}=\nabla^*\nabla,
\qquad
L_{\mathrm{Hodge}}=d d^*+d^*d,
\qquad
L_{\mathrm{Def}}=2\operatorname{Def}^*\operatorname{Def}.
\]

CCD17 writes the signed Hodge Laplacian as \(\Delta_H=-(d d^*+d^*d)\).  Translation into the repository convention gives

\[
L_{\mathrm{Def}}
=L_{\mathrm{Hodge}}+d d^*-2\operatorname{Ric}.
\]

For a divergence-free field, \(d^*(u^\flat)=0\), so

\[
L_{\mathrm{Def}}u
=L_{\mathrm{Hodge}}u-2\operatorname{Ric}(u).
\]

## Formal status of the comparison

| Component | Status |
| --- | --- |
| smooth musical maps and inverse laws | constructed |
| covariant differentiation and regularity loss | constructed |
| field-level curvature commutator and alternating law | constructed |
| pointwise continuous curvature in the two direction slots | constructed under local connection regularity |
| `C²` tensoriality in the differentiated-field slot | proved under local connection regularity and a `C³` atlas |
| continuous trilinear curvature tensor `R(X,Y)Z` on `T_xM` | constructed under the same hypotheses |
| pointwise Ricci trace and metric-raised action | constructed from `R(X,Y)Z`; orthonormal-frame formula proved |
| bounded Ricci contraction on curvature model tensors | constructed; its Euclidean model-space map is smooth |
| global Ricci form and raised action | constructed under `HasConnectionRicciContractionRegularity` and smooth metric data |
| scalar curvature | constructed as the smooth trace of the raised Ricci field |
| sectional curvature | constructed pointwise as the normalized contraction of `R(X,Y)Y` against `X`; geometric use requires a nonzero Gram determinant |
| connection-derived `RiemannianCurvatureData` | all four fields derived by `connectionRiemannianCurvatureDataOfRegularCurvature` |
| smooth `RicciData` adapter | `RicciData.ofRegularConnection` discharges the older standalone `HasConnectionRicciRegularity` input |
| trace, divergence, and divergence-free predicate | constructed |
| tensor transpose, symmetrization, and `Def` | constructed |
| \(d^*(u^\flat)=-\operatorname{div}u\) | proved |
| vanishing of \((d d^*(u^\flat))^\sharp\) on divergence-free fields | proved |
| degree-one exterior derivative and degree-two codifferential | interface data |
| \(2\operatorname{Def}^*\operatorname{Def}\) from a formal adjoint | interface data |
| Weitzenbock and symmetric-gradient identities | theorem hypotheses |
| full and divergence-free comparison | proved from the displayed hypotheses |

This table identifies the exact formal boundary of `ccd17_divfree_def_hodge`.

## Dependency order

```text
smooth sections and manifold models
  -> connection and musical maps
  -> pointwise curvature tensor and bounded Ricci contraction
  -> global Ricci and scalar fields; pointwise sectional normalization
  -> scalar and vector calculus
  -> tensor symmetry and deformation strain
  -> differential forms and codifferential
  -> Hodge, rough, Ricci, and deformation operators
  -> geometric comparison identities
  -> incompressible specialization
  -> Stokes and Navier--Stokes consequences
```

The submanifold, thin-shell, and hyperbolic branches reuse these layers with their own geometry and function spaces.

## Trust boundary

The formal root contains zero proof placeholders and zero project axioms.  `make lean/check` performs four checks:

1. build the complete root;
2. scan its project import closure for forbidden proof primitives;
3. check and axiom-audit every literature crosswalk declaration; and
4. run `RiemannianFluids/AxiomAudit.lean` over representative milestones.

The accepted axiom set consists of Lean and Mathlib foundations such as `propext`, `Classical.choice`, and `Quot.sound`.

## Sources

- Chan, Czubak, and Disconzi, *The formulation of the Navier--Stokes equations on Riemannian manifolds*, arXiv:1608.05114v2: <https://arxiv.org/abs/1608.05114v2>.
- Versioned source metadata and claim locators: [`../claims/registry.json`](../claims/registry.json).
- Literature synthesis: [`literature.md`](literature.md).
