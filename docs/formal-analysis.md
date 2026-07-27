# Reading the formal analysis

The Lean development is an expository analysis of geometric fluid equations. Its purpose is not to replace the mathematical literature or its peer review. Its purpose is to expose, with machine-checked precision, which definitions, conventions, regularity losses, and intermediate identities make a literature claim work.

The prose is the primary exposition. Lean bookends the informal argument with precise declarations and checks that the advertised steps compose. A reader should be able to understand the mathematical idea from a module's opening narrative before reading a tactic. The code then answers a narrower question: did we represent that narrative faithfully enough for every stated dependency, type conversion, sign, and algebraic step to check?

## How to read a module

Each substantive Lean module should answer four questions.

1. **What is the mathematical construction?** The module documentation develops the coordinate-free idea and proof before discussing Lean.
2. **Where does it enter the literature?** Source-dependent modules cite the paper version and equation or section. Foundational modules state which later source identity they support.
3. **How is it represented in Lean?** Documentation explains the relevant mathlib bundle, the reason for each regularity index, and any gap between the paper's notation and the available library API.
4. **What does the proof do?** The module narrative gives the whole argument; nontrivial tactic proofs then carry comments that translate each formal step back into mathematics. Definitional proofs marked `rfl` are documented at the declaration because their content is precisely the choice of representation.

The intended balance is deliberately closer to an annotated mathematical essay than to a conventional software library. API documentation alone is not enough: the reader should encounter the motivation, the one central idea, the proof movements, and the current formal boundary before the implementation details.

Lean and Python source use a relaxed 160-column limit. Expository paragraphs are normally filled near 150 columns, leaving a little room for indentation; code may use the same width when that keeps one mathematical expression together. Semantic breaks remain welcome, but narrow wrapping is not a goal. Markdown prose remains unwrapped, following `.prettierrc` and `.editorconfig`.

The comments distinguish three kinds of statements:

- **Concrete construction:** the object is built from mathlib geometry, such as metric lowering, divergence, tensor transposition, or $\operatorname{Def} u$.
- **Interface hypothesis:** the mathematical object is named and typed, but a prerequisite absent from the pinned library is supplied as data, such as the degree-one exterior derivative or curvature-derived Ricci endomorphism.
- **Derived theorem:** Lean checks the conclusion from the preceding concrete constructions and explicit interface hypotheses.

This distinction is part of the mathematics. An interface theorem can explain the exact logical shape of a paper argument without yet constituting a formal reproduction of the paper.

## The CCD17 notation crosswalk

The first vertical slice follows Chan--Czubak--Disconzi, *The formulation of the Navier--Stokes equations on Riemannian manifolds*, arXiv:1608.05114v2, published in *Journal of Geometry and Physics* 121 (2017), 335--346.

| CCD17 notation | Repository declaration | Lean representation |
| --- | --- | --- |
| $v$, identified with $v^\flat$ when forms are used | `SmoothVectorField`, `flat` | A regularity-indexed section of $TM$, converted to a section of $T^*M$ |
| $\nabla v$ | `covariantDerivative` | A section of $\operatorname{Hom}(TM,TM)$ losing one derivative |
| $(\operatorname{Def} v)_{ij} = \frac12 (\nabla_i v_j + \nabla_j v_i)$ (1.2) | `deformationTensor` | Metric-lower $\nabla v$, then apply coordinate-natural symmetrization |
| $d^*$ on one-forms | `codifferentialOne` | $-\operatorname{div} \circ \sharp$ |
| $d d^* + d^* d$ | `OneFormHodgeData.hodgeLaplacian` | Sum of two regularity-losing linear maps |
| $\operatorname{Ric}(v)$ | `RicciData.action` | Pointwise action of a supplied smooth Ricci endomorphism |
| $\nabla^*\nabla = d d^* + d^* d - \operatorname{Ric}$ (1.1) | `WeitzenbockIdentity` | Equality of second-order linear maps |
| $2\operatorname{Def}^*\operatorname{Def} = \nabla^*\nabla + d d^* - \operatorname{Ric}$ | `SymmetricGradientIdentity` | Equality of second-order linear maps |
| equation (1.3) | `ccd17_positive_full` | Algebraic combination of the previous two identities |
| equation (1.3), $d^*v = 0$ | `ccd17_divfree_def_hodge` | Evaluate the full identity and eliminate the exact correction |

CCD17 defines its signed Hodge Laplacian by $\Delta_H = -(d d^* + d^* d)$. This repository instead reserves names beginning with `L_` for analysis-positive operators. Thus $L_{\mathrm{Hodge}} = d d^* + d^* d = -\Delta_H$. The translated positive identity is

$$
L_{\mathrm{Def}} = L_{\mathrm{Hodge}} + d d^* - 2\operatorname{Ric},
$$

and on divergence-free fields it becomes

$$
L_{\mathrm{Def}}u = L_{\mathrm{Hodge}}u - 2\operatorname{Ric}(u).
$$

The sign translation is documented next to the Lean declarations so that an apparently harmless notation change cannot silently reverse the PDE.

## Dependency order

The package root imports the two terminal modules. The actual import graph, which a Lean IDE can display, gives the proof order:

```text
smooth sections
  -> manifold and metric infrastructure
  -> connection, musical maps, scalar differential, trace, tensor symmetry
  -> divergence, Def, and the codifferential
  -> Hodge/Ricci operator data
  -> Weitzenbock and symmetric-gradient identities
  -> CCD17 full identity
  -> CCD17 divergence-free specialization
```

The abstract Stokes/Navier--Stokes branch is separate. It proves algebraic consequences of incompressibility, pressure orthogonality, and advection cancellation, but does not pretend that those abstract spaces are already the Sobolev spaces used in an analytic existence theorem.

## Current formal boundary

The following parts of the CCD17 path are concrete:

- smooth musical maps and their inverse laws;
- covariant differentiation with explicit loss of one derivative;
- coordinate-invariant trace and intrinsic divergence;
- coordinate-natural transpose and symmetrization;
- the pointwise formula and symmetry of $\operatorname{Def} u$;
- $d^*(u^\flat) = -\operatorname{div}u$ and vanishing of $(d d^*(u^\flat))^\sharp$ for divergence-free $u$;
- the algebra deriving equation (1.3) and its divergence-free specialization.

The following parts are still interfaces:

- existence and uniqueness of the chosen Levi-Civita connection;
- the exterior derivative on one-forms and codifferential on two-forms;
- construction of Ricci by contracting the Riemann tensor;
- the formal adjoint needed to construct $2\operatorname{Def}^*\operatorname{Def}$;
- geometric proofs of the Weitzenbock and symmetric-gradient identities.

Consequently, `ccd17_divfree_def_hodge` is an expository interface theorem, not yet an end-to-end formal reproduction. The theorem is useful precisely because its type shows the remaining obligations without conflating them with the algebra that has already been checked.

## Sources

- Chan, Czubak, and Disconzi, arXiv:1608.05114v2, especially equations (1.1)--(1.3) and the divergence-free specialization immediately following equation (1.3): <https://arxiv.org/abs/1608.05114>.
- The language-neutral source version and claim locator are recorded in [`claims/registry.json`](../claims/registry.json).
- The broader source corpus and evidence classes are recorded in [`literature.md`](literature.md).
