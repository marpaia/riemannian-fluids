# Czubak Formal Corpus roadmap

The repository is being developed as a robust formal corpus for Magdalena Czubak's literature:

> For a versioned publication corpus, expose every key mathematical claim as an atomic, source-scoped specification; prove it from shared geometric and analytic infrastructure; and make the exact proof boundary independently checkable from the claim ID through the public Lean declaration and its axiom audit.

Lean establishes exact geometric and analytic statements. Symbolic computation supplies inspectable formulas. JAX and finite elements provide independent computational checks. A source-labeled heuristic may be reconstructed under explicit assumptions, but it is never silently promoted to a theorem. A project specialization or computational gate never substitutes for a proof of its parent source claim.

## Corpus completion contract

A corpus release is complete only when all of the following hold:

1. its paper list, immutable source versions, key-claim inventory, and locators are complete for the declared release boundary;
2. every source result is split into atomic theorem or identity nodes, with conventions and assumptions represented in its Lean statement;
3. every atomic source-proof target has a stable declaration under `RiemannianFluids.Literature.<paper>` and reaches `formally-reproduced` without project axioms or unfinished placeholders;
4. source specializations, project theorems, source heuristics, and computational evidence gates remain separately typed and link to their parent claims;
5. every public claim declaration is covered by declaration-ownership validation and the strict axiom allowlist; and
6. shared geometry, functional analysis, operator theory, and PDE infrastructure is factored below the literature layer, so subsequent papers reuse the same definitions rather than restating bespoke interfaces.

The current `geometric-fluids-v1` boundary consists of the eleven pinned papers and 26 registry nodes already in the repository. It is the first corpus release, not yet a claim that the author's entire publication record has been inventoried. Expanding the bibliography and claim graph is a named later phase and cannot be conflated with completing the current release.

## Program capabilities

| Capability | Exit condition | State |
| --- | --- | --- |
| M0: corpus control plane | every current node is classified by origin, assertion kind, verification target, and atomicity; paper-namespaced Lean entry points and validators enforce the schema | complete |
| M1: atomic source specifications | all seven compound nodes in `geometric-fluids-v1` are split; every source-proof node has a source-faithful Lean theorem signature and dependency route | complete |
| M2: geometric operator kernel | the CZ24, CCD17, CCY23, CCG25, CCF25, and WBK26 operator identities and constructions are proved at their exact source scope | active; CCG25 now reaches constructed rough/Hodge operators with its tangent-Hessian trace proved, while the remaining smooth local-field realization is open |
| M3: noncompact Hodge foundation | CCP25 is proved first on `H²(-1)` and then at the source's full dimension, degree, and curvature-scale scope, with reusable closed-form and self-adjoint-operator machinery | partial; `H²(-1)` complete |
| M4: hyperbolic PDE corpus | CC13 nonuniqueness, CC15 Liouville, CC21 exterior Stokes/Navier--Stokes, and the full WBK26 weak-solution theorem are formally reproduced | open |
| M5: thin-shell selection | WBS26 Mosco, resolvent, semigroup, and spectral results are reproduced at source scope; heuristic CCF25 limits remain explicitly heuristic unless independently promoted and proved | active on the canonical torus |
| M6: full-literature expansion | the versioned bibliography and atomic claim inventory are extended from `geometric-fluids-v1` to the complete publication corpus | open |
| M7: audited corpus release | every in-scope source-proof target is reproduced, all heuristic and computational nodes have their proper evidence, documentation is generated from the ledgers, and the full repository validation passes | open |

Work is scheduled by the earliest incomplete corpus capability it closes. Shared infrastructure is prioritized when it discharges multiple paper routes; isolated lemmas are not reported as program milestones.

## Completed capability: M1 atomic source specifications

M1 closes a precise specification boundary over the current release. The seven compound registry nodes are split into 26 atomic obligations, and the resulting proof-status ledger contains 42 atomic formal targets. Exactly 35 of those targets are source proofs. Every one now owns a stable declaration under `RiemannianFluids.Literature.<paper>`, and every crosswalk records a nonempty route into reusable geometry, function-space, operator, convergence, or PDE infrastructure.

The previously absent paper namespaces `CC13`, `CC15`, `CC21`, `CCY23`, `CCG25`, and `CCF25` now expose source-scoped propositions. `CCD17`, `CCP25`, `WBK26`, and `WBS26` expose the remaining unproved conclusions alongside their already proved fragments. In particular, the WBS26 surface is no longer one generic convergence placeholder: form-domain recovery, the smooth `O(epsilon^2)` rate, form/operator association, strong resolvents, compact-time-uniform semigroups, fixed-mode compactness and spectral convergence, the uniform high-mode gap, and full-spectrum no-pollution are distinct definitions on actual varying Hilbert carriers.

M1 does not count definitions as proofs. A `source-signature` is an axiom-free `Prop` definition whose hypotheses and conclusion have been audited against the pinned source; it remains `contract-checked` until a theorem inhabits it. The validators now fail closed if any atomic source-proof unit loses its declaration, dependency route, paper ownership, or axiom audit. This makes M2 the next incomplete capability: proving the geometric operator kernel at exact source scope.

## Active end-to-end campaign: M2 geometric operator kernel

M2 is one coherent source-to-proof campaign, not a queue of unrelated identities. Its target is a reusable embedded-submanifold differential engine that proves the arbitrary-codimension Gauss--Weingarten trace formulas once and then specializes them through the literature graph. The engine must prove the CCG25 Bochner formulas (1.5)--(1.6), the Ricci contraction (1.11)--(1.12), and the Hodge formula of Corollary 1.20 on actual Mathlib-backed immersion and tangent/normal bundle data. CCY23 must instantiate the restriction machinery on the axisymmetric ellipsoid, including the paper's construction of an admissible simultaneous ambient/surface divergence-free extension and the eccentricity expansion. The source proves existence of such extensions; it does not assert that the restricted operator is independent of arbitrary ambient extension choices. CCF25's sphere collapse is the constant-curvature algebraic corollary, while CZ24, CCD17, and WBK26 are regression endpoints for the intrinsic operator conventions.

M2 closes only when those paper-level source signatures are inhabited at their stated dimensions and codimensions by constructions derived from the source geometric data—not by assuming intermediate jet identities—the generic submanifold theorems are reusable below the literature layer, and the claim ledger upgrades the exact nodes to `formally-reproduced`. This shared kernel is also the geometric input required by the WBS26 shell forms, so completing M2 advances the thin-shell campaign rather than competing with it.

### M2 closure ledger

The reusable CCG25 differential core is now complete at the pointwise geometric level and connected to the repository's constructed operators. Starting from one isometric immersion, one ambient Levi--Civita connection, and one compatible extension operator, Lean constructs the adjoint orthogonal splitting, the induced Levi--Civita connection, the kernel-normal second fundamental form, and the full continuous trilinear tensor `∇ᴮ II`. Germ-local restriction locality makes this tensor linear even when the global extension operator itself preserves identities only after restriction to the immersed source. The source-checked Codazzi convention `(R̃(W,X)Y)⊥ = (∇ᴮ_W II)(X,Y) - (∇ᴮ_X II)(W,Y)` is then proved and contracted, rather than assumed. Torsion-freeness and the constructed Weingarten formula likewise prove the mean-bracket identity from an explicit first-order realization of the mean-curvature normal field. The analytic adapter starts from one actual `C²` source tangent field and its chosen `C²` ambient extension: the induced connection constructs its intrinsic covariant Hessian, while the ambient connection constructs its tangent and normal Hessian traces. Canonical linear extensions of normal-fiber vectors construct the normal-frame acceleration correction and identify raw iteration minus acceleration with the actual normal Hessian trace. The intrinsic jet value is unconditionally the immersion differential of `roughLaplacianAt`; an adapted-basis theorem splits the ambient `roughLaplacianAt`; and the normal half of that split is identified unconditionally. The remaining tangent half is now also proved: twice differentiating Gauss for the actual varying field, using Codazzi to identify the derivative-sensitive `∇ᴮ II` slot, yields the diagonal identity and its finite-frame trace. The paper-facing Bochner and Hodge theorems therefore no longer accept a tangent-Hessian or Laplacian identity. For `C²` metrics, Lean derives first Bianchi and curvature metric-skewness from the Levi--Civita structure and contracts them to Ricci symmetry, so the corresponding Hodge identifications require no separate symmetry premise. CCY23 equation (4.6) remains a separate construction with a proved raywise smooth coefficient, weighted ODE, and exact divergence cancellation. None of the remaining fragments is promoted to exact source reproduction until the smooth local extension data and mean-curvature first jet assumed in the paper-level realization are constructed from source hypotheses. A global tubular retraction is one possible implementation, not a premise of CCG25 Theorem 1.1, which only assumes extensions on a neighborhood of the evaluation point.

| Atomic target | Checked result | Remaining exact-source gate |
| --- | --- | --- |
| `CZ24-operator-census` | formally reproduced on the concrete hyperbolic witness | closed |
| `CCD17-divfree-def-hodge` | formally reproduced with constructed Levi-Civita, Hodge, deformation, and Ricci terms on a smooth Riemannian manifold | closed |
| `CCG25-gauss-ricci-codimension-two` | differentiated Gauss--Weingarten, field/pointwise shape agreement, vector Gauss, scalar Gauss, and the flat-ambient `Fin 2` Ricci contraction are derived from one actual-fiber immersion package under a regularity-only extension contract | realize that contract and ambient flatness from a smooth tubular extension in the concrete Euclidean model |
| `CCG25-bochner-laplacian-gauss-general-codimension` | the intrinsic and ambient values are the constructed rough Laplacians; the adapted tangent/normal trace split, complete normal trace, twice-differentiated tangent Gauss identity, and both actual-operator formulas are proved | construct the compatible smooth local-extension package, its differentiated regularity, and the mean-curvature normal-field first jet from source-level neighborhood data |
| `CCG25-hodge-laplacian-gauss-general-codimension` | scalar Gauss, adapted Ricci splitting, and both Hodge formulas are proved on the same actual fibers; for `C²` metrics both jet values equal the constructed Hodge operators, with the tangent Hessian and Ricci symmetry proved internally | discharge the shared smooth local-field realization gate from the Bochner node |
| `CCY23-invariant-restriction` | both components of (1.4) are proved for the exact ellipsoid two-jet; (4.6) now gives a proved raywise smooth coefficient with zero surface trace and exact ambient-divergence cancellation | prove joint angular-radial smoothness and extract the two-jet from the constructed neighborhood field |
| `CCY23-eccentricity-expansion` | the exact rational formula gives (5.8) with an explicit uniform `O(mu^4)` remainder on `0 < mu < 1/2` | connect smooth coordinate fields to the proved jet expansion |
| `CCF25-four-candidates-sphere` | formally reproduced: all four formulas are constructed and constant unit curvature kills the common scaling generator | closed; the paper's thin-shell derivations remain separately classified as heuristic |
| `WBK26-lie-strain` | the metric Lie-derivative identity equals twice deformation strain | realize the infinitesimal metric rate as the derivative of the pullback metric along the generated flow |

The critical path is therefore no longer formula discovery, tensoriality of `∇ᴮ II`, Codazzi, bracket--Weingarten, vector/scalar Gauss, ambient Ricci splitting, construction of the source field's intrinsic and ambient Hessians, either adapted-frame Hessian trace, Ricci symmetry, or a generic operator-identification problem. It is one reusable geometric obligation: construct the smooth local fields used by the source calculations and derive their regularity from neighborhood data. For CCG25 it must supply compatible tangent/normal extensions, differentiated regularity, the mean-curvature normal-field first jet, and the concrete Euclidean flatness specialization used by the codimension-two corollary. For CCY23 it must supply joint angular-radial smoothness and the coordinate jet already consumed by the ellipsoid result. A tubular retraction may implement these fields, but the public theorem must follow the source's weaker local-neighborhood hypothesis. Once this package is stable, the CCG25 source signatures can be inhabited without caller-supplied intermediate geometric facts, the CCY23 restriction and expansion can use the same neighborhood mechanism, and the remaining WBK26 flow-rate adapter is bounded cleanup. Only then do the six remaining fragments qualify for promotion and M2 close.

## Active end-to-end campaign: WBS26 wall selection

The largest current source theorem is a concrete specialization of WBS26 Theorem 4.5 and Corollary 4.6 on a non-umbilic torus-type surface of revolution. For each endpoint wall condition, that package must contain:

1. the rescaled shell geometry and weighted shell `L²` carrier for every admissible thickness;
2. the solenoidal shell form domain with the correct impermeability and natural wall condition;
3. the tangential solenoidal surface `L²` carrier and the selected Navier or Hodge limit form;
4. bounded identification and lifting maps between the varying shell spaces and the surface space;
5. the Mosco liminf theorem for every bounded-energy weakly convergent shell sequence;
6. a solenoidal recovery sequence for every limit-form vector, including the `O(epsilon²)` rate on the smooth core;
7. the nonnegative self-adjoint operators associated with those exact forms; and
8. strong resolvent convergence, compact-time semigroup convergence, fixed-mode spectral convergence, and the high-mode exclusion needed for the source's full spectral conclusion.

The public completion theorem must quantify over the actual carriers and operators. A structure populated with predicates, a single-mode computation, or a numerical refinement study does not satisfy this objective.

The first exact target geometry is the canonical torus of revolution already used by the recovery certificate. Once both endpoints are closed there, the construction is generalized to the source's torus-type surface-of-revolution class. General hypersurfaces and nonlinear Navier--Stokes convergence are later extensions, not hidden requirements of the first end-to-end theorem.

## Completed analytic proving ground

The repository now contains an axiom-free hyperbolic analytic benchmark on `H²(-1)`: Chan--Czubak--Pinilla Suarez's complete-space `H¹` Hodge identification together with the concrete `L²` Leray projector and closed nonnegative self-adjoint Hodge--Stokes operator. The operator was constructed on a coexact-`H¹` plus harmonic-`L²` form domain independently of global regularity; the completed CCP25 package proves that this form domain is continuously linearly equivalent to the source's full divergence-free `H¹` space.

The completed package exposes all of the following without project axioms or analytic placeholders:

1. the complete measured Poincare half-plane;
2. concrete scalar and one-form `L²` quotient Hilbert spaces;
3. the source `H¹` completion of compact smooth one-forms with its exact CCP25 norm;
4. weak `d` and `delta`, obtained by closing proved compact-core operators and characterized distributionally;
5. the `H¹` orthogonal decomposition into the closures of compact exact and coexact forms plus the actual `L²` harmonic one-forms;
6. the `L²` Leray projection onto distributionally coclosed one-forms; and
7. the closed nonnegative self-adjoint Hodge--Stokes operator on the divergence-free carrier, with its form domain, kernel, and resolvent stated in the concrete spaces.

This is the analytic proving ground for the north-star shell theorem. It proves that the repository can move from geometry to a source theorem and then to a PDE operator without replacing the hard analytic step by an interface. It is now left stable.

## Completed phase: genuine smooth shell recovery

Every smooth tangential solenoidal field on the canonical torus is represented globally by a periodic stream function plus the two harmonic flux modes. `canonical_torus_smooth_recovery` now gives an explicit three-dimensional shell field for that entire class at both WBS26 endpoint laws. Componentwise moment normalization makes the weighted transverse identification exact; a single weighted antiderivative supplies the normal component. The result is exactly solenoidal, impermeable at both walls, and satisfies the Navier stress-free or Hodge vorticity-free trace.

`canonical_torus_smooth_recovery_rate` proves that the exact field has the stated universal two-jet, that its squared strong-identification defect has no constant or linear term, and that the endpoint energy has the correct surface zeroth coefficient and a vanishing transverse average at first order. Uniform coefficient bounds for $0<\varepsilon\le1/4$ give the smooth-core estimates

\[
\lVert R_\varepsilon v-E_\varepsilon v\rVert_{H_\varepsilon}^2
\le C\varepsilon^2\lVert v\rVert_{C^1}^2,
\qquad
|Q_\varepsilon(R_\varepsilon v)-Q_0(v)|
\le C\varepsilon^2\lVert v\rVert_{C^2}^2.
\]

The exact construction and proof boundary are in [`thin-shell-convergence.md`](thin-shell-convergence.md). The older nonconstant azimuthal Navier mode remains a closed-integral regression fixture.

## Active phase: concrete varying forms

The actual ambient varying-space layer is now constructed. `CanonicalTorusL2` realizes the surface carrier and every normalized physical shell carrier as Mathlib `Lp` Hilbert quotients on the fixed rescaled cylinder. The exact Jacobian satisfies uniform two-sided measure bounds. The coordinate-constant lift $E_\varepsilon$ and weighted coordinate-flux identification $P_\varepsilon$ are genuine continuous linear maps with thickness-independent norm bounds; representative and integral theorems show that these quotient maps use the same frame factors, Jacobian, and probability-fiber normalization as the smooth recovery $R_\varepsilon$. A concrete sequence $\varepsilon_n\downarrow0$ packages them as a genuinely dependent family, rather than reusing one bulk type.

The phase remains active because its exit condition is larger than the ambient carriers. The remaining work is to close the shell and surface differential operators, take the solenoidal kernels with impermeability encoded in the shell form domains, construct both endpoint closed forms, prove dense embedding into the corresponding solenoidal `L²` carriers, and associate the nonnegative self-adjoint Stokes operators. Those objects must consume the completed $P_\varepsilon$, $E_\varepsilon$, and $R_\varepsilon$ without changing conventions.

## End-to-end dependency

```text
complete measured H²
        |
        v
concrete L² carriers and dense compact cores
        |
        v
closed de Rham/covariant operators + Bochner--Weitzenbock
        |
        v
source-normalized H¹ completion with weak d and delta
        |
        +---------------------------+
        |                           |
        v                           v
L² Hodge sectors              H¹ exact/coexact closures
and Leray projector                 |
        |                           +---------------------+
        |                           |                     |
        v                           v                     v
actual harmonic L²       coexact H¹ form sector   H¹ orthogonal remainder
        |                           |                     |
        +-------------+-------------+                     v
                      |                         proved shifted global theorem
                      v                           for -Delta_H² + 2
        closed nonnegative self-adjoint Hodge--Stokes      |
          with harmonic kernel                             v
                      |                       actual CCP25 H¹ harmonic
                      |                            identification
                      +-------------------+-----------------+
                                          v
                         weak surface PDEs and thin-shell limits
```

## Current checkpoint

| Capability | State | Repository evidence |
| --- | --- | --- |
| Evidence integrity | complete | pinned-source validation, strict Lean axiom audit, placeholder checks |
| M1 atomic source specifications | complete | 35/35 atomic source-proof units have paper-owned Lean signatures and checked dependency routes |
| CZ24 curved-operator census | complete | constructed rough, Hodge, and deformation outputs are pairwise distinct on the hyperbolic witness |
| First thin-shell recovery | complete | exact nonconstant canonical-torus Navier recovery with closed integrals and independent numerical checks |
| Canonical-torus smooth recovery | complete | every smooth solenoidal stream-plus-flux field, both endpoint wall laws, exact divergence/impermeability/identification, and quadratic strong/energy estimates |
| Complete measured `H²` | complete | canonical upper half-plane, Poincare distance, invariant measure, completeness |
| Scalar/one-form `L²` | complete | actual `Lp` quotients, complete Hilbert instances, dense compact smooth cores |
| First-order analytic layer | complete | compact de Rham and covariant derivatives, formal adjoints, closability, closed operators |
| Source one-form `H¹` | complete | concrete completion, dense core, exact norm, continuous weak `d` and `delta`, weak integration by parts, injective `H¹ -> L²` map |
| Hyperbolic Bochner--Weitzenbock | complete | integrated and polarized `N=2`, `k=1`, `a=1` identities on the compact core |
| `L²` Hodge/Leray layer | complete | closed exact/coexact/harmonic sectors, distributional characterization, orthogonal decomposition, contractive idempotent Leray projector |
| Abstract `H¹` orthogonal splitting | complete | exact, coexact, and orthogonal-remainder projectors with uniqueness |
| Hodge--Stokes operator | complete | dense coexact-`H¹` plus harmonic-`L²` form domain, coercive Lax--Milgram resolvent, closed densely defined symmetric nonnegative operator, weak form identity, exact harmonic kernel |
| CCP25 harmonic identification | complete | shifted-core dense range, exact source-harmonic equivalence, canonical harmonic `L² -> H¹` recovery, exact norm, and no-hypothesis three-sector theorem |
| Hodge--Stokes/source compatibility | complete | continuous linear equivalence with full divergence-free source `H¹`, intertwining the `L²` embedding and weak Hodge derivative |

The source `H¹` harmonic subspace was constructed first as an orthogonal remainder. It is now proved to map bijectively onto the actual distributional `L²` harmonic sector, so the canonical specialization may use the source terminology without qualification. The separately specified general CCP25 theorem for arbitrary dimension, form degree, and curvature scale is not claimed.

## Completed global analytic package

The CCP25 closure is one coherent complete-manifold theorem with two consequences.

For `u` in the `H¹` orthogonal remainder, the formalization now proves the precise weak equations

\[
\langle \delta u,(\delta d+2)\varphi\rangle_{L^2}=0,
\qquad
\langle d u,(d\delta+2)\psi\rangle_{L^2}=0
\]

for compact smooth scalar and top-degree tests. In dimension two the two displayed shifted core operators are proved equal. Consequently, density of the compact-core range of

\[
-\Delta_{\mathbb H^2}+2
\]

forces both `d u` and `delta u` to vanish and closes the canonical specialization of CCP25 Proposition 4.3. `HyperbolicScalarEnergy` proves the required dense range by an ambient Sobolev localization, exact weak energy identity, intrinsic cutoff estimate, and smooth outer-cutoff exhaustion; it is not an assumed interface.

For the reverse direction, `HyperbolicCCP25` combines the proved dense source embedding with compatible source and `L²` harmonic projections. The map from the source harmonic remainder to actual harmonic `L²` has dense range, while the exact identity

\[
\|u\|_{H^1}^2=2\|u\|_{L^2}^2
\]

makes that range closed. It is therefore onto and supplies a canonical inverse `hyperbolicHarmonicL2ToH1`, including the exact recovered norm. The public theorem `hyperbolicH1_exact_add_coexact_add_actualHarmonic` states the resulting no-hypothesis `N=2`, `k=1`, `a=1` three-sector decomposition with an actual distributional harmonic summand.

## Hodge--Stokes completion

The Hodge--Stokes construction no longer waits on the CCP25 identification. Its concrete form domain is

\[
V_{\mathrm{HS}}=overline{\delta C_c^\infty}^{\,H^1}\oplus L^2_{\mathrm{harm}},
\]

embedded densely into

\[
H_{\mathrm{div}}=\overline{\delta C_c^\infty}^{\,L^2}\oplus L^2_{\mathrm{harm}}.
\]

The harmonic summand is included directly with zero Hodge energy, while the coexact summand uses the source-normalized `H¹` completion. This produces the closed quadratic form

\[
a(u,v)=\langle d u,d v\rangle_{L^2}+\langle \delta u,\delta v\rangle_{L^2}
\]

restricted to distributionally coclosed one-forms. `Operators.HyperbolicHodgeStokes` now provides:

- the form-domain Hilbert carrier and its dense continuous embedding into divergence-free `L²`;
- the Lax--Milgram resolvent of `I+A`;
- the associated densely defined operator as a genuine `LinearPMap`/closed operator;
- closedness, nonnegativity, and symmetry;
- identification of its kernel with harmonic `L²` one-forms; and
- compatibility with the previously constructed Leray projector.

The operator is recovered from the injective dense-range resolvent as a genuine `LinearPMap`; its graph is characterized by `R(u+v)=u`, which proves closedness. Its quadratic value is exactly the squared weak Hodge derivative, and its kernel is exactly the actual distributional harmonic `L²` sector. The Leray projector fixes the whole ambient divergence-free carrier.

`HyperbolicHodgeStokesCCP25` now completes the compatibility role. It constructs a continuous linear equivalence from the independently defined form domain to the source's full divergence-free `H¹` carrier. One intertwining theorem proves that its image in concrete `L²` is exactly the pre-existing Hodge--Stokes embedding; another proves that its weak Hodge derivative is exactly the pre-existing form derivative. Thus the global regularity theorem identifies the source domain without retrofitting the operator construction.

## What this unlocks

The completed hyperbolic operator package gives the repository a checked analytic vertical slice from Riemannian geometry through the exact source Sobolev decomposition and weak operator. It supports source-faithful formulations of the hyperbolic stationary and evolutionary problems in CC13, CC15, and CC21 and supplies a proved reference model for pressure elimination, harmonic modes, energy identities, and coercivity.

For the thin-shell program, it supplies the functional-analytic pattern needed after the completed smooth-core recovery theorem: closed form domains, solenoidal projection, form/operator association, resolvents, and honest separation of kernels. The active thin-shell objective is to realize those structures on the weighted canonical shell, then prove the full M2 density extension and the M1 compactness theorem. The hyperbolic theorem does not prove the shell limit, but it removes the ambiguity about what the limiting Hilbert spaces and operators must be.

## Thin-shell program after the analytic benchmark

The arbitrary smooth-core recovery theorem is implemented on the canonical torus at both endpoints. The remaining shell program is organized by whole capabilities:

1. actual varying weighted shell and surface Hilbert carriers, the exact form domains, and the identification/lifting maps used by both Mosco halves;
2. extension of the smooth recovery by form-core density and a diagonal argument;
3. thickness-uniform Korn/Gaffney estimates modulo the correct kernel, compactness, and the Mosco liminf inequality;
4. association of the shell and surface forms with nonnegative self-adjoint operators;
5. strong resolvent, compact-time semigroup, fixed-mode spectral convergence, and the high-mode no-pollution statement; and
6. generalization of the complete canonical-torus theorem to the source torus-type surface-of-revolution class.

No general WBS26 status is claimed before both Mosco halves and the operator association are proved on the source geometry.

## Completion discipline

Every claimed milestone must end with focused Lean builds, a full root build, the strict axiom audit, placeholder scans, claim-ledger validation, and `make check`. Numerical convergence remains numerical evidence. Conditional theorems remain conditional. The roadmap advances only when the public theorem statement matches the source claim and all hypotheses visible in that statement are actually discharged on the concrete geometry.
