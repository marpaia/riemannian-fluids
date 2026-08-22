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
- the one-form codifferential;
- the exact codifferential correction;
- the exterior derivative of a lowered field, its degree-two codifferential trace, and the
  constructed Hodge Laplacian.

### Conditional theorem

A conditional theorem proves a conclusion from hypotheses displayed in its type.  This role captures mathematical reductions whose geometric or analytic inputs have an independent formalization path.

`ccd17_positive_full`, for example, derives the full deformation/Hodge identity from `WeitzenbockIdentity` and `SymmetricGradientIdentity`.  `energy_exponential_decay_of_coercive_dissipation` derives the exponential decay bound of the negative-curvature energy argument (Wang--Braunstein, arXiv:2605.17502v2, Theorem 6.1) from an explicit energy identity and coercivity estimate via Grönwall comparison; existence, uniqueness, pressure recovery, and the two analytic inputs themselves remain open.

### Source theorem

A source theorem instantiates the geometry, function spaces, boundary conditions, and analytic estimates of a literature result and proves its stated conclusion. The formalization ledger records progress for every atomic formal target, including geometric identities and the obligations obtained by splitting compound source theorems.

The machine-readable corpus classification further separates source results, source specializations, project theorems, source-labeled heuristics, and computational evidence gates. Stable public mappings live under `RiemannianFluids.Literature.<paper>`; those declarations delegate to reusable implementation modules without weakening or broadening their theorem types.

## The complete measured hyperbolic foundation

`Geometry.Instances.HyperbolicPlane` now reuses Mathlib's canonical upper-half-plane carrier. This places the repository's explicit Poincare Riemannian metric, Levi--Civita connection, and curvature proofs on the same type as Mathlib's genuine hyperbolic distance. Mathlib proves this metric space proper, so `CompleteSpace HyperbolicPlane` is an actual inferred instance. `Geometry.Instances.HyperbolicPlaneMeasure` names the invariant measure

\[
d\mu_{\mathbb H^2}=\frac{dx\,dy}{y^2}
\]

as `hyperbolicVolume`, exposes its weighted-Lebesgue formula, and packages the geometry as `completeRiemannianManifold : CompleteBoundarylessRiemannianManifoldData`.

`FunctionSpaces.HyperbolicL2` introduces the first concrete noncompact Hilbert carriers:

\[
\texttt{HyperbolicScalarL2}=L^2(\mathbb H^2,\mathbb R),
\qquad
\texttt{HyperbolicOneFormL2}=L^2(\mathbb H^2,\mathbb R^2).
\]

The second equality is geometric rather than a coordinate-norm shortcut. At each point, real Riesz duality sends a cotangent vector to its representing tangent vector, and the proved orthonormal frame $(y\partial_x,y\partial_y)$ sends that vector isometrically to `EuclideanSpace R (Fin 2)`. The forward and inverse maps are mutually inverse, and `norm_oneFormComponentsAt` proves exact equality between the component norm and the intrinsic cotangent operator norm. Raw intrinsic one-forms therefore enter the actual `Lp` quotient through `oneFormToL2` once their orthonormal component field satisfies `MemLp`.

The module also defines compactly supported smooth scalar and orthonormal-component cores as real modules under pointwise operations. Their common quotient inclusion `hyperbolicSmoothCompactToL2` is a linear map. Mathlib's manifold smoothing theorem, local finiteness of hyperbolic volume, and the `Lp` quotient metric are combined to prove that this linear map has dense range in `hyperbolicSmoothCompactScalar_dense` and `hyperbolicSmoothCompactOneForm_dense`. Completeness is supplied by the actual `Lp` `CompleteSpace` instances and is consumed by `hyperbolicScalarL2_complete` and `hyperbolicOneFormL2_complete`.

The concrete stack now continues beyond these carriers. `HyperbolicFirstOrder`, `HyperbolicIntegrationByParts`, and `HyperbolicSobolev` construct compact de Rham and covariant operators, prove their formal-adjoint identities in the invariant measure, and close them as genuine densely defined operators. `HyperbolicBochner` proves the integrated and polarized `N=2`, `k=1`, `a=1` Bochner--Weitzenbock identities. `HyperbolicH1` realizes the source one-form `H¹` completion with norm

\[
\|u\|_{H^1}^2=2\|u\|_{L^2}^2+\|d u\|_{L^2}^2+\|\delta u\|_{L^2}^2,
\]

continuous weak `d` and `delta`, weak integration by parts, a dense compact core, and an injective map into one-form `L²`.

`HyperbolicHodgeDecomposition` constructs the exact and coexact `H¹` closures and their orthogonal remainder. `HyperbolicL2HodgeDecomposition` separately constructs the actual distributional harmonic `L²` sector, proves the `L²` exact/coexact/harmonic splitting, and defines the contractive idempotent Leray projector onto distributionally coclosed forms.

`Operators.HyperbolicHodgeStokes` uses the Hilbert form domain

\[
\overline{\delta C_c^\infty}^{\,H^1}\oplus L^2_{\mathrm{harm}}
\]

and its dense embedding into divergence-free `L²`. Lax--Milgram constructs the resolvent of `I+A`; the range of that resolvent is the domain of a genuine `LinearPMap`. The reusable `Analysis.ResolventGeneratedOperator` theorem uses the graph identity `R(u+v)=u` for closedness and the adjoint-domain equation `R(y+A†y)=y` for maximality, proving that every injective symmetric bounded resolvent generates a self-adjoint operator. The concrete formalization therefore proves closedness, self-adjointness, nonnegativity, the weak Hodge form identity, compatibility with the Leray projector, and the exact kernel characterization

\[
Au=0\quad\Longleftrightarrow\quad u\in L^2_{\mathrm{harm}}.
\]

`HyperbolicScalarEnergy` closes the complete-manifold shifted elliptic input. It transports compact hyperbolic tests to ambient Schwartz functions, applies the proved Euclidean Sobolev and distributional Leibniz bridge to obtain the exact localized weak energy identity, bounds the intrinsic cutoff error, and sends the smooth outer-cutoff exhaustion to one. The resulting theorem `weakScalarShiftedHarmonic_eq_zero` says that the `L²` weak kernel of `-\Delta_{\mathbb H^2}+2` is trivial, and `hyperbolicScalarShiftedHodgeCoreL2_denseRange` converts this into dense range of the compact shifted core.

`HyperbolicCCP25` uses that dense range to prove that every source `H¹` orthogonal remainder is distributionally harmonic. Compatibility of the source and `L²` orthogonal projectors makes the induced harmonic map dense, while the exact identity `||u||_H1² = 2 ||u||_L2²` makes its range closed. It is therefore bijective onto the full distributional harmonic `L²` sector. The inverse `hyperbolicHarmonicL2ToH1` gives every actual harmonic form its canonical source representative and exact norm, and `hyperbolicH1_exact_add_coexact_add_actualHarmonic` states the no-hypothesis `N=2`, `k=1`, `a=1` specialization of CCP25 Theorem 1.3.

Finally, `Operators.HyperbolicHodgeStokesCCP25` identifies the independently constructed Stokes form domain with the source's full divergence-free `H¹` carrier by a continuous linear equivalence. Its intertwining theorems prove equality with the pre-existing `L²` embedding and weak Hodge derivative. This closes the canonical hyperbolic benchmark without changing the operator construction. The general CCP25 theorem for arbitrary dimension, form degree, and curvature scale remains a separately specified claim.

## The canonical-torus varying `L²` foundation

`FunctionSpaces.CanonicalTorusL2` realizes the ambient spaces required by WBS26 on actual Mathlib quotients. The mid-surface is `AddCircle (2*pi) × AddCircle (2*pi)` with area measure $(2+\cos\theta)\,d\theta\,d\phi$. Every shell is pulled back to the fixed cylinder with probability normal fiber $[-1,1]$, and its normalized physical measure is the product reference measure weighted by

\[
J_\varepsilon(\theta,z)
=(1+\varepsilon z)
\left(1+\varepsilon z\frac{\cos\theta}{2+\cos\theta}\right).
\]

For $0<\varepsilon\le1/4$, the formalization proves $9/16\le J_\varepsilon\le25/16$ and therefore two-sided domination between the reference and physical measures. The resulting surface and shell `Lp` spaces are complete Hilbert carriers, and identity-on-representative continuous maps compare every shell with the fixed cylinder.

`Analysis.LpMultipliers` packages a strongly measurable, essentially uniformly bounded family of continuous fiber maps as a continuous operator between Bochner `Lp` quotients. Applying it to the two parallel-surface frame factors constructs the coordinate-constant lift `constantCoordinateLiftL2`. Applying it to the reciprocal factors constructs the test lift whose Hilbert adjoint is `fluxIdentifyL2`. The representative theorems expose both maps pointwise, while `inner_fluxIdentifyL2_integral` exposes the exact weighted integral pairing. Uniform norm bounds hold for both maps throughout the admissible thickness range. Finally, `thicknessAt` tends to zero and produces the genuinely dependent family `ShellFamily`; this is why `HilbertQuadraticFormData` now accepts `Bulk : Nat -> Type` rather than silently reusing one bulk type.

This layer does not yet claim a solenoidal shell form, Mosco convergence, or a Stokes operator. The next analytic construction must close the surface and shell differential operators, impose the divergence and impermeability constraints in their graph carriers, and build the two endpoint closed forms on those exact spaces.

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
| \(\nabla^2 v\) | `secondCovariantDerivativeAt` | continuous bilinear second covariant derivative on \(T_xM\) |
| Ricci commutation | `secondCovariantDerivativeAt_sub_swap` | \(\nabla^2v(X,Y)-\nabla^2v(Y,X)=R(X,Y)v\) for torsion-free connections |
| \(L_{\mathrm{rough}}=\nabla^*\nabla\) in divergence form | `roughLaplacianAt` | \(-\operatorname{tr}_g\nabla^2v\) as an intrinsic trace |
| \(L_{\mathrm{Def}}=2\operatorname{Def}^*\operatorname{Def}\) in divergence form | `deformationLaplacianTestedAt` | \(-2(\operatorname{div}_g\operatorname{Def}v)\) tested against tangent vectors |
| divergence commutation | `divergenceCommutationAt_of_leviCivita` | \(\operatorname{tr}\nabla^2v(w,\cdot)=d(\operatorname{div}v)(w)\), proved via metric-dual frames |
| constructed incompressible comparison | `ccd17_divfree_def_rough_constructed` | \(L_{\mathrm{Def}}u=L_{\mathrm{rough}}u-\operatorname{Ric}\) proved from the connection |
| constructed \(d(u^\flat)\) | `exteriorDerivativeValueAt` | antisymmetrized lowered covariant derivative; its connection-free bracket formula is the proved `exteriorDerivativeValueAt_eq_mlieBracket` |
| constructed \(d_2^* d_1(u^\flat)\) | `hodgeCoexactHalfTestedAt` | intrinsic traces of \(\nabla^2 u\), tied to \(d(u^\flat)\) by `sum_exteriorDerivativeCovariantDerivativeAt_extend` |
| constructed \(L_{\mathrm{Hodge}}\) | `hodgeLaplacianConstructedTestedAt` | sum of the constructed exact and coexact de Rham halves |
| Weitzenböck, proved | `weitzenbock_constructedAt` | \(L_{\mathrm{Hodge}}(u^\flat)(w)=\langle L_{\mathrm{rough}}u,w\rangle+\mathrm{Ric}(w,u)\) from the connection |
| fully constructed incompressible comparison | `ccd17_divfree_def_hodge_constructed` | \(L_{\mathrm{Def}}u=L_{\mathrm{Hodge}}u-2\,\mathrm{Ric}\) with every operator constructed |

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

`Operators.ConstructedLaplacians` constructs \(L_{\mathrm{rough}}\) and \(L_{\mathrm{Def}}\)
from the connection as traces of the pointwise second covariant derivative and proves, for
divergence-free fields,

\[
\langle L_{\mathrm{Def}}u,w\rangle
=\langle L_{\mathrm{rough}}u,w\rangle-\mathrm{Ric}(w,u).
\]

`Operators.ConstructedHodge` constructs the Hodge side.  The exterior derivative on lowered
fields is the antisymmetrized lowered covariant derivative
\(d(u^\flat)(X,Y)=\langle\nabla_X u,Y\rangle-\langle\nabla_Y u,X\rangle\), and the proved
bracket formula
\(d(u^\flat)(X,Y)=X\langle u,Y\rangle-Y\langle u,X\rangle-\langle u,[X,Y]\rangle\)
identifies it with the intrinsic, connection-independent exterior derivative.  The Hodge
Laplacian is assembled from its two de Rham halves — \(d_0 d_1^*(u^\flat)(w)=-d(\mathrm{div}\,u)(w)\)
and the degree-two codifferential of \(d(u^\flat)\) in intrinsic trace form — and the
Weitzenböck identity

\[
L_{\mathrm{Hodge}}(u^\flat)(w)
=\langle L_{\mathrm{rough}}u,w\rangle+\mathrm{Ric}(w,u)
\]

is proved (`weitzenbock_constructedAt`), not assumed.  Combining the two proved identities
yields CCD17 equation (1.3) with every operator constructed, and on divergence-free fields the
central identity \(L_{\mathrm{Def}}u=L_{\mathrm{Hodge}}u-2\,\mathrm{Ric}\)
(`ccd17_divfree_def_hodge_constructed`).  The Ricci term is the trace-of-first-slot contraction
\(\mathrm{Ric}(w,u)=\mathrm{tr}(X\mapsto R(X,w)u)\), whose identification with
\(\mathrm{Ric}(u,w)\) would additionally require the first Bianchi identity.

## The CZ24 constructed census

`Operators.ConstructedLaplacians` and `Operators.ConstructedHodge` first raise the independently
constructed deformation and Hodge covectors by finite-dimensional Riesz duality.  The theorems
`inner_deformationLaplacianAt` and `inner_hodgeLaplacianConstructedAt` prove that pairing those
vectors recovers the original tested definitions.  The scalar comparison identities therefore
lift to the vector equalities `deformationLaplacian_rough_ricci_comparisonVectorAt_of_divergenceFree`
and `weitzenbock_constructedVectorAt`.

`Viscosity.CurvatureComparison` combines these constructions into
`constructedCandidateOutputs_pairwiseDistinct_of_ricciWitness`.  For a divergence-free field,
write \(\rho=\langle L_{\mathrm{rough}}u,w\rangle\) and
\(r=\mathrm{Ric}(w,u)\).  The three constructed tests are

\[
\rho-r,\qquad \rho,\qquad \rho+r,
\]

so a nonzero Ricci pairing makes them pairwise distinct.

`Geometry.Instances.HyperbolicPlaneCensus` realizes that witness on the Poincaré half-plane.
The horizontal field \(u=\partial_x\) is divergence-free, the test vector is
\(w=\partial_x\), and the proved curvature calculation gives
\(r=\mathrm{Ric}(\partial_x,\partial_x)=-y^{-2}\ne0\).  Consequently
`cz24_census_hyperbolic` proves the three actual constructed tangent-vector outputs pairwise
distinct at every point, without geometric hypotheses supplied by the caller.

This pointwise output witness is enough to disprove universal equality of the three differential
constructions.  The separate `CandidateOperatorsPairwiseDistinct` predicate compares globally
bundled section operators and still depends on the interface-level `OneFormHodgeData`
representation; that broader packaging is not needed for the CZ24 counterexample.

## Formal status of the comparison

| Component | Status |
| --- | --- |
| smooth musical maps and inverse laws | constructed |
| covariant differentiation and regularity loss | constructed |
| field-level curvature commutator and alternating law | constructed |
| pointwise continuous curvature in the two direction slots | constructed under local connection regularity |
| local connection-regularity bridge | discharged from mathlib's `C¹` connection class on a smooth Hausdorff atlas |
| `C²` tensoriality in the differentiated-field slot | proved under local connection regularity and a `C³` atlas |
| continuous trilinear curvature tensor `R(X,Y)Z` on `T_xM` | constructed under the same hypotheses |
| pointwise Ricci trace and metric-raised action | constructed from `R(X,Y)Z`; orthonormal-frame formula proved |
| bounded Ricci contraction on curvature model tensors | constructed; its Euclidean model-space map is smooth |
| global Ricci form and raised action | constructed under `HasConnectionRicciContractionRegularity` and smooth metric data |
| scalar curvature | constructed as the smooth trace of the raised Ricci field |
| sectional curvature | constructed pointwise as the normalized contraction of `R(X,Y)Y` against `X`; geometric use requires a nonzero Gram determinant |
| connection-derived `RiemannianCurvatureData` | all four fields derived by `connectionRiemannianCurvatureDataOfRegularCurvature` |
| smooth `RicciData` adapter | `RicciData.ofRegularConnection` discharges the older standalone `HasConnectionRicciRegularity` input |
| Levi--Civita restriction locality along an immersion | proved for equality of pulled-back differentiable germs (`LeviCivitaConnection.eq_on_mfderiv_of_comp_eventuallyEq`) |
| pointwise submanifold `∇ᴮ II` | constructed as a continuous trilinear map into the actual kernel-normal fiber; symmetry in the `II` slots proved |
| uncontracted and contracted Codazzi | proved from the differentiated Gauss identity with the CCG25 curvature-slot convention |
| actual-fiber CCG25 Bochner and Hodge Gauss formulas | proved from one actual `C²` source field and its chosen `C²` ambient extension; the intrinsic rough value and ambient normal Hessian trace are identified with constructed operators, one explicit tangent-Hessian identity completes the ambient rough bridge, and first Bianchi plus curvature metric-skewness prove the Ricci symmetry needed for both constructed Hodge values |
| smooth tubular realization of the remaining CCG25 data | open: construct the compatible extension package, its differentiated regularity, and the mean-curvature first jet, then derive the varying-field tangent-Hessian trace |
| trace, divergence, and divergence-free predicate | constructed |
| tensor transpose, symmetrization, and `Def` | constructed |
| metric Lie-derivative identity \(L_u g = 2\operatorname{Def}u\) | proved from metric compatibility and torsion-freeness |
| \(d^*(u^\flat)=-\operatorname{div}u\) | proved |
| vanishing of \((d d^*(u^\flat))^\sharp\) on divergence-free fields | proved |
| exterior derivative \(d(u^\flat)\) on lowered fields | constructed as the antisymmetrized lowered covariant derivative; connection-free bracket formula proved (`exteriorDerivativeValueAt_eq_mlieBracket`) |
| degree-two codifferential of \(d(u^\flat)\) | constructed as intrinsic traces of \(\nabla^2u\); orthonormal-frame characterization against \(d(u^\flat)\) proved |
| bundled `OneFormHodgeData` (degree-one `d` and degree-two `d*` on arbitrary two-forms, `SmoothDifferentialForm` packaging) | interface data |
| \(2\operatorname{Def}^*\operatorname{Def}\) from a formal adjoint | interface data |
| second covariant derivative, tensorial in both direction slots | proved under local connection regularity |
| Ricci commutation \(\nabla^2u(X,Y)-\nabla^2u(Y,X)=R(X,Y)u\) | proved for torsion-free connections |
| \((\nabla_X\operatorname{Def}u)(Y,Z)=\tfrac12(\langle\nabla^2u(X,Y),Z\rangle+\langle\nabla^2u(X,Z),Y\rangle)\) | proved from metric compatibility |
| \(L_{\mathrm{rough}}\) and \(L_{\mathrm{Def}}\) in divergence form | constructed as intrinsic traces of \(\nabla^2u\) |
| divergence commutation \(\operatorname{tr}\nabla^2u(w,\cdot)=d(\operatorname{div}u)(w)\) | proved via metric-dual local frames |
| symmetric-gradient identity in divergence form | proved (`deformationLaplacian_rough_ricci_comparisonAt`) |
| constructed divergence-free comparison \(L_{\mathrm{Def}}u=L_{\mathrm{rough}}u-\operatorname{Ric}\) | proved (`ccd17_divfree_def_rough_constructed`) |
| constructed Hodge Laplacian \(L_{\mathrm{Hodge}}=d_0d_1^*+d_2^*d_1\) on \(u^\flat\) | constructed from both de Rham halves as a tested covector and its Riesz-representative tangent vector (`hodgeLaplacianConstructedTestedAt`, `hodgeLaplacianConstructedAt`) |
| Weitzenböck identity | proved for the constructed operators (`weitzenbock_constructedAt`); remains a displayed hypothesis of the bundled interface theorem `ccd17_divfree_def_hodge` |
| fully constructed divergence-free Hodge-form comparison \(L_{\mathrm{Def}}u=L_{\mathrm{Hodge}}u-2\,\mathrm{Ric}\) | proved (`ccd17_divfree_def_hodge_constructed`) |
| constructed rough/Hodge/deformation pointwise output census from a nonzero Ricci pairing | proved (`constructedCandidateOutputs_pairwiseDistinct_of_ricciWitness`) |
| concrete CZ24 census on the hyperbolic half-plane | actual tangent-vector outputs proved pairwise distinct at every point (`HyperbolicPlane.cz24_census_hyperbolic`) |
| full and divergence-free Hodge-form comparison on bundled section operators | proved from the displayed hypotheses (`ccd17_divfree_def_hodge`) |

This table identifies the exact formal boundaries.  `ccd17_divfree_def_hodge_constructed` proves
the paper's central divergence-free identity with every operator — both de Rham halves of the
Hodge Laplacian, the deformation Laplacian, and the Ricci contraction — constructed from the
packaged Levi-Civita connection under the curvature-regularity bridge and a `C³` atlas.  What
remains assumed there: the Levi-Civita connection is chosen data (existence and uniqueness from
the metric are not derived), the curvature-regularity bridge is a pointwise hypothesis
(dischargeable on smooth Hausdorff manifolds by `hasConnectionCurvatureRegularityAt_of_contMDiff`),
and the Ricci slot order is the trace-of-first-slot convention.  The constructed deformation
and Hodge covectors now have canonical pointwise Riesz-representative vector outputs;
`ccd17_divfree_def_hodge` remains the interface statement at the level of bundled section
operators, where `OneFormHodgeData` still awaits a standalone degree-two
codifferential on arbitrary two-forms and the alternating-form packaging of \(d(u^\flat)\).

## Dependency order

```text
smooth sections and manifold models
  -> complete measured hyperbolic geometry
  -> scalar and intrinsic one-form L2 carriers; dense smooth compact cores
  -> connection and musical maps
  -> pointwise curvature tensor and bounded Ricci contraction
  -> global Ricci and scalar fields; pointwise sectional normalization
  -> scalar and vector calculus
  -> tensor symmetry and deformation strain
  -> differential forms and codifferential
  -> Hodge, rough, Ricci, and deformation operators
  -> geometric comparison identities
  -> incompressible specialization
  -> constructed pointwise operator census
  -> concrete hyperbolic witness
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

- Czubak, *In Search of the Viscosity Operator on Riemannian Manifolds*, Notices of the AMS
  71(1), DOI [10.1090/noti2840](https://doi.org/10.1090/noti2840).
- Chan, Czubak, and Disconzi, *The formulation of the Navier--Stokes equations on Riemannian manifolds*, arXiv:1608.05114v2: <https://arxiv.org/abs/1608.05114v2>.
- Versioned source metadata and claim locators: [`../claims/registry.json`](../claims/registry.json).
- Literature synthesis: [`literature.md`](literature.md).
