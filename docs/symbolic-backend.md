# The symbolic backend

`riemannian_fluids.symbolic` is the exact computational layer of the Python implementation.  Where the JAX backend evaluates geometry at sampled points and the FEniCSx backend discretizes weak problems, the symbolic backend produces closed forms, certified verdicts, and chart-level identities in SymPy.  All three backends share the `analysis-positive-v1` conventions; the symbolic layer states its copy in `riemannian_fluids/symbolic/conventions.py`.

## Design principles

**Structured entry.**  Fields enter through constructors whose geometric properties hold by construction: a `CoexactField` stores a stream function and is divergence-free as a theorem of its definition, a `RotationKillingField` verifies at construction that the metric is invariant along its axis.  The vector-field hierarchy is closed; solver signatures consume capability unions such as `SolenoidalField`, so unsupported usage fails in the type checker and again at runtime.

**Certified results.**  Every solver returns a typed certificate rather than a bare expression:

- `ExactCertificate`: a closed form, with the positivity assumptions it consumed;
- `FiniteCertificate`: convergence proven without a closed form;
- `DivergentCertificate`: integrability refuted, with the failing endpoint;
- `UnresolvedCertificate`: an honest refusal when the answer depends on undecided parameter relations.

Certificates compose by weakest link and no code path upgrades a grade.  Results also carry a `DerivationLedger` recording each transformation with before/after expression sizes.

**The cross-check invariant.**  Every symbolic quantity with a numeric twin is compared against the JAX implementation at deterministic random points in float64 (`riemannian_fluids/symbolic/crosscheck.py`).  A disagreement is an error, not a warning: it means the two backends disagree about the mathematics.

## Module map

| Module | Contents |
| --- | --- |
| `conventions.py` | sign and orientation conventions shared with the numeric backend |
| `charts.py` | symbolic coordinate charts with validated volume densities |
| `kernel.py` | Christoffel symbols, curvature, strain, and the viscosity operators |
| `simplify.py` | staged size-guarded simplification and the three-valued zero test |
| `crosscheck.py` | float64 comparison against the JAX backend |
| `fields.py` | the closed structured-field hierarchy |
| `certificates.py` | certificate grades and derivation ledgers |
| `series.py` | truncation-tracked series in a small parameter |
| `energy/` | domains, radial reduction, certified integration, identities |
| `shells/` | tube charts, two-wall ansatz fields, thin-shell limits, and exact recovery certificates |

## The energy-integral solver

`energy_integral(density, chart, domain)` evaluates

```math
\int_{\Omega} \rho \; \mathrm{dV}
```

over radial domains (full chart, geodesic ball, exterior, annulus) by attaching the chart's declared volume density, reducing out the angular coordinate by symmetry or explicit integration, and resolving the radial integral in tiers: exact closed form first, then endpoint comparison tests that prove finiteness or divergence.  The comparison tests are rigorous implications for the solver's input class, nonnegative energy densities.  `verify_numerically` confirms exact results against high-precision quadrature.

The identity engine (`energy/identities.py`) exposes the divergence form of the deformation energy,

```math
\langle L_{\mathrm{Def}} u, u \rangle \;=\; 2\,\lvert \mathrm{Def}\, u \rvert^2 \;-\; \mathrm{div}\, F,
\qquad F^i = 2\, \mathrm{Def}^i{}_j\, u^j,
```

with the flux `F` available as data, so the boundary term of every integration by parts is an inspectable expression rather than a casualty.  `verify_divfree_def_hodge` checks the divergence-free comparison

```math
L_{\mathrm{Def}} \;=\; L_{\mathrm{Hodge}} \;-\; 2\,\mathrm{Ric}
```

componentwise on a chart; applied to a coexact field with a generic stream function it verifies the identity for every stream on the chart, which the test suite does on the sphere, the hyperbolic plane with symbolic curvature, and the torus of revolution.

## The thin-shell solver

`EpsSeries` (`series.py`) is a graded truncated series: arithmetic can only lose tracked order, and reading a coefficient beyond it raises `TruncationError`, so a silently dropped term is unrepresentable.  Exact polynomials, such as the codimension-one tube Jacobian, carry no unknown tail.

`ShellChart` (`shells/tube.py`) pairs a surface chart with its three-dimensional normal tube: the shell metric, the sigma-dependent shape operator of the level surfaces, and the exact Jacobian in the numeric backend's `det(I - sigma S)` convention.  `two_wall_rotational_field` imposes the invariant wall relation

```math
\partial_\sigma U \;=\; 2\alpha\, S(\sigma)\, U
```

at both walls when the ansatz is constructed and re-verifies the residual through the tracked order.

`pairing_eigenvalue` computes the transverse-averaged operator pairing per unit squared field and expands it in the thickness.  On the unit sphere its limit reproduces the wall-selected rotational eigenvalue

```math
\lambda_\alpha \;=\; 6\alpha - 4\alpha^2,
```

in exact agreement with the interpolating surface family

```math
L(\alpha) \;=\; L_{\mathrm{Def}} + 2\alpha\,\mathrm{Ric} + 4\alpha(1-\alpha)\,S^2
```

applied to the rotational mode, and with the numeric `interpolating_viscosity` operator at sampled wall parameters.  The endpoints are the Navier/stress-free wall (`alpha = 0`, zero dissipation on the rigid rotation) and the Hodge/vorticity-free wall (`alpha = 1`, eigenvalue 2, the exact resolvent coefficient used by the `wall-selection` study).

### Smooth-core recovery at both endpoints

`canonical_torus_smooth_solenoidal_field` parameterizes the full smooth solenoidal class on $T(2,1)$ by an arbitrary periodic stream function and two constant flux modes. `canonical_torus_smooth_recovery` then builds an exact shell field for either `RecoveryEndpoint.NAVIER` or `RecoveryEndpoint.HODGE`. It solves the two wall equations with an $\varepsilon$-dependent quadratic tangential profile, normalizes each tangential flux moment exactly, and defines the normal component by a weighted antiderivative. The constructor fails closed unless surface and shell divergence, both wall traces, both endpoint wall equations, the antiderivative identity, the upper-wall compatibility condition, and the weighted transverse identification all simplify to zero.

`canonical_torus_smooth_recovery_rate` connects that exact rational field to its universal two-jet. It proves equality of all component coefficients through order two, vanishing of the leading fast endpoint tensor, equality of the zeroth shell and surface energy densities, cancellation of the transversely averaged linear energy coefficient, and absence of constant or linear terms in the squared strong-recovery defect. These exact identities, together with uniform denominator bounds for $0<\varepsilon\le1/4$, give the smooth-core $O(\varepsilon^2)$ energy estimate and strong varying-space convergence. The arbitrary undefined stream derivatives are replaced injectively by independent jet symbols, so the identity is checked coefficientwise for every smooth input rather than sampled from a finite family.

This is the constructive content of `WBS26-smooth-recovery-canonical-torus`. The remaining M2 density extension and all of M1 belong to the analytic carrier/form program, not to this symbolic certificate.

### Integrated Navier regression

`canonical_navier_torus_recovery` constructs the first full form-domain recovery family rather than only an operator pairing. On the torus with major radius $R=2$ and minor radius $a=1$, it lifts the nonconstant solenoidal surface field $u=\sin(\theta)\partial_\phi$ unchanged through the shell. The constructor fails unless exact calculation proves three-dimensional solenoidality, impermeability and stress-free conditions at both walls, exact normalized transverse identification, and convergence of normalized mass and deformation energy.

For shell half-thickness $0<\varepsilon<1$, the certificate returns

\[
Q_0(u)=25\pi^2,
\qquad
Q_\varepsilon(U_\varepsilon)
=\frac{\pi^2}{\varepsilon}\left(9\varepsilon-8\log(1-\varepsilon)+8\log(1+\varepsilon)\right),
\qquad
\lim_{\varepsilon\downarrow0}\frac{Q_\varepsilon-Q_0}{\varepsilon^2}=\frac{16\pi^2}{3}.
\]

It also returns $\|u\|_{L^2}^2=19\pi^2$ and the normalized shell mass $19\pi^2+3\pi^2\varepsilon^2$. The symbolic divergence and energy density are independently evaluated by the JAX covariant-calculus implementation. This narrower certificate remains useful because it carries fully integrated closed forms and an independent backend cross-check.

## Verification

The suite in `python/tests/test_symbolic_*.py` enforces four kinds of guarantee: cross-backend agreement for every operator on every chart, golden curvature and eigenvalue identities, refutation of deliberately wrong signs (a flipped Ricci term must fail, not merely go unproven), and truncation discipline (a seeded dropped term must raise).

## Worked examples

[`python/examples/`](../python/examples/) contains narrated end-to-end computations for both solvers:

```sh
pixi run --locked symbolic-examples
```
