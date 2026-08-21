# Thin-shell convergence: numerical gates and proof obligations

## End-to-end theorem target

The governing deliverable is a concrete WBS26 Theorem 4.5/Corollary 4.6 package, first on the canonical torus of revolution and then on the source's torus-type revolution class. For both the Navier and Hodge wall conditions, the same package must construct the weighted shell and surface Hilbert spaces, the solenoidal closed forms, their associated nonnegative self-adjoint operators, the varying-space identification maps, both Mosco conditions, and the resulting resolvent, compact-time semigroup, and source-scoped spectral convergence. The smooth-core construction below closes the constructive heart of M2 on the canonical torus; it is not yet the full form-domain or Mosco theorem.

The resolved-shell program has two distinct goals.  The numerical goal is to show that a stated volume discretization behaves like its stated surface target under separated resolution studies.  The analytic goal is to prove convergence of the continuous shell forms before discretization.  Passing the first goal is evidence for an implementation; it is not the second goal.

## Implemented wall forms

For impermeable shell fields, the two source endpoint energies are

\[
Q_\varepsilon^{\mathrm{Navier}}(U)=2\int_{\Sigma_\varepsilon}|\operatorname{Def}U|^2,
\qquad
Q_\varepsilon^{\mathrm{Hodge}}(U)=\int_{\Sigma_\varepsilon}
\bigl(|\operatorname{curl}U|^2+|\operatorname{div}U|^2\bigr).
\]

The finite-element implementation uses these native endpoint forms.  Impermeability is approximated by a mesh-scaled normal penalty.  For $0<\alpha<1$, the deformation form receives the signed inner/outer curvature boundary term whose natural condition is the invariant two-wall relation

\[
\partial_r U^i=2\alpha S^i{}_j(r)U^j.
\]

On the unit sphere, the degree-one rotational mode has the surface eigenvalue

\[
\lambda_\alpha=2\alpha+4\alpha(1-\alpha)=6\alpha-4\alpha^2.
\]

This gives an exact scalar resolvent coefficient against which the transverse shell average can be compared.

## Computational acceptance gates

The `wall-selection` study separates two numerical questions.

1. At fixed thickness, tangential refinement must monotonically reduce the error in the averaged resolvent coefficient.  Divergence, normal trace, pressure gauge, and wall-law residuals are reported independently.
2. In the coupled thin sequence, $h/\varepsilon$ is held fixed while both $h$ and $\varepsilon$ decrease.  The single-mode coefficient error must decrease at nearly second order.

The intermediate values \(\alpha=0.25,0.5,0.75\) are compared with the extrinsic spherical family, not with a linear blend of the two endpoint eigenvalues.

These gates establish a spatially resolved, wall-sensitive spherical resolvent experiment.  They do not establish convergence for arbitrary data, a full operator norm, semigroups, or spectra.

## Smooth-core recovery theorem on the canonical torus

Let $T=T(2,1)$ have global periodic coordinates $(\theta,\phi)$, metric

\[
g=\mathrm d\theta^2+\rho(\theta)^2\mathrm d\phi^2,
\qquad \rho(\theta)=2+\cos\theta,
\]

and principal curvatures

\[
\kappa_1=-1,
\qquad
\kappa_2=-\frac{\cos\theta}{2+\cos\theta}.
\]

Every smooth periodic solenoidal field on $T$ has the global stream-plus-flux representation

\[
\rho v^\theta=\partial_\phi\psi+A,
\qquad
\rho v^\phi=-\partial_\theta\psi+B,
\]

where $\psi$ is smooth and periodic and $A,B\in\mathbb R$. To see that the representation is onto, average $\rho v^\theta$ in $\phi$ to obtain the constant $A$, integrate its zero-mean remainder in $\phi$, and then add a periodic function of $\theta$ so that $\rho v^\phi+\partial_\theta\psi$ is the constant $B$. The two constants retain both torus cohomology modes.

The shell $|\sigma|<\varepsilon$ has

\[
G_\sigma=\mathrm{diag}\!\left((1+\sigma)^2,
\left(2+(1+\sigma)\cos\theta\right)^2,1\right),
\qquad
J(\theta,\sigma)=\frac{(1+\sigma)(2+(1+\sigma)\cos\theta)}{2+\cos\theta}.
\]

Fix $\alpha=0$ for Navier or $\alpha=1$ for Hodge. For $i=1,2$, define

\[
d_i=1-(1+\alpha)(1+2\alpha)\kappa_i^2\varepsilon^2,
\qquad
p_i(\sigma)=1+\frac{2\alpha\kappa_i}{d_i}\sigma
+\frac{\alpha(1+2\alpha)\kappa_i^2}{d_i}\sigma^2,
\]

\[
m_i=\frac1{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}Jp_i\,\mathrm d\sigma,
\qquad
U^i_\varepsilon=m_i^{-1}p_i v^i.
\]

The polynomial $p_i$ satisfies the exact two-wall relation

\[
\partial_\sigma U^i_\varepsilon
=2\alpha\,S^i{}_i(\sigma)U^i_\varepsilon
\quad\text{at }\sigma=\pm\varepsilon,
\]

and the moment normalization gives

\[
P_\varepsilon U_\varepsilon
:=\frac1{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}
J(\theta,\sigma)U^\top_\varepsilon\,\mathrm d\sigma=v.
\]

Set

\[
D_\varepsilon
=\partial_\theta(\rho J U^\theta_\varepsilon)
+\partial_\phi(\rho J U^\phi_\varepsilon),
\qquad
U^\sigma_\varepsilon(\sigma)
=-\frac1{\rho J}\int_{-\varepsilon}^{\sigma}D_\varepsilon(t)\,\mathrm dt.
\]

This is an exact, non-iterative divergence correction. The lower normal trace vanishes by definition. At the upper wall, moment normalization and $\operatorname{div}_g v=0$ give

\[
\int_{-\varepsilon}^{\varepsilon}D_\varepsilon\,\mathrm d\sigma
=2\varepsilon\bigl[\partial_\theta(\rho v^\theta)
+\partial_\phi(\rho v^\phi)\bigr]=0,
\]

so the upper normal trace also vanishes, and differentiating the defining antiderivative proves $\operatorname{div}_{G_\sigma}U_\varepsilon=0$ identically. Lemma 3.1 of WBS26 then identifies the two-wall relation with the stress-free tensor trace at $\alpha=0$ and the vorticity-free trace at $\alpha=1$. The implementation also checks those native tensor traces independently on a nontrivial stream-and-flux field.

Consequently, for every smooth solenoidal $v$, `canonical_torus_smooth_recovery` constructs a smooth member of the source shell form domain at either endpoint; it actually satisfies the associated natural operator boundary condition, which is stronger than form-domain membership. The construction uses the same normalized weighted transverse map $P_\varepsilon$ required by the varying-space comparison, and $P_\varepsilon U_\varepsilon=v$ holds exactly.

Let $E_\varepsilon v=(v^\theta,v^\phi,0)$ be the constant normal lift and use the normalized shell norm

\[
\lVert U\rVert_{H_\varepsilon}^2
=\frac1{2\varepsilon}\int_{\Sigma_\varepsilon}|U|_{G_\sigma}^2\,\mathrm dV_G.
\]

After $\sigma=\varepsilon z$, the exact rational recovery agrees through order two with the universal field jet recorded by `canonical_torus_smooth_recovery_rate`. Its squared $H_\varepsilon$ distance from $E_\varepsilon v$ has zero constant and linear coefficients. For the selected endpoint energy, the pointwise zeroth coefficient is the surface energy density and the averaged linear coefficient is zero. The normal-tangential fast tensor has zero leading coefficient, so replacing the exact field by its two-jet does not lose an energy term at quadratic order. Since $\rho\ge1$, $|\kappa_i|\le1$, $d_i\ge5/8$, and the remaining rational coefficients and their tangential derivatives are uniformly bounded for $0<\varepsilon\le1/4$, Taylor's theorem on the compact coordinate cylinder gives constants depending only on $T(2,1)$ such that

\[
\lVert U_\varepsilon-E_\varepsilon v\rVert_{H_\varepsilon}^2
\le C_T\varepsilon^2\lVert v\rVert_{C^1(T)}^2,
\]

\[
\left|Q_\varepsilon^\alpha(U_\varepsilon)-Q_0^\alpha(v)\right|
\le C_T\varepsilon^2\lVert v\rVert_{C^2(T)}^2.
\]

Thus the construction gives strong varying-space recovery and the WBS26 smooth-data $O(\varepsilon^2)$ energy rate for every smooth solenoidal field on the canonical torus, at both rigorous endpoints. The source uses $z\in(-1/2,1/2)$ and full thickness $\varepsilon$; this implementation uses $z\in(-1,1)$ and half-thickness $\varepsilon$, an equivalent rescaling recorded in the claim assumptions.

`WBS26-smooth-recovery-canonical-torus` records this precise constructive theorem. It is the smooth-core part of Mosco M2, not the density/diagonal extension to every limit-form vector, M1, the full Mosco theorem, or an operator-convergence conclusion.

### Integrated regression mode

The earlier field $v=\sin(\theta)\partial_\phi$ remains a compact Navier regression. Its normal corrector vanishes and the lift is independent of $\sigma$. The exact normalized identities are

\[
\lVert v\rVert_{L^2(T)}^2=19\pi^2,
\qquad
\lVert U_\varepsilon\rVert_{H_\varepsilon}^2=19\pi^2+3\pi^2\varepsilon^2,
\]

\[
Q_0^{\mathrm{Navier}}(v)=25\pi^2,
\qquad
Q_\varepsilon^{\mathrm{Navier}}(U_\varepsilon)
=\frac{\pi^2}{\varepsilon}
\left(9\varepsilon-8\log(1-\varepsilon)+8\log(1+\varepsilon)\right)
=25\pi^2+\frac{16\pi^2}{3}\varepsilon^2+O(\varepsilon^4).
\]

`canonical_navier_torus_recovery` retains these closed integrals and the independent JAX divergence and deformation-density cross-check under the narrower `WBS26-smooth-recovery-mode` claim.

## Analytic proof ledger

The WBS26 Mosco theorem requires the following concrete results on the continuous shell spaces.

| Obligation | Required statement | Repository status |
| --- | --- | --- |
| Hilbert carriers | Define the weighted shell $L^2$ spaces, solenoidal form domains, and surface limit space | actual complete surface and thickness-dependent shell `Lp` Hilbert carriers; solenoidal form domains open |
| Identification | Prove the tangential lift and transverse average converge with the tubular Jacobian normalization | actual uniformly bounded $E_\varepsilon$ and $P_\varepsilon$ on the weighted quotients, with representative and integral identities; asymptotic $P_\varepsilon E_\varepsilon\to I$ theorem open |
| Uniform Navier coercivity | Thickness-uniform Korn/Gårding estimate modulo Killing fields | predicate exists; concrete shell theorem open |
| Uniform Hodge coercivity | Thickness-uniform Gaffney estimate using two-wall curvature cancellation | predicate exists; concrete shell theorem open |
| Compactness | Bounded energy implies a (z)-independent tangential solenoidal weak limit | open |
| Mosco liminf | Freeze the exact coefficients and discard nonnegative fluctuation squares | abstract definition exists; concrete proof open |
| Smooth recovery | Construct the condition-specific tangential profile and normal divergence corrector with $O(\varepsilon^2)$ energy error | complete on the canonical-torus smooth core at both endpoints |
| Exact solenoidality | Prove a uniformly bounded divergence correction | complete on the canonical-torus smooth core by the exact flux-normalized antiderivative |
| Form-domain recovery | Extend smooth recovery by core density and a diagonal argument | open |
| Operator association | Construct the closed self-adjoint generators and prove that their resolvents arise from the same forms | abstract contract exists; concrete proof open |
| Consequences | Apply varying-Hilbert-space Mosco theory to resolvents, compact-time semigroups, and scoped spectra | conditional interfaces exist; theorem instantiation open |

For the source theorem, Navier and Hodge are the rigorous endpoints on torus-type surfaces of revolution.  The intermediate partial-slip family is a formal general-hypersurface result in the current source; the new computation supports that formal family on spherical shells but does not upgrade its analytic status.

The ambient weighted carriers and bounded comparison maps are now concrete. The remaining gap to M2 is the closed solenoidal form setting, density of the smooth surface core in that exact limit form norm, compatibility of the symbolic recoveries with the quotient maps, and the diagonal extension. M1 still requires endpoint-uniform Korn/Gaffney estimates, transverse compactness, identification of the tangential solenoidal limit, and the liminf inequality. No Mosco or operator conclusion is claimed before those gates close.
