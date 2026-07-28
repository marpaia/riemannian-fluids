# Thin-shell convergence: numerical gates and proof obligations

The resolved-shell program has two distinct goals.  The numerical goal is to show that a stated volume discretization behaves like its stated surface target under separated resolution studies.  The analytic goal is to prove convergence of the continuous shell forms before discretization.  Passing the first goal is evidence for an implementation; it is not the second goal.

## Implemented wall forms

For impermeable shell fields, the two source endpoint energies are

\[
Q_\varepsilon^{\mathrm{Navier}}(U)=2\int_{\Sigma_\varepsilon}|\operatorname{Def}U|^2,
\qquad
Q_\varepsilon^{\mathrm{Hodge}}(U)=\int_{\Sigma_\varepsilon}
\bigl(|\operatorname{curl}U|^2+|\operatorname{div}U|^2\bigr).
\]

The finite-element implementation uses these native endpoint forms.  Impermeability is approximated by a mesh-scaled normal penalty.  For (0<\alpha<1), the deformation form receives the signed inner/outer curvature boundary term whose natural condition is the invariant two-wall relation

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
2. In the coupled thin sequence, (h/\varepsilon) is held fixed while both (h\) and \(\varepsilon\) decrease.  The single-mode coefficient error must decrease at nearly second order.

The intermediate values \(\alpha=0.25,0.5,0.75\) are compared with the extrinsic spherical family, not with a linear blend of the two endpoint eigenvalues.

These gates establish a spatially resolved, wall-sensitive spherical resolvent experiment.  They do not establish convergence for arbitrary data, a full operator norm, semigroups, or spectra.

## Analytic proof ledger

The WBS26 Mosco theorem requires the following concrete results on the continuous shell spaces.

| Obligation | Required statement | Repository status |
| --- | --- | --- |
| Hilbert carriers | Define the weighted shell (L^2) spaces, solenoidal form domains, and surface limit space | abstract interface only |
| Identification | Prove the tangential lift and transverse average converge with the tubular Jacobian normalization | geometry and averaging formulas exist; Hilbert proof open |
| Uniform Navier coercivity | Thickness-uniform Korn/Gårding estimate modulo Killing fields | predicate exists; concrete shell theorem open |
| Uniform Hodge coercivity | Thickness-uniform Gaffney estimate using two-wall curvature cancellation | predicate exists; concrete shell theorem open |
| Compactness | Bounded energy implies a (z)-independent tangential solenoidal weak limit | open |
| Mosco liminf | Freeze the exact coefficients and discard nonnegative fluctuation squares | abstract definition exists; concrete proof open |
| Smooth recovery | Construct the condition-specific tangential profile and normal divergence corrector with (O(\varepsilon^2)) energy error | computational formulas exist; Sobolev estimate open |
| Exact solenoidality | Prove a uniformly bounded divergence right inverse and convergence of the correction iteration | open |
| Form-domain recovery | Extend smooth recovery by core density and a diagonal argument | open |
| Operator association | Construct the closed self-adjoint generators and prove that their resolvents arise from the same forms | abstract contract exists; concrete proof open |
| Consequences | Apply varying-Hilbert-space Mosco theory to resolvents, compact-time semigroups, and scoped spectra | conditional interfaces exist; theorem instantiation open |

For the source theorem, Navier and Hodge are the rigorous endpoints on torus-type surfaces of revolution.  The intermediate partial-slip family is a formal general-hypersurface result in the current source; the new computation supports that formal family on spherical shells but does not upgrade its analytic status.

The next proof-bearing milestone is therefore not another finite-element refinement.  It is a concrete surface-of-revolution shell-space construction followed by the uniform Gaffney estimate and the smooth solenoidal recovery estimate.  Those two results unlock the liminf and recovery halves respectively.
