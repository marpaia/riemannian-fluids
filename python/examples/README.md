# Symbolic solver examples

These scripts are worked, narrated computations for the `riemannian_fluids.symbolic` backend.  They print every artifact a result carries: the reduced integrand, the closed form, the certificate grade with its assumptions, the derivation ledger, and the numeric verification.

- [`energy_integrals.py`](energy_integrals.py) solves deformation-energy integrals over hyperbolic exterior domains, shows the certificate tiers (exact, divergent, unresolved), exposes the integration-by-parts boundary flux, and verifies `L_Def = L_Hodge - 2 Ric` for a generic stream function on three chart families.
- [`thin_shell_limits.py`](thin_shell_limits.py) builds the spherical tube chart with its exact Jacobian, constructs the two-wall rotational profile for a symbolic wall parameter, and extracts the wall-selected eigenvalue `6 alpha - 4 alpha^2` from the transverse-averaged pairing, matching the interpolating surface family.

Run both from the repository root:

```sh
pixi run --locked symbolic-examples
```
