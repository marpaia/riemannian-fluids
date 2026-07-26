"""Finite-dimensional de Rham complexes and Hodge decomposition."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.types import Array


def _weighted_projection(basis: Array, mass: Array, value: Array) -> Array:
    if basis.shape[1] == 0:
        return jnp.zeros_like(value)
    gram = basis.T @ mass @ basis
    coefficients = jnp.linalg.lstsq(gram, basis.T @ mass @ value, rcond=None)[0]
    return basis @ coefficients


@dataclass(frozen=True)
class DiscreteDeRhamComplex:
    """The segment ``V0 --d0--> V1 --d1--> V2`` with mass matrices."""

    d0: Array
    d1: Array
    mass0: Array
    mass1: Array
    mass2: Array

    def complex_residual(self) -> Array:
        return self.d1 @ self.d0

    def codifferential2(self) -> Array:
        return jnp.linalg.solve(self.mass1, self.d1.T @ self.mass2)

    def hodge_laplacian1(self) -> Array:
        delta1 = jnp.linalg.solve(self.mass0, self.d0.T @ self.mass1)
        return self.d0 @ delta1 + self.codifferential2() @ self.d1


@dataclass(frozen=True)
class HodgeComponents:
    exact: Array
    coexact: Array
    harmonic: Array

    def reconstruct(self) -> Array:
        return self.exact + self.coexact + self.harmonic


def hodge_decomposition(complex: DiscreteDeRhamComplex, one_form: Array) -> HodgeComponents:
    """Orthogonally split a discrete one-form into exact, coexact, harmonic parts."""

    exact = _weighted_projection(complex.d0, complex.mass1, one_form)
    coexact_basis = complex.codifferential2()
    coexact = _weighted_projection(coexact_basis, complex.mass1, one_form - exact)
    harmonic = one_form - exact - coexact
    return HodgeComponents(exact, coexact, harmonic)
