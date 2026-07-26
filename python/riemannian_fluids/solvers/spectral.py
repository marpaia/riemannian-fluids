"""Dense generalized eigenproblems used as transparent spectral references."""

from __future__ import annotations

from dataclasses import dataclass

import jax.numpy as jnp

from riemannian_fluids.types import Array


@dataclass(frozen=True)
class GeneralizedEigenpairs:
    eigenvalues: Array
    eigenvectors: Array
    residual_norms: Array


def generalized_eigenpairs(
    stiffness: Array,
    mass: Array,
    *,
    count: int | None = None,
    nullspace_tolerance: float | None = None,
) -> GeneralizedEigenpairs:
    """Solve ``A u = lambda M u`` for symmetric ``A`` and positive ``M``."""

    if stiffness.shape != mass.shape or stiffness.ndim != 2:
        raise ValueError("stiffness and mass must be square matrices of equal shape")
    cholesky = jnp.linalg.cholesky(mass)
    left_reduced = jnp.linalg.solve(cholesky, stiffness)
    reduced = jnp.linalg.solve(cholesky, left_reduced.T).T
    values, reduced_vectors = jnp.linalg.eigh(0.5 * (reduced + reduced.T))
    vectors = jnp.linalg.solve(cholesky.T, reduced_vectors)
    if nullspace_tolerance is not None:
        keep = values > nullspace_tolerance
        values = values[keep]
        vectors = vectors[:, keep]
    if count is not None:
        if count < 1:
            raise ValueError("count must be positive")
        values = values[:count]
        vectors = vectors[:, :count]
    residuals = jnp.linalg.norm(stiffness @ vectors - mass @ vectors * values, axis=0)
    return GeneralizedEigenpairs(values, vectors, residuals)
