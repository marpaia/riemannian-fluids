from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.function_spaces import DiscreteDeRhamComplex, hodge_decomposition


def test_discrete_hodge_decomposition_reconstructs() -> None:
    d0 = jnp.asarray(((-1.0, 1.0, 0.0), (0.0, -1.0, 1.0), (-1.0, 0.0, 1.0)))
    d1 = jnp.asarray(((1.0, 1.0, -1.0),))
    complex = DiscreteDeRhamComplex(d0, d1, jnp.eye(3), jnp.eye(3), jnp.eye(1))
    value = jnp.asarray((0.4, -0.2, 0.7))
    pieces = hodge_decomposition(complex, value)
    assert jnp.allclose(complex.complex_residual(), 0.0)
    assert jnp.allclose(pieces.reconstruct(), value)
    assert jnp.isclose(pieces.exact @ pieces.coexact, 0.0, atol=1.0e-12)
