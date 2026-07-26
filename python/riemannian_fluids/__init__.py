"""Differential geometry, function spaces, and fluid equations on manifolds."""

import jax

from riemannian_fluids.types import Array, Embedding, ScalarField, VectorField

jax.config.update("jax_enable_x64", True)

__all__ = ("Array", "Embedding", "ScalarField", "VectorField")
