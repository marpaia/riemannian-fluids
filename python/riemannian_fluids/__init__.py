"""Differential geometry, function spaces, and fluid equations on manifolds."""

import jax

from riemannian_fluids.discrete import FlowDiagnostics, FlowSolveResult, FlowState, SemiDiscreteFlowSystem
from riemannian_fluids.types import Array, Embedding, ScalarField, VectorField

jax.config.update("jax_enable_x64", True)

__all__ = (
    "Array",
    "Embedding",
    "FlowDiagnostics",
    "FlowSolveResult",
    "FlowState",
    "ScalarField",
    "SemiDiscreteFlowSystem",
    "VectorField",
)
