"""Continuous and discrete spaces used by Riemannian fluid equations."""

from riemannian_fluids.function_spaces.constraints import (
    ConstraintDiagnostics,
    pressure_mean,
    project_linear_constraint,
    weighted_norm,
)
from riemannian_fluids.function_spaces.hodge import (
    DiscreteDeRhamComplex,
    HodgeComponents,
    hodge_decomposition,
)
from riemannian_fluids.function_spaces.sobolev import (
    integrate,
    scalar_l2_norm,
    tensor_product_quadrature,
    vector_h1_seminorm,
    vector_l2_norm,
)

__all__ = (
    "ConstraintDiagnostics",
    "DiscreteDeRhamComplex",
    "HodgeComponents",
    "hodge_decomposition",
    "integrate",
    "pressure_mean",
    "project_linear_constraint",
    "scalar_l2_norm",
    "tensor_product_quadrature",
    "vector_h1_seminorm",
    "vector_l2_norm",
    "weighted_norm",
)
