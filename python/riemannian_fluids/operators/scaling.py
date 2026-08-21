"""Scaling-direction viscosity candidates of Chan--Czubak--Fuster Aguilera (2025)."""

from __future__ import annotations

import jax.numpy as jnp

from riemannian_fluids.geometry import intrinsic_gaussian_curvature, metric
from riemannian_fluids.operators.viscosity import deformation_laplacian, hodge_laplacian
from riemannian_fluids.tensors import (
    gradient,
    lie_bracket,
    raised_lie_derivative_one_form,
)
from riemannian_fluids.types import Array, Embedding, VectorField


def ellipsoid_scaling_generator(embedding: Embedding) -> VectorField:
    """Return ``A=-1/4 grad(log K)`` for the cited spheroid."""

    def generator(q: Array) -> Array:
        return -0.25 * gradient(
            embedding,
            lambda point: jnp.log(intrinsic_gaussian_curvature(embedding, point)),
            q,
        )

    return generator


def ellipsoid_2025_candidates(
    embedding: Embedding,
    field: VectorField,
    q: Array,
) -> tuple[Array, Array, Array, Array]:
    """Return the four scaling-direction candidates of arXiv:2511.10579v1, (1.4)--(1.7)."""

    generator = ellipsoid_scaling_generator(embedding)
    deformation = deformation_laplacian(embedding, field, q)
    hodge = hodge_laplacian(embedding, field, q)
    bracket = lie_bracket(generator, field, q)
    one_form_lie = raised_lie_derivative_one_form(embedding, generator, field, q)
    generator_value = generator(q)
    component = (field(q) @ metric(embedding, q) @ generator_value) * generator_value
    return (
        deformation + bracket + 2.0 * component,
        hodge + one_form_lie,
        deformation + bracket,
        hodge + one_form_lie - 2.0 * component,
    )
