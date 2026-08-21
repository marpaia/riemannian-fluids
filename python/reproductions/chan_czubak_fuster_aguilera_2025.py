"""Four ellipsoid candidates of Chan--Czubak--Fuster Aguilera (2025)."""

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry import metric, sphere, spheroid, vector_norm
from riemannian_fluids.operators import (
    deformation_laplacian,
    ellipsoid_2025_candidates,
    ellipsoid_scaling_generator,
    hodge_laplacian,
)
from riemannian_fluids.tensors import lie_bracket, raised_lie_derivative_one_form, stream_vector_field
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CCF25",
    "Thin shell limit and the derivation of the viscosity operator on the ellipsoid",
    ("Chi Hin Chan", "Magdalena Czubak", "Padi Fuster Aguilera"),
    2025,
    "https://arxiv.org/abs/2511.10579",
    "v1",
    "Four scaling-direction candidates under Navier and Hodge wall conditions.",
)
CLAIMS = (
    Claim(
        "CCF25-four-candidates-sphere",
        PAPER.id,
        "The four ellipsoid candidates collapse to their Navier/Hodge endpoints on a sphere.",
        "arXiv:2511.10579v1, Theorems 1.1 and 1.3, formulas (1.4)--(1.7), specialized by Remark 1.5",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
        {
            "surface": "round sphere",
            "collapse mechanism": "the scaling generator -1/4 grad(log K) vanishes on constant curvature, so the check also gates that vanishing",
        },
        geometry_coverage="sphere",
        sample_coverage="3 generic points x 4 candidates",
    ),
    Claim(
        "CCF25-averaging-dependence",
        PAPER.id,
        "The scaling-direction thin-shell result depends on the averaging prescription.",
        "arXiv:2511.10579v1, Theorems 1.1, 1.3, and 1.6 with Remark 1.8; the paper labels these limits heuristic",
        EvidenceKind.CONSTRUCTIVE_WITNESS,
        ClaimStatus.VALIDATED,
        {
            "surface": "axisymmetric spheroid",
            "witness": "every candidate differs from its Navier/Hodge endpoint by a relative gap above 1e-3 at each sample point",
        },
        geometry_coverage="spheroid",
        sample_coverage="3 generic points x 4 candidates",
    ),
)


def _stream(q):
    return jnp.sin(q[0]) ** 2 * jnp.cos(2.0 * q[1]) + 0.17 * jnp.sin(3.0 * q[0]) * jnp.sin(q[1])


_POINTS = ((0.9, 0.8), (1.7, 2.6), (2.3, 5.1))


def _sphere_collapse() -> dict[str, float | int | str]:
    embedding = sphere().embedding
    velocity = stream_vector_field(embedding, _stream)
    generator = ellipsoid_scaling_generator(embedding)

    def diagnostics(q):
        candidates = ellipsoid_2025_candidates(embedding, velocity, q)
        endpoints = (
            deformation_laplacian(embedding, velocity, q),
            hodge_laplacian(embedding, velocity, q),
        ) * 2
        residuals = jnp.asarray(
            [vector_norm(embedding, candidate - endpoint, q) for candidate, endpoint in zip(candidates, endpoints, strict=True)]
        )
        return jnp.concatenate((residuals, jnp.asarray((vector_norm(embedding, generator(q), q),))))

    values = jax.jit(jax.vmap(diagnostics))(jnp.asarray(_POINTS, dtype=jnp.float64))
    return {
        "max_absolute_residual": float(jnp.max(values[:, :4])),
        "max_scaling_generator_norm": float(jnp.max(values[:, 4])),
    }


def _spheroid_dependence() -> dict[str, float | int | str]:
    embedding = spheroid().embedding
    velocity = stream_vector_field(embedding, _stream)
    generator = ellipsoid_scaling_generator(embedding)

    def diagnostics(q):
        candidates = ellipsoid_2025_candidates(embedding, velocity, q)
        deformation = deformation_laplacian(embedding, velocity, q)
        hodge = hodge_laplacian(embedding, velocity, q)
        bracket = lie_bracket(generator, velocity, q)
        one_form_lie = raised_lie_derivative_one_form(embedding, generator, velocity, q)
        generator_value = generator(q)
        component = (velocity(q) @ metric(embedding, q) @ generator_value) * generator_value
        constructions = (
            deformation + bracket + 2.0 * component,
            hodge + one_form_lie,
            deformation + bracket,
            hodge + one_form_lie - 2.0 * component,
        )
        endpoints = (deformation, hodge, deformation, hodge)
        construction_residuals = []
        endpoint_gaps = []
        for candidate, construction, endpoint in zip(candidates, constructions, endpoints, strict=True):
            scale = jnp.maximum(vector_norm(embedding, candidate, q), 1.0e-12)
            construction_residuals.append(vector_norm(embedding, candidate - construction, q) / scale)
            gap_scale = jnp.maximum(jnp.maximum(vector_norm(embedding, candidate, q), vector_norm(embedding, endpoint, q)), 1.0e-12)
            endpoint_gaps.append(vector_norm(embedding, candidate - endpoint, q) / gap_scale)
        return jnp.asarray(construction_residuals + endpoint_gaps)

    values = jax.jit(jax.vmap(diagnostics))(jnp.asarray(_POINTS, dtype=jnp.float64))
    measurements: dict[str, float | int | str] = {
        "max_relative_construction_residual": float(jnp.max(values[:, :4])),
        "min_relative_endpoint_gap": float(jnp.min(values[:, 4:])),
    }
    for index in range(4):
        measurements[f"candidate_{index + 1}_min_relative_endpoint_gap"] = float(jnp.min(values[:, 4 + index]))
    return measurements


def run() -> tuple[ClaimResult, ...]:
    collapse = _sphere_collapse()
    dependence = _spheroid_dependence()
    collapse_passed = (
        float(collapse["max_absolute_residual"]) < 1.0e-10 and float(collapse["max_scaling_generator_norm"]) < 1.0e-10
    )
    dependence_passed = (
        float(dependence["max_relative_construction_residual"]) < 1.0e-12 and float(dependence["min_relative_endpoint_gap"]) > 1.0e-3
    )
    return (
        ClaimResult(CLAIMS[0].id, collapse_passed, collapse),
        ClaimResult(CLAIMS[1].id, dependence_passed, dependence),
    )
