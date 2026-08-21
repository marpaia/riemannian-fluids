"""Core operator relations from Chan--Czubak--Disconzi (2017)."""

import jax
import jax.numpy as jnp

from riemannian_fluids.geometry import sphere, spheroid, torus_of_revolution, vector_norm
from riemannian_fluids.operators import deformation_laplacian, hodge_laplacian, ricci_action
from riemannian_fluids.tensors import stream_vector_field
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CCD17",
    "The formulation of the Navier-Stokes equations on Riemannian manifolds",
    ("Chi Hin Chan", "Magdalena Czubak", "Marcelo M. Disconzi"),
    2017,
    "https://arxiv.org/abs/1608.05114",
    "v2",
    "Operator selection, stress, energy, hyperbolic obstruction, and relativistic limit.",
)
CLAIMS = (
    Claim(
        "CCD17-divfree-def-hodge",
        PAPER.id,
        "For divergence-free velocity, L_Def = L_Hodge - 2 Ric in the positive convention.",
        "Introduction, equations (1.1)-(1.3) and the divergence-free specialization immediately following (1.3)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
        {"field": "divergence-free", "manifold": "oriented surface"},
        geometry_coverage="sphere+spheroid+torus_of_revolution",
        sample_coverage="3 generic points per surface, divergence-free stream fields",
    ),
    Claim(
        "CCD17-hyperbolic-energy-obstruction",
        PAPER.id,
        "On H2(-a^2), no positive absolute constant controls the expected global "
        "Hodge-Stokes energy estimate uniformly over all terminal times and weak solutions "
        "in the stated energy spaces.",
        "arXiv:1608.05114v2, Theorems 3.2--3.3 and equations (3.11)--(3.17)",
        EvidenceKind.CONSTRUCTIVE_WITNESS,
        ClaimStatus.CATALOGUED,
        {
            "geometry": "hyperbolic plane H2(-a^2), a > 0",
            "viscosity": "Hodge Laplacian",
            "quantifier": "no C0 > 0 works for every T > 0",
        },
    ),
    Claim(
        "CCD17-relativistic-limit",
        PAPER.id,
        "The Lichnerowicz, Choquet-Bruhat, and Freistuehler-Temple first-order relativistic "
        "stresses all produce div(2 Def v) in the nonrelativistic spatial momentum equation.",
        "arXiv:1608.05114v2, Section 5, especially equation (5.1) and the paragraph following it",
        EvidenceKind.SYMBOLIC_IDENTITY,
        ClaimStatus.CATALOGUED,
        {
            "models": "Lichnerowicz; Choquet-Bruhat; Freistuehler-Temple",
            "limit": "nonrelativistic spatial momentum equation",
        },
    ),
)


def _spherical_stream(q):
    return jnp.sin(q[0]) ** 2 * jnp.cos(2.0 * q[1]) + 0.17 * jnp.sin(3.0 * q[0]) * jnp.sin(q[1])


def _torus_stream(q):
    return jnp.sin(q[0]) + 0.31 * jnp.cos(2.0 * q[1]) + 0.19 * jnp.sin(q[0] + q[1])


def run() -> tuple[ClaimResult, ...]:
    cases = (
        ("sphere", sphere().embedding, _spherical_stream, ((0.9, 0.8), (1.7, 2.6), (2.3, 5.1))),
        ("spheroid", spheroid().embedding, _spherical_stream, ((0.9, 0.8), (1.7, 2.6), (2.3, 5.1))),
        ("torus_of_revolution", torus_of_revolution().embedding, _torus_stream, ((0.9, 0.7), (1.7, 2.6), (2.4, 4.1))),
    )
    measurements: dict[str, float | int | str] = {}
    worst = 0.0
    for name, embedding, stream, points in cases:
        velocity = stream_vector_field(embedding, stream)

        def residual(q, embedding=embedding, velocity=velocity):
            left = deformation_laplacian(embedding, velocity, q)
            right = hodge_laplacian(embedding, velocity, q) - 2.0 * ricci_action(embedding, velocity, q)
            return vector_norm(embedding, left - right, q)

        values = jax.jit(jax.vmap(residual))(jnp.asarray(points, dtype=jnp.float64))
        surface_max = float(jnp.max(values))
        measurements[f"{name}_max_absolute_residual"] = surface_max
        worst = max(worst, surface_max)
    measurements["max_absolute_residual"] = worst
    return (ClaimResult(CLAIMS[0].id, worst < 1.0e-10, measurements),)
