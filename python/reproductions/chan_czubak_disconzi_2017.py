"""Core operator relations from Chan--Czubak--Disconzi (2017)."""

import jax.numpy as jnp

from riemannian_fluids.geometry import sphere, vector_norm
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


def run() -> tuple[ClaimResult, ...]:
    surface = sphere()
    velocity = stream_vector_field(surface, lambda q: jnp.sin(q[0]) ** 2 * jnp.cos(2 * q[1]))
    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)
    left = deformation_laplacian(surface, velocity, q)
    right = hodge_laplacian(surface, velocity, q) - 2.0 * ricci_action(surface, velocity, q)
    residual = float(vector_norm(surface, left - right, q))
    return (ClaimResult(CLAIMS[0].id, residual < 1.0e-10, {"absolute_residual": residual}),)
