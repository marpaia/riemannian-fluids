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
        "The Hodge formulation has a hyperbolic energy obstruction.",
        "Section 3",
        EvidenceKind.CONSTRUCTIVE_WITNESS,
        ClaimStatus.CATALOGUED,
    ),
    Claim(
        "CCD17-relativistic-limit",
        PAPER.id,
        "The nonrelativistic limit motivates the deformation operator.",
        "arXiv v1, nonrelativistic-limit section",
        EvidenceKind.SYMBOLIC_IDENTITY,
        ClaimStatus.CATALOGUED,
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
