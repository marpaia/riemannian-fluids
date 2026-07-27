"""A codimension-two Gauss-equation gate for Chan--Czubak (2025)."""

import jax.numpy as jnp

from riemannian_fluids.geometry import (
    euclidean_submanifold,
    gauss_ricci_tensor,
    intrinsic_ricci_tensor,
)
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CCG25",
    "The Gauss formulas for Laplacians on submanifolds",
    ("Chi Hin Chan", "Magdalena Czubak"),
    2025,
    "https://arxiv.org/abs/2212.11928",
    "v2",
    "Gauss formulas for vector Laplacians on submanifolds of arbitrary codimension.",
)
CLAIMS = (
    Claim(
        "CCG25-gauss-ricci-codimension-two",
        PAPER.id,
        "The intrinsic Ricci tensor equals its Euclidean Gauss-equation expression.",
        "Ricci Gauss formula",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
        {"codimension": "2", "ambient": "Euclidean"},
    ),
    Claim(
        "CCG25-laplacian-gauss-family",
        PAPER.id,
        "Bochner and Hodge Laplacians admit the paper's arbitrary-codimension formulas.",
        "main theorems",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.CATALOGUED,
    ),
)


def run() -> tuple[ClaimResult, ...]:
    def clifford_torus(q):
        return jnp.asarray((jnp.cos(q[0]), jnp.sin(q[0]), jnp.cos(q[1]), jnp.sin(q[1])))

    surface = euclidean_submanifold("Clifford torus", 2, 4, clifford_torus)
    q = jnp.asarray((0.7, 1.1), dtype=jnp.float64)
    residual = float(jnp.linalg.norm(intrinsic_ricci_tensor(surface, q) - gauss_ricci_tensor(surface, q)))
    return (ClaimResult(CLAIMS[0].id, residual < 1.0e-10, {"absolute_residual": residual}),)
