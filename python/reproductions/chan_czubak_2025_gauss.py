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
        "arXiv:2212.11928v2, Theorem 1.9, equations (1.11)--(1.12)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
        {"codimension": "2", "ambient": "Euclidean"},
        geometry_coverage="Clifford torus+curved graph surface in R^4",
        sample_coverage="3 generic points per surface",
    ),
    Claim(
        "CCG25-laplacian-gauss-family",
        PAPER.id,
        "Bochner and Hodge Laplacians admit the paper's arbitrary-codimension formulas.",
        "arXiv:2212.11928v2, Theorem 1.1, equations (1.5)--(1.6), and Corollary 1.20",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.CATALOGUED,
    ),
)


def run() -> tuple[ClaimResult, ...]:
    def clifford_torus(q):
        return jnp.asarray((jnp.cos(q[0]), jnp.sin(q[0]), jnp.cos(q[1]), jnp.sin(q[1])))

    def graph_surface(q):
        u, v = q
        return jnp.asarray((u, v, jnp.sin(u) * jnp.cos(v), 0.4 * jnp.cos(2.0 * u) + 0.3 * jnp.sin(u + v)))

    cases = (
        euclidean_submanifold("Clifford torus", 2, 4, clifford_torus),
        euclidean_submanifold("curved graph surface", 2, 4, graph_surface),
    )
    points = ((0.7, 1.1), (1.9, 2.8), (2.6, 4.4))
    measurements: dict[str, float | int | str] = {}
    worst = 0.0
    largest_ricci_norm = 0.0
    for surface in cases:
        surface_max = 0.0
        for point in points:
            q = jnp.asarray(point, dtype=jnp.float64)
            intrinsic = intrinsic_ricci_tensor(surface, q)
            surface_max = max(surface_max, float(jnp.linalg.norm(intrinsic - gauss_ricci_tensor(surface, q))))
            largest_ricci_norm = max(largest_ricci_norm, float(jnp.linalg.norm(intrinsic)))
        key = surface.name.replace(" ", "_")
        measurements[f"{key}_max_absolute_residual"] = surface_max
        worst = max(worst, surface_max)
    measurements["max_absolute_residual"] = worst
    measurements["max_intrinsic_ricci_norm"] = largest_ricci_norm
    passed = worst < 1.0e-10 and largest_ricci_norm > 1.0e-1
    return (ClaimResult(CLAIMS[0].id, passed, measurements),)
