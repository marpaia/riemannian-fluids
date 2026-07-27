"""Kinematic selection claims of Wang--Braunstein (2026)."""

import jax.numpy as jnp

from riemannian_fluids.geometry import covariant_tensor_norm, sphere
from riemannian_fluids.tensors import deformation_tensor, lie_derivative_metric
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "WBK26",
    "Resolving the viscosity operator ambiguity on Riemannian manifolds via a kinematic selection principle",
    ("Zhi-Wei Wang", "Samuel L. Braunstein"),
    2026,
    "https://arxiv.org/abs/2605.17502",
    "v2",
    "Intrinsic strain selection, hyperbolic coercivity, weak solutions, and energy decay.",
)
CLAIMS = (
    Claim(
        "WBK26-lie-strain",
        PAPER.id,
        "The metric rate under a velocity field is twice the deformation tensor.",
        "kinematic construction",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "WBK26-negative-curvature-decay",
        PAPER.id,
        "Deformation-viscosity weak solutions decay exponentially under uniform negative curvature.",
        "global weak-solution theorem",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
    ),
)


def run() -> tuple[ClaimResult, ...]:
    surface = sphere()

    def field(q):
        return jnp.asarray((jnp.sin(q[1]), jnp.cos(q[0])))

    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)
    residual = float(
        covariant_tensor_norm(
            surface,
            lie_derivative_metric(surface, field, q) - 2.0 * deformation_tensor(surface, field, q),
            q,
        )
    )
    return (ClaimResult(CLAIMS[0].id, residual < 1.0e-10, {"absolute_residual": residual}),)
