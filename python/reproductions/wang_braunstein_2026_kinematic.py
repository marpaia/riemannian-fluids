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
        "arXiv:2605.17502v2, Section 4.2, equations (22)--(24)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "WBK26-negative-curvature-decay",
        PAPER.id,
        (
            "On a complete noncompact two-dimensional manifold of bounded geometry with K <= -kappa^2 < 0, for every mu > 0 and u0 in H, "
            "the deformation-viscosity Navier-Stokes equation has a unique global weak solution in L-infinity(0,T;H) intersect L2(0,T;V) for every "
            "T > 0, admits a pressure distribution recovering momentum, and satisfies ||u(t)||_L2^2 <= exp(-2 mu kappa^2 t) ||u0||_L2^2."
        ),
        "arXiv:2605.17502v2, Theorem 6.1, equations (39)-(40), with uniqueness detailed in Remark 6.2",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        assumptions={
            "manifold": "complete, noncompact, two-dimensional Riemannian manifold of bounded geometry",
            "curvature": "Gaussian curvature K <= -kappa^2 < 0 for some kappa > 0",
            "spaces": "H and V are the L2 and H1 closures of smooth compactly supported divergence-free vector fields",
            "viscosity": "mu > 0",
            "initial data": "u0 in H",
        },
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
