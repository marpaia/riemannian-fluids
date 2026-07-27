"""Hyperbolic nonuniqueness claim of Chan--Czubak (2013)."""

import jax.numpy as jnp

from riemannian_fluids.geometry import hyperbolic_upper_half_space, scalar_curvature
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CC13",
    "Non-uniqueness of the Leray-Hopf solutions in the hyperbolic setting",
    ("Chi Hin Chan", "Magdalena Czubak"),
    2013,
    "https://arxiv.org/abs/1006.2819",
    "v1",
    "Weak-solution nonuniqueness and Liouville failure on hyperbolic space.",
)
CLAIMS = (
    Claim(
        "CC13-hyperbolic-curvature-model",
        PAPER.id,
        "The computational H2 model has scalar curvature -2a^2.",
        "arXiv:1006.2819v1, Section 2.1, constant-curvature identities specialized to H2(-a^2)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "CC13-leray-hopf-nonuniqueness",
        PAPER.id,
        "For every a > 0, the deformation-viscosity Navier-Stokes equation on H2(-a^2) admits distinct Leray-Hopf solutions with the same initial datum.",
        "arXiv:1006.2819v1, Theorem 1.2",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "geometry": "hyperbolic plane H2(-a^2), a > 0",
            "viscosity": "2 Def* Def, equivalently the paper's N-S_H2(-a^2)",
            "solution class": "Leray-Hopf",
        },
    ),
)


def run() -> tuple[ClaimResult, ...]:
    curvature = -2.25
    manifold = hyperbolic_upper_half_space(curvature=curvature)
    value = float(scalar_curvature(manifold, jnp.asarray((0.3, 1.2), dtype=jnp.float64)))
    error = abs(value - 2.0 * curvature)
    return (ClaimResult(CLAIMS[0].id, error < 1.0e-10, {"absolute_residual": error}),)
