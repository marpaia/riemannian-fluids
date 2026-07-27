"""H1 Hodge decomposition of Chan--Czubak--Pinilla Suarez (published 2025)."""

import jax.numpy as jnp

from riemannian_fluids.function_spaces import DiscreteDeRhamComplex, hodge_decomposition
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CCP25",
    "Hodge decomposition of the Sobolev space H1 on a space form of nonpositive curvature",
    ("Chi Hin Chan", "Magdalena Czubak", "Carlos Pinilla Suarez"),
    2025,
    "https://arxiv.org/abs/1812.11764",
    "v1; Differential Geometry and its Applications 2025",
    "H1 Hodge decomposition for k-forms on noncompact nonpositively curved space forms.",
)
CLAIMS = (
    Claim(
        "CCP25-discrete-hodge-gate",
        PAPER.id,
        "The discrete API separates exact, coexact, and harmonic one-form components.",
        "Project FEEC gate motivated by arXiv:1812.11764v1, Theorem 1.3; not a discrete theorem asserted in the paper",
        EvidenceKind.MANUFACTURED_SOLUTION,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "CCP25-h1-noncompact-decomposition",
        PAPER.id,
        "For every form degree k on HN(-a^2), a >= 0, H1 k-forms split uniquely and "
        "H1-orthogonally into the H1 closures of compactly supported exact and coexact "
        "forms plus an L2 harmonic k-form.",
        "arXiv:1812.11764v1, Theorem 1.3 and equation (1.1)",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "geometry": "space form HN(-a^2), including a = 0",
            "degree": "general k-form",
            "closures": "H1 closures of d Lambda_c^(k-1) and d* Lambda_c^(k+1)",
            "harmonic summand": "L2 harmonic k-forms, which the paper proves lie in H1",
        },
    ),
)


def run() -> tuple[ClaimResult, ...]:
    d0 = jnp.asarray(((-1.0, 1.0, 0.0), (0.0, -1.0, 1.0), (-1.0, 0.0, 1.0)))
    d1 = jnp.asarray(((1.0, 1.0, -1.0),))
    complex = DiscreteDeRhamComplex(d0, d1, jnp.eye(3), jnp.eye(3), jnp.eye(1))
    value = jnp.asarray((0.4, -0.2, 0.7))
    pieces = hodge_decomposition(complex, value)
    residual = float(jnp.linalg.norm(pieces.reconstruct() - value))
    complex_residual = float(jnp.linalg.norm(complex.complex_residual()))
    passed = residual < 1.0e-12 and complex_residual < 1.0e-12
    return (
        ClaimResult(
            CLAIMS[0].id,
            passed,
            {"reconstruction_residual": residual, "d_squared_residual": complex_residual},
        ),
    )
