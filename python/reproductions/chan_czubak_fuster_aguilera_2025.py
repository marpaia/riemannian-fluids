"""Four ellipsoid candidates of Chan--Czubak--Fuster Aguilera (2025)."""

import jax.numpy as jnp

from riemannian_fluids.geometry import intrinsic_gaussian_curvature, metric, sphere, vector_norm
from riemannian_fluids.operators import deformation_laplacian, hodge_laplacian
from riemannian_fluids.tensors import (
    gradient,
    lie_bracket,
    raised_lie_derivative_one_form,
    stream_vector_field,
)
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
        {"surface": "round sphere"},
    ),
    Claim(
        "CCF25-averaging-dependence",
        PAPER.id,
        "The scaling-direction thin-shell result depends on the averaging prescription.",
        "arXiv:2511.10579v1, Theorems 1.1, 1.3, and 1.6 with Remark 1.8; the paper labels these limits heuristic",
        EvidenceKind.THIN_SHELL_CONVERGENCE,
        ClaimStatus.CATALOGUED,
        {"surface": "axisymmetric ellipsoid"},
    ),
)


def run() -> tuple[ClaimResult, ...]:
    surface = sphere()
    velocity = stream_vector_field(surface, lambda q: jnp.sin(q[0]) ** 2 * jnp.cos(2 * q[1]))
    generator = lambda q: -0.25 * gradient(  # noqa: E731
        surface, lambda x: jnp.log(intrinsic_gaussian_curvature(surface, x)), q
    )
    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)
    deformation = deformation_laplacian(surface, velocity, q)
    hodge = hodge_laplacian(surface, velocity, q)
    component = (velocity(q) @ metric(surface, q) @ generator(q)) * generator(q)
    candidates = (
        deformation + lie_bracket(generator, velocity, q) + 2.0 * component,
        hodge + raised_lie_derivative_one_form(surface, generator, velocity, q),
        deformation + lie_bracket(generator, velocity, q),
        hodge + raised_lie_derivative_one_form(surface, generator, velocity, q) - 2.0 * component,
    )
    residual = max(
        float(vector_norm(surface, candidate - endpoint, q))
        for candidate, endpoint in zip(
            candidates,
            (deformation, hodge, deformation, hodge),
            strict=True,
        )
    )
    return (ClaimResult(CLAIMS[0].id, residual < 1.0e-10, {"max_absolute_residual": residual}),)
