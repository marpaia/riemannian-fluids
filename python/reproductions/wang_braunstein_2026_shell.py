"""Thin-shell operator-selection claims of Wang--Braunstein (2026)."""

import jax.numpy as jnp

from riemannian_fluids.geometry import shape_operator, sphere, vector_norm
from riemannian_fluids.operators import interpolating_viscosity
from riemannian_fluids.shells import (
    ambient_positive_laplacian_tangent,
    matched_wall_jets,
    solve_two_wall_tangential_field,
    wall_residual,
)
from riemannian_fluids.tensors import stream_vector_field
from riemannian_fluids.validation import Claim, ClaimResult, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "WBS26",
    "Boundary conditions select the viscous operator on Riemannian hypersurfaces: formal analysis and rigorous thin-shell limits",
    ("Zhi-Wei Wang", "Samuel L. Braunstein"),
    2026,
    "https://arxiv.org/abs/2605.20589",
    "v3",
    "Wall-condition selection, matched fields, and rigorous thin-shell convergence.",
)
CLAIMS = (
    Claim(
        "WBS26-local-interpolating-family",
        PAPER.id,
        "The tangential ambient operator gives L_Def + 2a Ric + 4a(1-a)S^2.",
        "equations (12)--(17)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "WBS26-two-wall-profile",
        PAPER.id,
        "A finite-thickness tangential profile satisfies both wall laws.",
        "equations (13)--(20)",
        EvidenceKind.MANUFACTURED_SOLUTION,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "WBS26-mosco-resolvent-spectrum",
        PAPER.id,
        "The energy forms converge in the Mosco sense, hence resolvents, semigroups, and spectra converge.",
        "rigorous convergence theorem",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
    ),
    Claim(
        "WBS26-resolved-volume-shell",
        PAPER.id,
        "A resolved curved shell converges after transverse averaging to the selected surface operator.",
        "computational analogue of the thin-shell limit",
        EvidenceKind.THIN_SHELL_CONVERGENCE,
        ClaimStatus.CATALOGUED,
    ),
)


def run() -> tuple[ClaimResult, ...]:
    surface = sphere()
    velocity = stream_vector_field(surface, lambda q: jnp.sin(q[0]) ** 2 * jnp.cos(2 * q[1]))

    def zero(q):
        return jnp.asarray(0.0, dtype=q.dtype)

    q = jnp.asarray((1.1, 0.7), dtype=jnp.float64)
    alpha = 0.5
    jets = matched_wall_jets(surface, velocity, zero, zero, alpha)
    direct = ambient_positive_laplacian_tangent(surface, jets, jnp.ones((6,)), q)
    expected = interpolating_viscosity(surface, velocity, q, alpha)
    identity_residual = float(vector_norm(surface, direct - expected, q))
    shape = shape_operator(surface, q)
    profile = solve_two_wall_tangential_field(shape, velocity(q), 0.1, alpha)
    wall_error = max(float(jnp.linalg.norm(wall_residual(shape, profile, 0.1, alpha, sign))) for sign in (-1, 1))
    return (
        ClaimResult(
            CLAIMS[0].id,
            identity_residual < 1.0e-10,
            {"absolute_residual": identity_residual},
        ),
        ClaimResult(CLAIMS[1].id, wall_error < 1.0e-10, {"max_wall_residual": wall_error}),
    )
