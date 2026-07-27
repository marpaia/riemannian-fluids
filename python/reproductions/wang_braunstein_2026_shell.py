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
        "arXiv:2605.20589v3, Lemma 3.1, Proposition 3.2, and Theorem 3.3, equations (12)--(18)",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "WBS26-two-wall-profile",
        PAPER.id,
        "A finite-thickness tangential profile satisfies both wall laws.",
        "arXiv:2605.20589v3, Proposition 3.2 and Section 3.4, equations (13)--(19)",
        EvidenceKind.MANUFACTURED_SOLUTION,
        ClaimStatus.VALIDATED,
    ),
    Claim(
        "WBS26-mosco-resolvent-spectrum",
        PAPER.id,
        "For torus-type surfaces of revolution and for both stress-free/deformation and "
        "vorticity-free/Hodge wall conditions, the thin-shell forms Mosco-converge; the "
        "associated nonnegative self-adjoint operators have strongly convergent resolvents "
        "and semigroups uniformly on compact time intervals; eigenvalues converge with "
        "multiplicity on each fixed azimuthal mode and, by the uniform high-mode gap, for "
        "the full spectrum without spectral pollution.",
        "arXiv:2605.20589v3, Theorem 4.5 and Corollary 4.6",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "surface": "torus-type surface of revolution",
            "wall conditions": "stress-free/deformation and vorticity-free/Hodge",
            "spectral scope": "fixed-mode and full-spectrum convergence with multiplicity; no high-mode pollution",
            "framework": "Kuwae-Shioya varying Hilbert spaces",
        },
    ),
    Claim(
        "WBS26-resolved-volume-shell",
        PAPER.id,
        "A resolved curved 3D shell converges after transverse averaging to the selected "
        "surface operator, with mesh convergence at fixed thickness established separately "
        "from thickness convergence.",
        "Project numerical gate motivated by arXiv:2605.20589v3, Theorem 4.5; not a numerical theorem asserted in the paper",
        EvidenceKind.THIN_SHELL_CONVERGENCE,
        ClaimStatus.CATALOGUED,
        {
            "required limits": "mesh size h -> 0 at fixed epsilon, then thickness epsilon -> 0",
            "geometry": "resolved curved volume shell rather than a normal-fibre surrogate",
        },
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
