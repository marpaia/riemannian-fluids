"""Exterior-domain Stokes claims of Chan--Czubak (published 2021)."""

from riemannian_fluids.validation import Claim, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CC21",
    "Antithesis of the Stokes paradox on the hyperbolic plane",
    ("Chi Hin Chan", "Magdalena Czubak"),
    2021,
    "https://arxiv.org/abs/1708.05134",
    "v1; J. Geom. Anal. 2021",
    "Nontrivial steady Stokes and Navier--Stokes flows on a hyperbolic exterior domain.",
)
CLAIMS = (
    Claim(
        "CC21-nontrivial-stokes-exterior",
        PAPER.id,
        "For every R0,a > 0, the exterior of the radius-R0 geodesic ball in H2(-a^2) "
        "admits a nontrivial finite-Dirichlet steady Stokes solution with zero boundary trace "
        "and pressure in L2_loc; the constructed velocity is not a harmonic potential flow.",
        "arXiv:1708.05134v1, Theorems 1.2 and 1.4",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "domain": "Omega(R0) = H2(-a^2) minus the closed geodesic ball, R0,a > 0",
            "boundary": "zero trace",
            "energy": "finite Dirichlet integral",
            "pressure": "L2_loc",
        },
    ),
    Claim(
        "CC21-nontrivial-navier-stokes-exterior",
        PAPER.id,
        "For every R0,a > 0, the same hyperbolic exterior domain admits a nontrivial "
        "finite-Dirichlet steady Navier-Stokes solution with zero boundary trace and pressure "
        "in L2_loc; the constructed velocity is not a harmonic potential flow.",
        "arXiv:1708.05134v1, Theorems 1.3 and 1.4",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "domain": "Omega(R0) = H2(-a^2) minus the closed geodesic ball, R0,a > 0",
            "boundary": "zero trace",
            "energy": "finite Dirichlet integral",
            "pressure": "L2_loc",
        },
    ),
)
