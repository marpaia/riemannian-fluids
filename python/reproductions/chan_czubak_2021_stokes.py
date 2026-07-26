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
        "A nontrivial H1_0 steady Stokes solution exists on the hyperbolic exterior domain.",
        "main Stokes theorem",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
    ),
    Claim(
        "CC21-nontrivial-navier-stokes-exterior",
        PAPER.id,
        "A nontrivial steady Navier--Stokes solution exists on the same exterior domain.",
        "main Navier--Stokes theorem",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
    ),
)
