"""Liouville claims of Chan--Czubak (2015)."""

from riemannian_fluids.validation import Claim, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CC15",
    "Liouville theorems for the Stationary Navier Stokes equation on a hyperbolic space",
    ("Chi Hin Chan", "Magdalena Czubak"),
    2015,
    "https://arxiv.org/abs/1501.04928",
    "v1",
    "Stationary Navier--Stokes Liouville theorems on hyperbolic spaces.",
)
CLAIMS = (
    Claim(
        "CC15-stationary-liouville",
        PAPER.id,
        "Finite-Dirichlet stationary solutions satisfy the stated hyperbolic Liouville results.",
        "main theorems",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
    ),
)
