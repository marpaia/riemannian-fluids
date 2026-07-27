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
        "A smooth divergence-free finite-Dirichlet stationary deformation-viscosity solution "
        "on HN(-a^2) vanishes for N=3,4; for N=2, an additional L-infinity bound makes it "
        "an L2 harmonic gradient; and for N>=5, the same bound implies vanishing.",
        "arXiv:1501.04928v1, Theorem 1.1",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.ANALYTIC_ONLY,
        {
            "geometry": "HN(-a^2), N >= 2 and a > 0",
            "equation": "2 Def* Def u + nabla_u u + dp = 0, d* u = 0",
            "base regularity": "smooth velocity and pressure; finite Dirichlet integral",
            "extra bound": "u in L-infinity for N=2 and N>=5 only",
        },
    ),
)
