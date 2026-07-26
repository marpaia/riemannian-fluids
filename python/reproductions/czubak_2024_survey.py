"""Executable census for Czubak's 2024 viscosity survey."""

from riemannian_fluids.validation import Claim, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CZ24",
    "In Search of the Viscosity Operator on Riemannian Manifolds",
    ("Magdalena Czubak",),
    2024,
    "https://doi.org/10.1090/noti2840",
    "Notices AMS 71(1)",
    "Survey and crosswalk for inequivalent geometric viscosity operators.",
)

CLAIMS = (
    Claim(
        "CZ24-operator-census",
        PAPER.id,
        "Bochner, Hodge, and deformation choices are inequivalent on curved manifolds.",
        "survey discussion of viscosity operators",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.CATALOGUED,
    ),
)
