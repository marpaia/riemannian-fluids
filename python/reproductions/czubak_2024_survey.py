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
        "The rough/Bochner, Hodge, and deformation constructions are inequivalent in general on curved Riemannian manifolds.",
        "Notices AMS 71(1), pp. 8-16, survey comparison of the candidate viscosity operators",
        EvidenceKind.ANALYTIC_THEOREM,
        ClaimStatus.CATALOGUED,
        assumptions={
            "formal witness": "a curved Riemannian setting on which the three operator maps are pairwise distinct",
            "convention": "rough, Hodge, and deformation operators translated to analysis-positive-v1",
        },
    ),
)
