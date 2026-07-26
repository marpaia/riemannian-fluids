"""Claim census for Chan--Czubak--Yoneda's ellipsoid restriction paper."""

from riemannian_fluids.validation import Claim, ClaimStatus, EvidenceKind, Paper

PAPER = Paper(
    "CCY23",
    "The restriction problem on the ellipsoid",
    ("Chi Hin Chan", "Magdalena Czubak", "Tsuyoshi Yoneda"),
    2023,
    "https://arxiv.org/abs/2203.16050",
    "v1",
    "Invariant restriction formula and its eccentricity expansion on an ellipsoid.",
)
CLAIMS = (
    Claim(
        "CCY23-invariant-restriction",
        PAPER.id,
        "A projected ambient restriction gives an invariant ellipsoid viscosity candidate.",
        "main restriction formula",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.CATALOGUED,
        {"surface": "axisymmetric ellipsoid"},
    ),
    Claim(
        "CCY23-eccentricity-expansion",
        PAPER.id,
        "The candidate admits the stated expansion in ellipsoid eccentricity.",
        "eccentricity expansion section",
        EvidenceKind.SYMBOLIC_IDENTITY,
        ClaimStatus.CATALOGUED,
    ),
)
