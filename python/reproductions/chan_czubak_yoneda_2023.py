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
        "arXiv:2203.16050v1, Theorem 1.1, equations (1.4)--(1.5), with the component proof in Section 2",
        EvidenceKind.POINTWISE_IDENTITY,
        ClaimStatus.CATALOGUED,
        {"surface": "axisymmetric ellipsoid"},
    ),
    Claim(
        "CCY23-eccentricity-expansion",
        PAPER.id,
        "The candidate admits the stated expansion in ellipsoid eccentricity.",
        "arXiv:2203.16050v1, Section 5, equations (5.2)--(5.9)",
        EvidenceKind.SYMBOLIC_IDENTITY,
        ClaimStatus.CATALOGUED,
    ),
)
