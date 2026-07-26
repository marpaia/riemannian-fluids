"""Claim provenance and validation criteria."""

from riemannian_fluids.validation.literature import (
    Claim,
    ClaimResult,
    ClaimStatus,
    EvidenceKind,
    Paper,
    PaperModule,
    paper_module,
    validate_registry,
)
from riemannian_fluids.validation.refinement import monotone_refinement, observed_orders

__all__ = (
    "Claim",
    "ClaimResult",
    "ClaimStatus",
    "EvidenceKind",
    "Paper",
    "PaperModule",
    "monotone_refinement",
    "observed_orders",
    "paper_module",
    "validate_registry",
)
