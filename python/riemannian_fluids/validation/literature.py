"""Traceable paper, claim, and computational-evidence records."""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from enum import StrEnum
from types import ModuleType


class ClaimStatus(StrEnum):
    CATALOGUED = "catalogued"
    EXECUTABLE = "executable"
    VALIDATED = "validated"
    ANALYTIC_ONLY = "analytic-only"


class EvidenceKind(StrEnum):
    SYMBOLIC_IDENTITY = "symbolic-identity"
    POINTWISE_IDENTITY = "pointwise-identity"
    MANUFACTURED_SOLUTION = "manufactured-solution"
    WEAK_FORM = "weak-form"
    MESH_REFINEMENT = "mesh-refinement"
    SPECTRAL_CONVERGENCE = "spectral-convergence"
    THIN_SHELL_CONVERGENCE = "thin-shell-convergence"
    CONSTRUCTIVE_WITNESS = "constructive-witness"
    ANALYTIC_THEOREM = "analytic-theorem"


@dataclass(frozen=True)
class Paper:
    id: str
    title: str
    authors: tuple[str, ...]
    year: int
    url: str
    version: str
    scope: str

    def __post_init__(self) -> None:
        if not self.id or not self.title or not self.authors:
            raise ValueError("paper id, title, and authors are required")
        if not self.url.startswith("https://"):
            raise ValueError("paper URL must be an HTTPS source")


@dataclass(frozen=True)
class Claim:
    id: str
    paper_id: str
    statement: str
    locator: str
    evidence: EvidenceKind
    status: ClaimStatus
    assumptions: Mapping[str, str] = field(default_factory=dict)
    convention: str = "analysis-positive-v1"

    def __post_init__(self) -> None:
        if not self.id.startswith(f"{self.paper_id}-"):
            raise ValueError("claim ids must begin with '<paper-id>-' for provenance")
        if not self.locator:
            raise ValueError("every claim needs an equation, theorem, or section locator")
        if self.status is ClaimStatus.VALIDATED and self.evidence is EvidenceKind.ANALYTIC_THEOREM:
            raise ValueError("a computational run cannot validate an analytic theorem")


@dataclass(frozen=True)
class ClaimResult:
    claim_id: str
    passed: bool
    measurements: Mapping[str, float | int | str]
    note: str = ""


PaperRunner = Callable[[], Sequence[ClaimResult]]


@dataclass(frozen=True)
class PaperModule:
    paper: Paper
    claims: tuple[Claim, ...]
    run: PaperRunner | None = None


def paper_module(module: ModuleType) -> PaperModule:
    paper = module.PAPER
    claims = tuple(module.CLAIMS)
    runner = getattr(module, "run", None)
    if not isinstance(paper, Paper) or not all(isinstance(claim, Claim) for claim in claims):
        raise TypeError("paper modules must define PAPER: Paper and CLAIMS: tuple[Claim, ...]")
    if any(claim.paper_id != paper.id for claim in claims):
        raise ValueError(f"{paper.id} contains a claim belonging to another paper")
    return PaperModule(paper, claims, runner)


def validate_registry(modules: Sequence[PaperModule]) -> None:
    paper_ids = [module.paper.id for module in modules]
    claim_ids = [claim.id for module in modules for claim in module.claims]
    if len(set(paper_ids)) != len(paper_ids):
        raise ValueError("paper ids must be unique")
    if len(set(claim_ids)) != len(claim_ids):
        raise ValueError("claim ids must be unique")
    for module in modules:
        executable = any(
            claim.status in {ClaimStatus.EXECUTABLE, ClaimStatus.VALIDATED}
            for claim in module.claims
        )
        if executable and module.run is None:
            raise ValueError(f"{module.paper.id} has executable claims but no run()")
