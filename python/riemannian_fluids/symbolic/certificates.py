"""Typed certificates and derivation ledgers for symbolic results.

Certificates grade what a result establishes: ``ExactCertificate`` carries a
closed form, ``FiniteCertificate`` proves convergence without one,
``DivergentCertificate`` refutes integrability, and ``UnresolvedCertificate``
records an honest failure to decide.  Certificates compose by weakest link;
no code path upgrades a grade.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class DerivationStep:
    kind: str
    description: str
    before_ops: int
    after_ops: int


@dataclass(frozen=True)
class DerivationLedger:
    steps: tuple[DerivationStep, ...] = ()

    def record(self, kind: str, description: str, before_ops: int, after_ops: int) -> DerivationLedger:
        return DerivationLedger((*self.steps, DerivationStep(kind, description, before_ops, after_ops)))

    def render(self) -> str:
        return "\n".join(f"[{step.kind}] {step.description} ({step.before_ops} ops -> {step.after_ops} ops)" for step in self.steps)


@dataclass(frozen=True)
class ExactCertificate:
    assumptions: tuple[str, ...]


@dataclass(frozen=True)
class FiniteCertificate:
    assumptions: tuple[str, ...]
    enclosure: float | None = None


@dataclass(frozen=True)
class DivergentCertificate:
    assumptions: tuple[str, ...]
    reason: str


@dataclass(frozen=True)
class UnresolvedCertificate:
    reason: str


type Certificate = ExactCertificate | FiniteCertificate | DivergentCertificate | UnresolvedCertificate
