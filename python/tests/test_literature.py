from __future__ import annotations

from reproductions import MODULES
from riemannian_fluids.validation import ClaimStatus, validate_registry


def test_literature_registry_is_unique_and_honest() -> None:
    validate_registry(MODULES)
    assert len(MODULES) == 11
    assert all(module.claims for module in MODULES)
    assert any(claim.status is ClaimStatus.ANALYTIC_ONLY for module in MODULES for claim in module.claims)


def test_all_current_executable_claims_pass() -> None:
    results = [result for module in MODULES if module.run for result in module.run()]
    assert results
    assert all(result.passed for result in results)
