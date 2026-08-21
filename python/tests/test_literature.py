from __future__ import annotations

from reproductions import MODULES
from riemannian_fluids.validation import ClaimStatus, validate_registry


def test_literature_registry_is_unique_and_honest() -> None:
    validate_registry(MODULES)
    assert len(MODULES) == 11
    assert all(module.claims for module in MODULES)
    assert any(claim.status is ClaimStatus.ANALYTIC_ONLY for module in MODULES for claim in module.claims)


def test_validated_claims_declare_their_evidence_scope() -> None:
    validated = [claim for module in MODULES for claim in module.claims if claim.status is ClaimStatus.VALIDATED]
    assert validated
    assert all(claim.geometry_coverage and claim.sample_coverage for claim in validated)


def test_non_umbilic_claims_cover_more_than_the_round_sphere() -> None:
    for claim_id in ("CCD17-divfree-def-hodge", "WBS26-local-interpolating-family", "WBS26-two-wall-profile", "WBK26-lie-strain"):
        claim = next(claim for module in MODULES for claim in module.claims if claim.id == claim_id)
        assert "spheroid" in claim.geometry_coverage or "torus" in claim.geometry_coverage


def test_all_current_executable_claims_pass() -> None:
    results = [result for module in MODULES if module.run for result in module.run()]
    assert results
    assert all(result.passed for result in results)
