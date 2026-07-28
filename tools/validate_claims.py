"""Validate shared claim provenance against Python and Lean evidence mappings."""

from __future__ import annotations

import json
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PYTHON_ROOT = ROOT / "python"
sys.path.insert(0, str(PYTHON_ROOT))

from reproductions import MODULES  # noqa: E402

FORMALIZATION_STATES = {
    "catalogued",
    "contract-checked",
    "interface-proved",
    "formally-reproduced",
}


def _json_value(value: Any) -> Any:
    """Normalize dataclasses, mappings, tuples, and string enums through JSON."""

    return json.loads(json.dumps(value))


def _python_registry() -> dict[str, object]:
    papers: list[dict[str, object]] = []
    for module in MODULES:
        paper = _json_value(asdict(module.paper))
        paper["claims"] = [_json_value(asdict(claim)) for claim in module.claims]
        papers.append(paper)
    return {"schema_version": 1, "papers": papers}


def main() -> None:
    registry = json.loads((ROOT / "claims" / "registry.json").read_text())
    expected = _python_registry()
    if registry != expected:
        raise SystemExit(
            "claims/registry.json has drifted from the Python claim declarations"
        )

    formalization = json.loads(
        (ROOT / "claims" / "formalization.json").read_text()
    )
    lean_contracts = json.loads(
        (ROOT / "claims" / "lean-contracts.json").read_text()
    )
    entries = formalization.get("claims", [])
    entries_by_id = {entry["id"]: entry for entry in entries}
    if len(entries_by_id) != len(entries):
        raise SystemExit("claims/formalization.json contains duplicate claim IDs")

    analytic_ids = {
        claim["id"]
        for paper in registry["papers"]
        for claim in paper["claims"]
        if claim["evidence"] == "analytic-theorem"
    }
    if set(entries_by_id) != analytic_ids:
        missing = sorted(analytic_ids - set(entries_by_id))
        extra = sorted(set(entries_by_id) - analytic_ids)
        raise SystemExit(
            f"formalization coverage mismatch: missing={missing}, extra={extra}"
        )

    claim_ids = {
        claim["id"]
        for paper in registry["papers"]
        for claim in paper["claims"]
    }
    contract_entries = lean_contracts.get("claims", [])
    contracts_by_id = {entry["id"]: entry for entry in contract_entries}
    if len(contracts_by_id) != len(contract_entries):
        raise SystemExit("claims/lean-contracts.json contains duplicate claim IDs")
    if not set(contracts_by_id) <= claim_ids:
        extra = sorted(set(contracts_by_id) - claim_ids)
        raise SystemExit(
            f"Lean crosswalk contains unknown claims: {extra}"
        )
    for claim_id, contract in contracts_by_id.items():
        if not contract.get("lean_module") or not contract.get("declaration"):
            raise SystemExit(f"{claim_id} has an incomplete Lean crosswalk entry")
        for field in ("intellectual_thread", "relationship", "limitation"):
            if not contract.get(field):
                raise SystemExit(
                    f"{claim_id} Lean crosswalk is missing explanatory field {field}"
                )

    for claim_id, entry in entries_by_id.items():
        state = entry.get("state")
        if state not in FORMALIZATION_STATES:
            raise SystemExit(f"{claim_id} has invalid formalization state {state!r}")
        if state != "catalogued" and not (
            entry.get("lean_module") and entry.get("declaration")
        ):
            raise SystemExit(
                f"{claim_id} is {state!r} without a Lean declaration"
            )
        if state != "catalogued":
            contract = contracts_by_id.get(claim_id)
            if contract is None:
                raise SystemExit(
                    f"{claim_id} is {state!r} but has no selective Lean crosswalk entry"
                )
            if (
                entry["lean_module"] != contract["lean_module"]
                or entry["declaration"] != contract["declaration"]
            ):
                raise SystemExit(
                    f"{claim_id} formalization mapping disagrees with lean-contracts.json"
                )

    claim_count = len(claim_ids)
    print(
        f"validated {len(registry['papers'])} papers, {claim_count} claims, "
        f"{len(contracts_by_id)} selective Lean crosswalk entries, and "
        f"{len(analytic_ids)} analytic formalization records"
    )


if __name__ == "__main__":
    main()
