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

    for claim_id, entry in entries_by_id.items():
        state = entry.get("state")
        if state not in FORMALIZATION_STATES:
            raise SystemExit(f"{claim_id} has invalid formalization state {state!r}")
        if state == "formally-reproduced" and not (
            entry.get("lean_module") and entry.get("declaration")
        ):
            raise SystemExit(
                f"{claim_id} is formally reproduced without a Lean declaration"
            )

    claim_count = sum(len(paper["claims"]) for paper in registry["papers"])
    print(
        f"validated {len(registry['papers'])} papers, {claim_count} claims, "
        f"and {len(analytic_ids)} analytic formalization records"
    )


if __name__ == "__main__":
    main()

