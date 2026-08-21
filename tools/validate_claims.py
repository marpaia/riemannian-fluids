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

from validate_literature import validate_archive  # noqa: E402

from reproductions import MODULES  # noqa: E402

FORMALIZATION_STATES = frozenset(
    {
        "specified",
        "contract-checked",
        "proved-fragment",
        "project-proved",
        "formally-reproduced",
    }
)

LEAN_CONTRACT_RELATIONSHIPS = frozenset(
    {
        "proved-core",
        "conditional-theorem",
        "interface-theorem",
        "source-signature",
        "signed-to-analysis-positive-crosswalk",
    }
)

CORPUS_ORIGINS = frozenset({"source", "source-specialization", "project"})
CORPUS_ASSERTION_KINDS = frozenset(
    {"theorem", "identity", "heuristic", "constructed-example", "evidence-gate"}
)
CORPUS_VERIFICATION_TARGETS = frozenset(
    {
        "source-proof",
        "source-specialization-proof",
        "heuristic-reconstruction",
        "project-proof",
        "computational-validation",
    }
)
CORPUS_ATOMICITY = frozenset({"atomic", "compound-needs-split"})
OBLIGATION_STATES = frozenset({"specified", "contract-checked", "proved"})


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
    archive_count = validate_archive()
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

    claim_ids = {
        claim["id"]
        for paper in registry["papers"]
        for claim in paper["claims"]
    }
    corpus = json.loads((ROOT / "claims" / "corpus.json").read_text())
    if corpus.get("schema_version") != 1:
        raise SystemExit("claims/corpus.json has an unsupported schema version")
    release = corpus.get("release", {})
    if release.get("paper_count") != len(registry["papers"]):
        raise SystemExit("claims/corpus.json paper_count disagrees with registry.json")
    if release.get("claim_count") != len(claim_ids):
        raise SystemExit("claims/corpus.json claim_count disagrees with registry.json")
    vocabulary = corpus.get("vocabularies", {})
    expected_vocabulary = {
        "origin": CORPUS_ORIGINS,
        "assertion_kind": CORPUS_ASSERTION_KINDS,
        "verification_target": CORPUS_VERIFICATION_TARGETS,
        "atomicity": CORPUS_ATOMICITY,
    }
    for field, expected_values in expected_vocabulary.items():
        if set(vocabulary.get(field, [])) != expected_values:
            raise SystemExit(
                f"claims/corpus.json declares the wrong {field} vocabulary"
            )

    corpus_entries = corpus.get("claims", [])
    corpus_by_id = {entry["id"]: entry for entry in corpus_entries}
    if len(corpus_by_id) != len(corpus_entries):
        raise SystemExit("claims/corpus.json contains duplicate claim IDs")
    if set(corpus_by_id) != claim_ids:
        missing = sorted(claim_ids - set(corpus_by_id))
        extra = sorted(set(corpus_by_id) - claim_ids)
        raise SystemExit(
            f"corpus classification mismatch: missing={missing}, extra={extra}"
        )
    for claim_id, entry in corpus_by_id.items():
        origin = entry.get("origin")
        assertion_kind = entry.get("assertion_kind")
        verification_target = entry.get("verification_target")
        atomicity = entry.get("atomicity")
        if origin not in CORPUS_ORIGINS:
            raise SystemExit(f"{claim_id} has unknown corpus origin {origin!r}")
        if assertion_kind not in CORPUS_ASSERTION_KINDS:
            raise SystemExit(
                f"{claim_id} has unknown assertion kind {assertion_kind!r}"
            )
        if verification_target not in CORPUS_VERIFICATION_TARGETS:
            raise SystemExit(
                f"{claim_id} has unknown verification target {verification_target!r}"
            )
        if atomicity not in CORPUS_ATOMICITY:
            raise SystemExit(f"{claim_id} has unknown atomicity {atomicity!r}")

        if origin == "source":
            expected_target = (
                "heuristic-reconstruction"
                if assertion_kind == "heuristic"
                else "source-proof"
            )
        elif origin == "source-specialization":
            expected_target = "source-specialization-proof"
        else:
            expected_target = (
                "computational-validation"
                if assertion_kind == "evidence-gate"
                else "project-proof"
            )
        if verification_target != expected_target:
            raise SystemExit(
                f"{claim_id} has verification target {verification_target!r}; "
                f"expected {expected_target!r} from its origin and assertion kind"
            )

        parent_claims = entry.get("parent_claims", [])
        if not isinstance(parent_claims, list) or len(parent_claims) != len(
            set(parent_claims)
        ):
            raise SystemExit(f"{claim_id} has invalid or duplicate parent claims")
        unknown_parents = sorted(set(parent_claims) - claim_ids)
        if unknown_parents:
            raise SystemExit(
                f"{claim_id} has unknown parent claims: {unknown_parents}"
            )
        if claim_id in parent_claims:
            raise SystemExit(f"{claim_id} cannot be its own parent claim")
        if origin != "source" and not parent_claims:
            raise SystemExit(
                f"{claim_id} is {origin!r} but has no parent claim"
            )

    visit_state: dict[str, int] = {}

    def visit_parent_graph(claim_id: str) -> None:
        state = visit_state.get(claim_id, 0)
        if state == 1:
            raise SystemExit(f"corpus parent graph contains a cycle at {claim_id}")
        if state == 2:
            return
        visit_state[claim_id] = 1
        for parent_id in corpus_by_id[claim_id].get("parent_claims", []):
            visit_parent_graph(parent_id)
        visit_state[claim_id] = 2

    for claim_id in claim_ids:
        visit_parent_graph(claim_id)

    source_ancestry: dict[str, bool] = {}

    def reaches_source(claim_id: str) -> bool:
        if claim_id in source_ancestry:
            return source_ancestry[claim_id]
        entry = corpus_by_id[claim_id]
        result = entry["origin"] == "source" or any(
            reaches_source(parent_id)
            for parent_id in entry.get("parent_claims", [])
        )
        source_ancestry[claim_id] = result
        return result

    for claim_id, entry in corpus_by_id.items():
        if entry["origin"] != "source" and not reaches_source(claim_id):
            raise SystemExit(f"{claim_id} has no ancestry path to a source claim")

    obligations = json.loads((ROOT / "claims" / "obligations.json").read_text())
    if obligations.get("schema_version") != 1:
        raise SystemExit("claims/obligations.json has an unsupported schema version")
    if set(obligations.get("states", [])) != OBLIGATION_STATES:
        raise SystemExit("claims/obligations.json declares the wrong state vocabulary")
    split_entries = obligations.get("splits", [])
    splits_by_parent = {entry["parent_id"]: entry for entry in split_entries}
    if len(splits_by_parent) != len(split_entries):
        raise SystemExit("claims/obligations.json contains duplicate parent IDs")
    compound_ids = {
        claim_id
        for claim_id, entry in corpus_by_id.items()
        if entry["atomicity"] == "compound-needs-split"
    }
    if set(splits_by_parent) != compound_ids:
        missing = sorted(compound_ids - set(splits_by_parent))
        extra = sorted(set(splits_by_parent) - compound_ids)
        raise SystemExit(
            f"atomic obligation coverage mismatch: missing={missing}, extra={extra}"
        )
    obligation_ids: set[str] = set()
    obligations_by_id: dict[str, dict[str, object]] = {}
    obligation_count = 0
    for parent_id, split in splits_by_parent.items():
        children = split.get("obligations", [])
        if len(children) < 2:
            raise SystemExit(
                f"{parent_id} is compound but has fewer than two atomic obligations"
            )
        expected_target = corpus_by_id[parent_id]["verification_target"]
        for child in children:
            obligation_count += 1
            child_id = child.get("id")
            if not child_id or child_id in obligation_ids or child_id in claim_ids:
                raise SystemExit(
                    f"{parent_id} has a missing, duplicate, or registry-colliding obligation ID"
                )
            obligation_ids.add(child_id)
            obligations_by_id[child_id] = child
            for field in ("statement", "locator"):
                if not child.get(field):
                    raise SystemExit(f"{child_id} is missing {field}")
            if child.get("verification_target") != expected_target:
                raise SystemExit(
                    f"{child_id} does not inherit verification target {expected_target!r}"
                )
            state = child.get("state")
            if state not in OBLIGATION_STATES:
                raise SystemExit(f"{child_id} has invalid obligation state {state!r}")
            if state != "specified" and not (
                child.get("lean_module") and child.get("declaration")
            ):
                raise SystemExit(
                    f"{child_id} is {state!r} without a Lean declaration"
                )

    if formalization.get("schema_version") != 3:
        raise SystemExit("claims/formalization.json has an unsupported schema version")
    if set(formalization.get("states", [])) != FORMALIZATION_STATES:
        raise SystemExit("claims/formalization.json declares the wrong state vocabulary")
    proof_targets = {
        "source-proof",
        "source-specialization-proof",
        "project-proof",
    }
    atomic_claim_ids = {
        claim_id
        for claim_id, entry in corpus_by_id.items()
        if entry["atomicity"] == "atomic"
        and entry["verification_target"] in proof_targets
    }
    proof_unit_ids = atomic_claim_ids | obligation_ids
    if set(entries_by_id) != proof_unit_ids:
        missing = sorted(proof_unit_ids - set(entries_by_id))
        extra = sorted(set(entries_by_id) - proof_unit_ids)
        raise SystemExit(
            f"atomic proof-status coverage mismatch: missing={missing}, extra={extra}"
        )
    verification_target_by_id = {
        claim_id: corpus_by_id[claim_id]["verification_target"]
        for claim_id in atomic_claim_ids
    }
    for split in split_entries:
        for child in split["obligations"]:
            verification_target_by_id[child["id"]] = child["verification_target"]

    contract_entries = lean_contracts.get("claims", [])
    if lean_contracts.get("schema_version") != 3:
        raise SystemExit("claims/lean-contracts.json has an unsupported schema version")
    contracts_by_id = {entry["id"]: entry for entry in contract_entries}
    if len(contracts_by_id) != len(contract_entries):
        raise SystemExit("claims/lean-contracts.json contains duplicate claim IDs")
    if not set(contracts_by_id) <= proof_unit_ids:
        extra = sorted(set(contracts_by_id) - proof_unit_ids)
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
        relationship = contract["relationship"]
        if relationship not in LEAN_CONTRACT_RELATIONSHIPS:
            allowed = ", ".join(sorted(LEAN_CONTRACT_RELATIONSHIPS))
            raise SystemExit(
                f"{claim_id} has unknown Lean crosswalk relationship "
                f"{relationship!r}; allowed values: {allowed}"
            )
        dependencies = contract.get("dependencies")
        if (
            not isinstance(dependencies, list)
            or not dependencies
            or not all(isinstance(item, str) and item for item in dependencies)
            or len(dependencies) != len(set(dependencies))
        ):
            raise SystemExit(
                f"{claim_id} must name a nonempty, duplicate-free dependency route"
            )

    for claim_id, entry in entries_by_id.items():
        state = entry.get("state")
        if state not in FORMALIZATION_STATES:
            raise SystemExit(f"{claim_id} has invalid formalization state {state!r}")
        if state != "specified" and not (
            entry.get("lean_module") and entry.get("declaration")
        ):
            raise SystemExit(
                f"{claim_id} is {state!r} without a Lean declaration"
            )
        if state != "specified":
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
        elif claim_id in contracts_by_id:
            raise SystemExit(
                f"{claim_id} has a Lean crosswalk but remains merely specified"
            )
        elif entry.get("lean_module") or entry.get("declaration"):
            raise SystemExit(
                f"{claim_id} is specified but already names a Lean declaration"
            )
        if state == "formally-reproduced":
            if verification_target_by_id[claim_id] not in {
                "source-proof",
                "source-specialization-proof",
            }:
                raise SystemExit(
                    f"{claim_id} is formally reproduced but is not a source proof target"
                )
        if (
            state == "project-proved"
            and verification_target_by_id[claim_id] != "project-proof"
        ):
            raise SystemExit(
                f"{claim_id} is project-proved but is not a project proof target"
            )

    source_proof_unit_ids = {
        claim_id
        for claim_id in proof_unit_ids
        if verification_target_by_id[claim_id] == "source-proof"
    }
    for claim_id in sorted(source_proof_unit_ids):
        if entries_by_id[claim_id]["state"] == "specified":
            raise SystemExit(
                f"M1 source-signature coverage is incomplete at {claim_id}"
            )
        if claim_id not in contracts_by_id:
            raise SystemExit(
                f"M1 dependency routing is incomplete at {claim_id}"
            )
        obligation = obligations_by_id.get(claim_id)
        if obligation is not None and obligation["state"] == "specified":
            raise SystemExit(
                f"M1 atomic obligation remains merely specified at {claim_id}"
            )

    claim_count = len(claim_ids)
    print(
        f"validated {len(registry['papers'])} papers ({archive_count} pinned PDFs), "
        f"{claim_count} claims, "
        f"{len(corpus_by_id)} corpus classifications, "
        f"{obligation_count} atomic obligations from {len(compound_ids)} splits, "
        f"{len(contracts_by_id)} selective Lean crosswalk entries, and "
        f"{len(proof_unit_ids)} atomic proof-status records; "
        f"M1 covers all {len(source_proof_unit_ids)} atomic source-proof units"
    )


if __name__ == "__main__":
    main()
