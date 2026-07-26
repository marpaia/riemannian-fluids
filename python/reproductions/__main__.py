"""List registered claims or run one paper's executable evidence."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence
from dataclasses import asdict

from reproductions import MODULES, find_paper


def _catalog() -> list[dict[str, object]]:
    return [
        {
            "paper": asdict(module.paper),
            "claims": [asdict(claim) for claim in module.claims],
            "runnable": module.run is not None,
        }
        for module in MODULES
    ]


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper", nargs="?", help="paper id to run; omit to list the census")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)
    if args.paper is None:
        catalog = _catalog()
        if args.as_json:
            print(json.dumps(catalog, indent=2, sort_keys=True))
            return
        for entry in catalog:
            paper = entry["paper"]
            claims = entry["claims"]
            assert isinstance(paper, dict) and isinstance(claims, list)
            statuses = ", ".join(str(claim["status"]) for claim in claims)
            print(f"{paper['id']:6s} {paper['year']}  {paper['title']} [{statuses}]")
        return

    module = find_paper(args.paper)
    if module.run is None:
        parser.error(f"{args.paper} has no executable claims yet")
    results = list(module.run())
    registered = {claim.id for claim in module.claims}
    if any(result.claim_id not in registered for result in results):
        raise ValueError("paper runner returned an unregistered claim id")
    if args.as_json:
        print(json.dumps([asdict(result) for result in results], indent=2, sort_keys=True))
    else:
        for result in results:
            state = "PASS" if result.passed else "FAIL"
            print(f"{state} {result.claim_id}: {dict(result.measurements)}")
    if not all(result.passed for result in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
