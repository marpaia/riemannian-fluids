"""Audit the checked, thematic RiemannianFluids Lean library."""

from __future__ import annotations

import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
LIBRARY_ROOT = LEAN_ROOT / "RiemannianFluids.lean"
LEAN_CROSSWALK = ROOT / "claims" / "lean-contracts.json"
ATOMIC_OBLIGATIONS = ROOT / "claims" / "obligations.json"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)
FORBIDDEN_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected)\s+)*(?:axiom|constant)\s+"
    r"[A-Za-z_][A-Za-z0-9_']*|\bsorry\b|\badmit\b"
)
AXIOM_LIST_RE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
NO_AXIOMS_RE = re.compile(r"does not depend on any axioms")


def module_path(module: str) -> Path | None:
    candidate = LEAN_ROOT / (module.replace(".", "/") + ".lean")
    return candidate if candidate.exists() else None


def import_closure(root: Path) -> set[Path]:
    pending = [root]
    closure: set[Path] = set()
    while pending:
        path = pending.pop()
        if path in closure:
            continue
        closure.add(path)
        for module in IMPORT_RE.findall(path.read_text()):
            imported = module_path(module)
            if imported is not None:
                pending.append(imported)
    return closure


def strip_comments_and_strings(source: str) -> str:
    """Blank Lean comments and strings while retaining source line positions."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if block_depth:
            if pair == "/-":
                output.extend("  ")
                block_depth += 1
                index += 2
            elif pair == "-/":
                output.extend("  ")
                block_depth -= 1
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            if char == "\\" and index + 1 < len(source):
                output.extend("  ")
                index += 2
            elif char == '"':
                output.append(" ")
                in_string = False
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if pair == "--":
            newline = source.find("\n", index)
            if newline == -1:
                output.extend(" " * (len(source) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        elif pair == "/-":
            output.extend("  ")
            block_depth = 1
            index += 2
        elif char == '"':
            output.append(" ")
            in_string = True
            index += 1
        else:
            output.append(char)
            index += 1
    return "".join(output)


def audit_sources(paths: set[Path]) -> None:
    failures: list[str] = []
    for path in sorted(paths):
        source = strip_comments_and_strings(path.read_text())
        for match in FORBIDDEN_RE.finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(
                f"{path.relative_to(ROOT)}:{line}: forbidden "
                f"`{match.group(0).strip()}`"
            )
    if failures:
        raise SystemExit("Lean source audit failed:\n" + "\n".join(failures))


def crosswalk_declarations() -> list[tuple[str, str, str]]:
    registry = json.loads(LEAN_CROSSWALK.read_text())
    declarations: list[tuple[str, str, str]] = []
    for entry in registry["claims"]:
        module = entry["lean_module"]
        declaration = entry["declaration"]
        path = module_path(module)
        if path is None:
            raise SystemExit(f"{entry['id']} names missing Lean module {module}")
        local_name = declaration.rsplit(".", 1)[-1]
        declared_names = set(DECL_RE.findall(strip_comments_and_strings(path.read_text())))
        if local_name not in declared_names:
            raise SystemExit(
                f"{entry['id']} maps {declaration} to {module}, "
                "but that module does not own the declaration"
            )
        declarations.append((entry["id"], module, declaration))
    return declarations


def obligation_declarations() -> list[tuple[str, str, str]]:
    """Return contract-checked and proved atomic obligation declarations."""

    registry = json.loads(ATOMIC_OBLIGATIONS.read_text())
    declarations: list[tuple[str, str, str]] = []
    for split in registry["splits"]:
        for entry in split["obligations"]:
            if entry["state"] == "specified":
                continue
            module = entry["lean_module"]
            declaration = entry["declaration"]
            path = module_path(module)
            if path is None:
                raise SystemExit(
                    f"{entry['id']} names missing Lean module {module}"
                )
            local_name = declaration.rsplit(".", 1)[-1]
            declared_names = set(
                DECL_RE.findall(strip_comments_and_strings(path.read_text()))
            )
            if local_name not in declared_names:
                raise SystemExit(
                    f"{entry['id']} maps {declaration} to {module}, "
                    "but that module does not own the declaration"
                )
            declarations.append((entry["id"], module, declaration))
    return declarations


def parse_print_axioms(segment: str) -> frozenset[str]:
    """Parse one delimited ``#print axioms`` response, failing closed on drift."""

    lists = AXIOM_LIST_RE.findall(segment)
    no_axioms = NO_AXIOMS_RE.findall(segment)
    if len(lists) + len(no_axioms) != 1:
        raise ValueError("expected exactly one recognizable #print axioms response")
    if no_axioms:
        return frozenset()
    names = re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", lists[0])
    if not names:
        raise ValueError("axiom list was present but empty or unparsable")
    return frozenset(names)


def audit_crosswalk_axioms(declarations: list[tuple[str, str, str]]) -> None:
    lines = ["import RiemannianFluids", ""]
    for claim_id, module, declaration in declarations:
        lines.extend(
            [
                f"-- {claim_id} via {module}",
                f"#check {declaration}",
                f'#eval IO.println "CROSSWALK_BEGIN {claim_id}"',
                f"#print axioms {declaration}",
                f'#eval IO.println "CROSSWALK_END {claim_id}"',
            ]
        )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as handle:
        handle.write("\n".join(lines) + "\n")
        audit_path = Path(handle.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(audit_path)],
            cwd=LEAN_ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
    finally:
        audit_path.unlink(missing_ok=True)
    output = result.stdout + result.stderr
    if result.returncode:
        raise SystemExit(f"Lean crosswalk audit failed:\n{output}")
    failures: list[str] = []
    for claim_id, _, _ in declarations:
        begin = f"CROSSWALK_BEGIN {claim_id}"
        end = f"CROSSWALK_END {claim_id}"
        if begin not in output or end not in output:
            failures.append(f"missing axiom-audit sentinel for {claim_id}")
            continue
        segment = output.split(begin, 1)[1].split(end, 1)[0]
        try:
            axioms = parse_print_axioms(segment)
        except ValueError as error:
            failures.append(f"{claim_id} has an unparsable axiom report: {error}")
            continue
        unexpected = sorted(axioms - ALLOWED_AXIOMS)
        if unexpected:
            failures.append(
                f"{claim_id} reaches axioms outside the allowlist: {unexpected}"
            )
    if failures:
        raise SystemExit("Lean crosswalk axiom audit failed:\n" + "\n".join(failures))


def main() -> None:
    library = import_closure(LIBRARY_ROOT)
    audit_sources(library)
    crosswalks = crosswalk_declarations()
    obligations = obligation_declarations()
    crosswalk_ids = {claim_id for claim_id, _, _ in crosswalks}
    uncovered_obligations = [
        declaration
        for declaration in obligations
        if declaration[0] not in crosswalk_ids
    ]
    audit_crosswalk_axioms(crosswalks + uncovered_obligations)
    print(
        f"validated thematic Lean closure: {len(library)} files, "
        f"0 placeholders, {len(crosswalks)} selective literature crosswalks, and "
        f"{len(obligations)} atomic obligation contracts"
    )


if __name__ == "__main__":
    main()
