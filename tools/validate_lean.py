"""Audit the single RiemannianFluids Lean import closure.

The library may contain ``sorry`` only inside source steps tagged
``proof_obligation``. These unfinished steps may depend on earlier source steps. Internal
``proof_assembly`` nodes and literature-facing
``literature_terminal`` declarations must be directly sorry-free and are audited
transitively with ``#print axioms``.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "lean"
LIBRARY_ROOT = LEAN_ROOT / "RiemannianFluids.lean"
LEAN_CONTRACTS = ROOT / "claims" / "lean-contracts.json"
FORMALIZATION = ROOT / "claims" / "formalization.json"

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)
DECL_RE = re.compile(
    r"(?m)^(?P<attrs>(?:[ \t]*@\[[^\]]+\][ \t]*\n)*)"
    r"[ \t]*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)
FORBIDDEN_AXIOM_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected)\s+)*(?:axiom|constant)\s+[A-Za-z_][A-Za-z0-9_']*|\badmit\b"
)
SORRY_RE = re.compile(r"\bsorry\b")
AGGREGATED_SOURCE_STEP_RE = re.compile(r"(?:^|_)(?:lemmas|theorems|equations)_")


@dataclass(frozen=True)
class TaggedDeclaration:
    name: str
    tag: str
    path: Path
    line: int
    has_direct_sorry: bool

    @property
    def full_name(self) -> str:
        return f"RiemannianFluids.{self.name}"


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
    """Replace Lean comments and strings with spaces while preserving newlines."""

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


def declaration_segments(source: str) -> list[tuple[re.Match[str], str]]:
    matches = list(DECL_RE.finditer(source))
    return [
        (match, source[match.start() : matches[index + 1].start() if index + 1 < len(matches) else len(source)])
        for index, match in enumerate(matches)
    ]


def audit_sources(paths: set[Path]) -> list[TaggedDeclaration]:
    tagged: list[TaggedDeclaration] = []
    failures: list[str] = []
    for path in sorted(paths):
        source = strip_comments_and_strings(path.read_text())
        for forbidden in FORBIDDEN_AXIOM_RE.finditer(source):
            line = source.count("\n", 0, forbidden.start()) + 1
            failures.append(f"{path.relative_to(ROOT)}:{line}: forbidden `{forbidden.group(0).strip()}`")

        covered_sorries: set[int] = set()
        for match, segment in declaration_segments(source):
            attrs = match.group("attrs")
            tags = [
                tag
                for tag in ("proof_obligation", "proof_assembly", "literature_terminal")
                if tag in attrs
            ]
            sorry_matches = list(SORRY_RE.finditer(segment))
            has_sorry = bool(sorry_matches)
            for sorry_match in sorry_matches:
                covered_sorries.add(match.start() + sorry_match.start())
            line = source.count("\n", 0, match.start()) + 1
            if len(tags) > 1:
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: declaration must have exactly one proof-status role"
                )
            if tags:
                tagged.append(
                    TaggedDeclaration(
                        name=match.group("name"),
                        tag=tags[0],
                        path=path,
                        line=line,
                        has_direct_sorry=has_sorry,
                    )
                )
            if "proof_obligation" in tags and AGGREGATED_SOURCE_STEP_RE.search(
                match.group("name")
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: an unfinished source step may not merge "
                    "multiple named results or displayed equations"
                )
            if has_sorry and "proof_obligation" not in tags:
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: `sorry` is allowed only in a `proof_obligation` declaration"
                )

        all_sorries = {match.start() for match in SORRY_RE.finditer(source)}
        for position in sorted(all_sorries - covered_sorries):
            line = source.count("\n", 0, position) + 1
            failures.append(f"{path.relative_to(ROOT)}:{line}: `sorry` appears outside a recognized declaration")

    names = [declaration.full_name for declaration in tagged]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    if duplicates:
        failures.append(f"duplicate tagged declaration names: {duplicates}")
    if failures:
        raise SystemExit("Lean source audit failed:\n" + "\n".join(failures))
    return tagged


def tagged_source_dependencies(
    tagged: list[TaggedDeclaration],
) -> dict[str, tuple[str, ...]]:
    """Recover explicit edges between tagged declarations from their source bodies.

    Lean's axiom audit tells us whether a route reaches ``sorryAx`` but intentionally
    does not expose which project declarations produced that dependency.  The source
    graph complements it: every tagged declaration name referenced in another tagged
    declaration's body becomes a visible edge in ``lean/progress``.
    """

    segments: dict[tuple[Path, str], str] = {}
    for path in {declaration.path for declaration in tagged}:
        source = strip_comments_and_strings(path.read_text())
        for match, segment in declaration_segments(source):
            segments[(path, match.group("name"))] = segment

    dependencies: dict[str, tuple[str, ...]] = {}
    for declaration in tagged:
        segment = segments[(declaration.path, declaration.name)]
        found: list[str] = []
        for candidate in tagged:
            if candidate.full_name == declaration.full_name:
                continue
            reference = re.compile(
                rf"(?<![A-Za-z0-9_']){re.escape(candidate.name)}(?![A-Za-z0-9_'])"
            )
            if reference.search(segment):
                found.append(candidate.full_name)
        dependencies[declaration.full_name] = tuple(sorted(found))
    return dependencies


def claim_declarations() -> list[tuple[str, str]]:
    registry = json.loads(LEAN_CONTRACTS.read_text())
    declarations: list[tuple[str, str]] = []
    for entry in registry["claims"]:
        module = entry["lean_module"]
        declaration = entry["declaration"]
        path = module_path(module)
        if path is None:
            raise SystemExit(f"{entry['id']} names missing Lean module {module}")
        local_name = declaration.rsplit(".", 1)[-1]
        declared_names = {
            match.group("name")
            for match in DECL_RE.finditer(strip_comments_and_strings(path.read_text()))
        }
        if local_name not in declared_names:
            raise SystemExit(
                f"{entry['id']} maps {declaration} to {module}, but that module does not own the declaration"
            )
        declarations.append((module, declaration))
    return declarations


def formal_terminal_declarations() -> set[str]:
    registry = json.loads(FORMALIZATION.read_text())
    terminals: set[str] = set()
    for entry in registry["claims"]:
        if entry["state"] == "catalogued":
            continue
        module = entry.get("terminal_module", entry["lean_module"])
        terminal = entry.get("terminal_declaration")
        if not terminal:
            raise SystemExit(f"{entry['id']} has no literature terminal declaration")
        path = module_path(module)
        if path is None:
            raise SystemExit(f"{entry['id']} names missing Lean module {module}")
        local_name = terminal.rsplit(".", 1)[-1]
        declared_names = {
            match.group("name")
            for match in DECL_RE.finditer(strip_comments_and_strings(path.read_text()))
        }
        if local_name not in declared_names:
            raise SystemExit(
                f"{entry['id']} maps terminal {terminal} to {module}, "
                "but that module does not own the declaration"
            )
        terminals.add(terminal)
    return terminals


def lean_axiom_audit(tagged: list[TaggedDeclaration]) -> dict[str, bool]:
    checks = claim_declarations()
    lines = ["import RiemannianFluids", ""]
    for module, declaration in checks:
        lines.append(f"-- formalization declaration from {module}")
        lines.append(f"#check {declaration}")
    for declaration in tagged:
        lines.extend(
            [
                f'#eval IO.println "PROOF_STATUS_BEGIN {declaration.full_name}"',
                f"#print axioms {declaration.full_name}",
                f'#eval IO.println "PROOF_STATUS_END {declaration.full_name}"',
            ]
        )
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as audit_file:
        audit_file.write("\n".join(lines) + "\n")
        audit_path = Path(audit_file.name)
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
    if result.returncode:
        raise SystemExit(f"Lean declaration audit failed:\n{result.stdout}{result.stderr}")

    output = result.stdout + result.stderr
    status: dict[str, bool] = {}
    for declaration in tagged:
        begin = f"PROOF_STATUS_BEGIN {declaration.full_name}"
        end = f"PROOF_STATUS_END {declaration.full_name}"
        if begin not in output or end not in output:
            raise SystemExit(f"missing axiom-audit sentinel for {declaration.full_name}")
        segment = output.split(begin, 1)[1].split(end, 1)[0]
        status[declaration.full_name] = "sorryAx" in segment
    return status


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("check", "progress"))
    args = parser.parse_args()

    library = import_closure(LIBRARY_ROOT)
    tagged = audit_sources(library)
    source_dependencies = tagged_source_dependencies(tagged)
    axiom_status = lean_axiom_audit(tagged)
    obligations = [declaration for declaration in tagged if declaration.tag == "proof_obligation"]
    assemblies = [declaration for declaration in tagged if declaration.tag == "proof_assembly"]
    terminals = [declaration for declaration in tagged if declaration.tag == "literature_terminal"]
    tagged_terminal_names = {declaration.full_name for declaration in terminals}
    mapped_terminal_names = formal_terminal_declarations()
    missing_terminal_tags = sorted(mapped_terminal_names - tagged_terminal_names)
    if missing_terminal_tags:
        raise SystemExit(
            "formalization terminals missing `literature_terminal` tags: "
            f"{missing_terminal_tags}"
        )

    if args.mode == "check":
        print(
            f"validated Lean closure: {len(library)} files, "
            f"{len(obligations)} open obligations, {len(assemblies)} assembly routes, "
            f"{len(terminals)} terminal routes"
        )
        return

    print("Open proof obligations")
    for declaration in obligations:
        transitive_sorry = axiom_status[declaration.full_name]
        if declaration.has_direct_sorry:
            status = "OPEN_DIRECT"
        elif transitive_sorry:
            status = "BLOCKED_TRANSITIVE"
        else:
            status = "COMPLETE"
        location = f"{declaration.path.relative_to(ROOT)}:{declaration.line}"
        dependencies = source_dependencies[declaration.full_name]
        suffix = f" <- {', '.join(dependencies)}" if dependencies else ""
        print(f"{status:18} {declaration.full_name} ({location}){suffix}")

    print("Assembly routes")
    for declaration in assemblies:
        status = "BLOCKED_TRANSITIVE" if axiom_status[declaration.full_name] else "COMPLETE"
        location = f"{declaration.path.relative_to(ROOT)}:{declaration.line}"
        dependencies = source_dependencies[declaration.full_name]
        suffix = f" <- {', '.join(dependencies)}" if dependencies else ""
        print(f"{status:18} {declaration.full_name} ({location}){suffix}")

    print("Terminal routes")
    for declaration in terminals:
        status = "BLOCKED_TRANSITIVE" if axiom_status[declaration.full_name] else "COMPLETE"
        location = f"{declaration.path.relative_to(ROOT)}:{declaration.line}"
        dependencies = source_dependencies[declaration.full_name]
        suffix = f" <- {', '.join(dependencies)}" if dependencies else ""
        print(f"{status:18} {declaration.full_name} ({location}){suffix}")


if __name__ == "__main__":
    main()
