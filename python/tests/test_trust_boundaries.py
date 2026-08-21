from __future__ import annotations

import sys
from pathlib import Path

import pytest

TOOLS = Path(__file__).resolve().parents[2] / "tools"
sys.path.insert(0, str(TOOLS))

from validate_lean import ALLOWED_AXIOMS, parse_print_axioms  # noqa: E402
from validate_literature import validate_archive  # noqa: E402


def test_pinned_literature_archive_matches_all_manifests() -> None:
    assert validate_archive() == 11


def test_lean_axiom_parser_accepts_only_the_documented_dependencies() -> None:
    segment = "'example' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert parse_print_axioms(segment) == ALLOWED_AXIOMS


def test_lean_axiom_parser_exposes_an_unexpected_axiom() -> None:
    segment = "'example' depends on axioms: [propext, Project.unsound]"
    assert parse_print_axioms(segment) - ALLOWED_AXIOMS == {"Project.unsound"}


@pytest.mark.parametrize("segment", ["", "depends on axioms: []", "unrecognized output"])
def test_lean_axiom_parser_fails_closed(segment: str) -> None:
    with pytest.raises(ValueError):
        parse_print_axioms(segment)
