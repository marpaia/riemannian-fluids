"""Validate the pinned literature archive against its manifests and claim registry."""

from __future__ import annotations

import hashlib
import json
import re
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LITERATURE_ROOT = ROOT / "literature"
MANIFEST = LITERATURE_ROOT / "manifest.json"
CHECKSUMS = LITERATURE_ROOT / "SHA256SUMS"
CLAIM_REGISTRY = ROOT / "claims" / "registry.json"

PAGE_OBJECT_RE = re.compile(rb"/Type\s*/Page\b")
STREAM_RE = re.compile(rb"stream\r?\n")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _pdf_page_count(data: bytes) -> int:
    """Count page objects, including page trees stored in Flate object streams."""

    count = len(PAGE_OBJECT_RE.findall(data))
    for match in STREAM_RE.finditer(data):
        end = data.find(b"endstream", match.end())
        if end < 0:
            continue
        compressed = data[match.end() : end].rstrip(b"\r\n")
        try:
            decoded = zlib.decompress(compressed)
        except zlib.error:
            continue
        count += len(PAGE_OBJECT_RE.findall(decoded))
    return count


def _checksum_entries() -> dict[str, str]:
    entries: dict[str, str] = {}
    for line_number, line in enumerate(CHECKSUMS.read_text().splitlines(), start=1):
        if not line.strip():
            continue
        parts = line.split(maxsplit=1)
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{64}", parts[0]):
            raise ValueError(f"SHA256SUMS:{line_number}: malformed checksum entry")
        path = parts[1].lstrip("*")
        if path in entries:
            raise ValueError(f"SHA256SUMS:{line_number}: duplicate path {path}")
        entries[path] = parts[0]
    return entries


def validate_archive() -> int:
    manifest = json.loads(MANIFEST.read_text())
    registry = json.loads(CLAIM_REGISTRY.read_text())
    papers = manifest.get("papers", [])
    registry_papers = registry.get("papers", [])
    by_id = {paper["id"]: paper for paper in papers}
    registry_by_id = {paper["id"]: paper for paper in registry_papers}
    if len(by_id) != len(papers):
        raise ValueError("literature/manifest.json contains duplicate paper IDs")
    if len(registry_by_id) != len(registry_papers):
        raise ValueError("claims/registry.json contains duplicate paper IDs")
    if set(by_id) != set(registry_by_id):
        raise ValueError(
            "literature and claim paper IDs differ: "
            f"manifest_only={sorted(set(by_id) - set(registry_by_id))}, "
            f"registry_only={sorted(set(registry_by_id) - set(by_id))}"
        )

    checksums = _checksum_entries()
    manifest_checksums: dict[str, str] = {}
    archived_paths: set[Path] = set()
    for paper_id, paper in by_id.items():
        registered = registry_by_id[paper_id]
        for manifest_key, registry_key in (
            ("title", "title"),
            ("version", "version"),
            ("canonical_url", "url"),
        ):
            if paper[manifest_key] != registered[registry_key]:
                raise ValueError(
                    f"{paper_id}: manifest {manifest_key} disagrees with claim registry"
                )

        relative = Path(paper["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"{paper_id}: unsafe archive path {relative}")
        path = LITERATURE_ROOT / relative
        if path in archived_paths:
            raise ValueError(f"{paper_id}: duplicate archive path {relative}")
        archived_paths.add(path)
        if not path.is_file():
            raise ValueError(f"{paper_id}: missing archived PDF {relative}")
        data = path.read_bytes()
        if not data.startswith(b"%PDF-"):
            raise ValueError(f"{paper_id}: archive is not a PDF: {relative}")
        if len(data) != paper["bytes"]:
            raise ValueError(
                f"{paper_id}: byte count {len(data)} != manifest {paper['bytes']}"
            )
        digest = _sha256(path)
        if digest != paper["sha256"]:
            raise ValueError(f"{paper_id}: SHA-256 does not match manifest")
        pages = _pdf_page_count(data)
        if pages != paper["pages"]:
            raise ValueError(
                f"{paper_id}: page count {pages} != manifest {paper['pages']}"
            )
        manifest_checksums[relative.as_posix()] = digest

    if checksums != manifest_checksums:
        raise ValueError("literature/SHA256SUMS disagrees with manifest paths or digests")
    actual_pdfs = set((LITERATURE_ROOT / "pdfs").glob("*.pdf"))
    if actual_pdfs != archived_paths:
        raise ValueError(
            "unmanifested or missing PDFs: "
            f"extra={sorted(str(path.relative_to(LITERATURE_ROOT)) for path in actual_pdfs - archived_paths)}, "
            f"missing={sorted(str(path.relative_to(LITERATURE_ROOT)) for path in archived_paths - actual_pdfs)}"
        )
    return len(papers)


def main() -> None:
    count = validate_archive()
    print(f"validated {count} pinned literature PDFs against manifest, checksums, and claims")


if __name__ == "__main__":
    main()
