#!/usr/bin/env python3
"""Require one locally enforced negative fixture for every neural block."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
COVERAGE = ROOT / "scripts/neural-block-negative-fixtures.tsv"
REGISTRY = ROOT / "scripts/expected-failures.tsv"
SH_PORTAL = ROOT / "scripts/verify.sh"
PS_PORTAL = ROOT / "scripts/verify.ps1"

EXPECTED_BLOCKS = tuple(f"B{index:02d}_" for index in range(1, 15))


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_BLOCK_NEGATIVE_FIXTURES_ERROR: {message}")


def rows(path: Path, field_count: int) -> list[list[str]]:
    parsed: list[list[str]] = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != field_count or any(not field for field in fields):
            fail(f"{path.name}:{line_number}: expected {field_count} nonempty fields")
        parsed.append(fields)
    return parsed


def main() -> None:
    coverage = rows(COVERAGE, 2)
    blocks = [row[0] for row in coverage]
    if len(coverage) != len(EXPECTED_BLOCKS):
        fail(f"expected {len(EXPECTED_BLOCKS)} blocks, found {len(coverage)}")
    for prefix in EXPECTED_BLOCKS:
        matching = [block for block in blocks if block.startswith(prefix)]
        if len(matching) != 1:
            fail(f"{prefix} must occur exactly once, found {len(matching)}")
    if len(set(blocks)) != len(blocks):
        fail("duplicate block identifiers")

    registry = {row[0]: row for row in rows(REGISTRY, 6)}
    fixtures = [row[1] for row in coverage]
    if len(set(fixtures)) != len(fixtures):
        fail("one fixture cannot stand in for two implementation blocks")
    for fixture in fixtures:
        if fixture not in registry:
            fail(f"fixture is not enforced by the exact diagnostic gate: {fixture}")
        if not (ROOT / fixture).is_file():
            fail(f"fixture is missing: {fixture}")
        if not registry[fixture][5].strip():
            fail(f"fixture has no semantic obligation: {fixture}")

    gate = Path(__file__).name
    for portal in (SH_PORTAL, PS_PORTAL):
        if gate not in portal.read_text(encoding="utf-8"):
            fail(f"{portal.name} does not execute {gate}")

    print(
        "NEURAL_BLOCK_NEGATIVE_FIXTURES_OK "
        f"blocks={len(blocks)} fixtures={len(fixtures)} portals=2"
    )


if __name__ == "__main__":
    main()
