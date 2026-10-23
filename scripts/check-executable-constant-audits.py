#!/usr/bin/env python3
"""Audit each executable root in a separate Lean environment and verify their union."""

from __future__ import annotations

import argparse
import re
import subprocess
import tempfile
from pathlib import Path


ROOTS = (
    "Tests.Executables.CompiledNeuralCheckerMeasure",
    "Tests.Executables.CompiledNeuralComparisonAdapters",
    "Tests.Executables.CompiledCompleteNeuralComparison",
    "Tests.Executables.CompiledIndependentCompleteNeuralComparison",
    "Tests.Executables.CompiledParameterizedNeuralCheckerFamily",
    "Tests.Executables.CompiledCompletePropertyNeuralScaling",
    "Tests.Executables.CompiledCausalCompletePropertyNeuralScaling",
)
BLOCK_RE = re.compile(
    r"/- REPOSITORY_CONSTANT_AUDIT_BEGIN -/\s*(.*?)\s*"
    r"/- REPOSITORY_CONSTANT_AUDIT_END -/",
    re.DOTALL,
)
SUMMARY_RE = re.compile(
    r"ALL_CONSTANTS_OK constants=([0-9]+) modules=([0-9]+) "
    r"generatedExceptions=([0-9]+) writtenExceptions=([0-9]+)"
)
MODULE_RE = re.compile(r"ALL_CONSTANTS_MODULE\t([^\r\n]+)")


def fail(message: str) -> "NoReturn":
    raise RuntimeError(message)


def validate_output(output: str, root: str) -> set[str]:
    summaries = SUMMARY_RE.findall(output)
    if len(summaries) != 1:
        fail(f"{root}: expected exactly one exhaustive-audit summary, found {len(summaries)}")
    _constants, module_count, _generated, written = summaries[0]
    if written != "0":
        fail(f"{root}: handwritten constant depends on an axiom")
    modules = set(MODULE_RE.findall(output))
    if len(modules) != int(module_count):
        fail(
            f"{root}: summary reports {module_count} modules but emitted "
            f"{len(modules)} module identities"
        )
    if root not in modules:
        fail(f"{root}: executable root is absent from its own audit environment")
    return modules


def repository_modules(repo: Path) -> set[str]:
    completed = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    modules: set[str] = set()
    for raw in completed.stdout.splitlines():
        relative = raw.strip().replace("\\", "/")
        if not relative or not (repo / relative).is_file():
            continue
        modules.add(relative.removesuffix(".lean").replace("/", "."))
    return modules


def audit_block(repo: Path) -> str:
    source = (repo / "Tests" / "AllConstantsAudit.lean").read_text(encoding="utf-8")
    matches = BLOCK_RE.findall(source)
    if len(matches) != 1:
        fail(f"expected exactly one reusable exhaustive-audit block, found {len(matches)}")
    return matches[0]


def audit_root(repo: Path, temporary: Path, block: str, root: str) -> set[str]:
    client = temporary / f"{root.rsplit('.', 1)[-1]}Audit.lean"
    client.write_text(
        f"import Tests.AllConstantsAudit\nimport {root}\n\n"
        f"set_option maxHeartbeats 0\nopen Lean\n\n{block}\n",
        encoding="utf-8",
    )
    completed = subprocess.run(
        ["lake", "env", "lean", str(client)],
        cwd=repo,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    output = completed.stdout + completed.stderr
    if completed.returncode != 0:
        fail(f"{root}: Lean audit client failed\n{output[-4000:]}")
    return validate_output(output, root)


def self_test() -> None:
    good = (
        "info: ALL_CONSTANTS_MODULE\tTests.AllConstantsAudit\n"
        "info: ALL_CONSTANTS_MODULE\tTests.Executables.Example\n"
        "info: ALL_CONSTANTS_OK constants=12 modules=2 generatedExceptions=1 writtenExceptions=0\n"
    )
    modules = validate_output(good, "Tests.Executables.Example")
    if modules != {"Tests.AllConstantsAudit", "Tests.Executables.Example"}:
        fail("self-test: valid module inventory was parsed incorrectly")
    mutations = (
        good.replace("writtenExceptions=0", "writtenExceptions=1"),
        good.replace("modules=2", "modules=3"),
        good.replace("Tests.Executables.Example", "Tests.Executables.Foreign"),
        good + "info: ALL_CONSTANTS_OK constants=12 modules=2 generatedExceptions=1 writtenExceptions=0\n",
    )
    for mutation in mutations:
        try:
            validate_output(mutation, "Tests.Executables.Example")
        except RuntimeError:
            continue
        fail("self-test: malformed executable audit was accepted")
    print("EXECUTABLE_CONSTANT_AUDITS_SELFTEST_OK mutations=4")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return

    repo = Path(__file__).resolve().parent.parent
    expected = repository_modules(repo)
    block = audit_block(repo)
    union: set[str] = set()
    per_root: list[tuple[str, int]] = []
    with tempfile.TemporaryDirectory(prefix="relational-perimeter-executable-audit-") as raw:
        temporary = Path(raw)
        for root in ROOTS:
            modules = audit_root(repo, temporary, block, root)
            union.update(modules)
            per_root.append((root, len(modules)))

    missing = sorted(expected - union)
    extra = sorted(union - expected)
    if missing or extra:
        fail(f"exhaustive module union mismatch; missing={missing}; extra={extra}")
    details = " ".join(f"{root}={count}" for root, count in per_root)
    print(f"EXECUTABLE_CONSTANT_AUDITS_OK modules={len(union)} roots={len(ROOTS)} {details}")


if __name__ == "__main__":
    main()
