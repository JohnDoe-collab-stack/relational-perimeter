#!/usr/bin/env python3
"""Compute and verify the complete repository-local material used by v13."""

from __future__ import annotations

import hashlib
import ast
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from typing import Callable, Iterable

from lean_imports import imports as parse_lean_imports


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = Path("experiments/constitutive-neural-alignment/v13")
LEAN_ROOTS = (
    "Tests/Executables/CompiledIndependentCompleteNeuralComparison.lean",
    "Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean",
)
PYTHON_ROOTS = (
    "scripts/check-independent-comparison-codegen.py",
    "scripts/check-unified-codegen.py",
    "scripts/independent_capability_snapshot_v13.py",
    "scripts/run-independent-capability-ablations-v13.py",
    "scripts/check-independent-capability-comparison-v13.py",
    "scripts/freeze-independent-capability-comparison-v13.py",
    "scripts/run-independent-capability-comparison-v13.py",
)
FIXED_MATERIAL = (
    "RelationalPerimeter.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "scripts/expected-failures.tsv",
    "scripts/stratification.tsv",
    f"{EXPERIMENT.as_posix()}/README.md",
    f"{EXPERIMENT.as_posix()}/authorized-ablations.json",
    f"{EXPERIMENT.as_posix()}/capability-matrix.json",
    f"{EXPERIMENT.as_posix()}/evidence-ledger.json",
    f"{EXPERIMENT.as_posix()}/probe-specification.json",
    f"{EXPERIMENT.as_posix()}/result-schema.json",
    f"{EXPERIMENT.as_posix()}/success-criteria.json",
    "experiments/constitutive-neural-alignment/v12/scaling-protocol.json",
)
SHA256 = re.compile(r"[0-9a-f]{64}")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def git(*arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments], cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", check=False)
    if result.returncode != 0:
        raise ValueError(result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def working_reader(relative: str) -> bytes:
    path = ROOT / relative
    require(path.is_file(), f"material is missing: {relative}")
    return path.read_bytes()


def commit_reader(commit: str) -> Callable[[str], bytes]:
    def read(relative: str) -> bytes:
        result = subprocess.run(
            ["git", "show", f"{commit}:{relative}"], cwd=ROOT,
            capture_output=True, check=False)
        require(result.returncode == 0,
                f"material is absent from {commit}: {relative}")
        return result.stdout
    return read


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def lean_import_closure(
    roots: Iterable[str], read: Callable[[str], bytes]
) -> list[str]:
    pending = list(roots)
    closure: set[str] = set()
    while pending:
        relative = pending.pop()
        if relative in closure:
            continue
        source = read(relative).decode("utf-8")
        closure.add(relative)
        for module in parse_lean_imports(source):
            candidate = module_path(module)
            try:
                read(candidate)
            except ValueError:
                continue
            pending.append(candidate)
    return sorted(closure)


def python_import_closure(
    roots: Iterable[str], read: Callable[[str], bytes]
) -> list[str]:
    """Resolve repository-local imports of every executable Python root."""
    pending = list(roots)
    closure: set[str] = set()
    while pending:
        relative = pending.pop()
        if relative in closure:
            continue
        source = read(relative).decode("utf-8")
        closure.add(relative)
        tree = ast.parse(source, filename=relative)
        modules: list[str] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                modules.extend(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module is not None:
                modules.append(node.module)
        parent = PurePosixPath(relative).parent
        for module in modules:
            module_file = module.replace(".", "/") + ".py"
            candidates = (
                (parent / module_file).as_posix(),
                PurePosixPath(module_file).as_posix(),
            )
            for candidate in candidates:
                try:
                    read(candidate)
                except ValueError:
                    continue
                pending.append(candidate)
                break
    return sorted(closure)


def authorized_fixtures(read: Callable[[str], bytes]) -> list[str]:
    relative = f"{EXPERIMENT.as_posix()}/authorized-ablations.json"
    value = json.loads(read(relative).decode("utf-8"))
    rows = value.get("ablations")
    require(isinstance(rows, list) and rows, "authorized ablations are absent")
    fixtures: list[str] = []
    for row in rows:
        fixture = row.get("fixture")
        if fixture is not None:
            require(isinstance(fixture, str) and fixture.endswith(".lean.fail"),
                    "invalid authorized fixture")
            fixtures.append(fixture)
    return sorted(set(fixtures))


def material_paths(read: Callable[[str], bytes]) -> list[str]:
    fixtures = authorized_fixtures(read)
    lean = lean_import_closure((*LEAN_ROOTS, *fixtures), read)
    python = python_import_closure(PYTHON_ROOTS, read)
    paths = set(lean) | set(python) | set(FIXED_MATERIAL)
    for relative in paths:
        read(relative)
    required = {
        "RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean",
        "RelationalPerimeter/Agents/Neural/IndependentLearnedArtifact.lean",
    }
    require(required <= set(lean),
            "required transitive learned dependencies are outside the closure")
    return sorted(paths)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def material_digest(data: bytes) -> str:
    """Hash text material independently of Git's platform line endings."""
    return digest(data.replace(b"\r\n", b"\n"))


def canonical_digest(value: dict, omitted: str) -> str:
    copied = dict(value)
    copied.pop(omitted, None)
    encoded = json.dumps(
        copied, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return digest(encoded)


def build_snapshot(commit: str, remote: str, remote_ref: str) -> dict:
    read = commit_reader(commit)
    paths = material_paths(read)
    fixtures = authorized_fixtures(read)
    snapshot = {
        "snapshot_id": "constitutive-neural-independent-capability-v13",
        "source_commit": commit,
        "source_tree": git("rev-parse", f"{commit}^{{tree}}"),
        "remote_url": remote,
        "remote_ref": remote_ref,
        "material_normalization": "crlf-to-lf",
        "lean_roots": list(LEAN_ROOTS),
        "python_roots": list(PYTHON_ROOTS),
        "ablation_roots": fixtures,
        "lean_import_closure":
            lean_import_closure((*LEAN_ROOTS, *fixtures), read),
        "python_import_closure": python_import_closure(PYTHON_ROOTS, read),
        "material_sha256": {
            relative: material_digest(read(relative)) for relative in paths
        },
    }
    snapshot["snapshot_sha256"] = canonical_digest(snapshot, "snapshot_sha256")
    return snapshot


def validate_snapshot(snapshot: dict, check_worktree: bool) -> None:
    require(snapshot.get("snapshot_id") ==
            "constitutive-neural-independent-capability-v13",
            "wrong snapshot id")
    commit = snapshot.get("source_commit")
    require(isinstance(commit, str) and len(commit) == 40,
            "snapshot source commit is absent")
    require(git("cat-file", "-t", commit) == "commit",
            "snapshot source commit is not available")
    require(snapshot.get("source_tree") == git("rev-parse", f"{commit}^{{tree}}"),
            "snapshot source tree differs")
    require(snapshot.get("snapshot_sha256") ==
            canonical_digest(snapshot, "snapshot_sha256"),
            "snapshot seal differs")
    require(snapshot.get("material_normalization") == "crlf-to-lf",
            "snapshot material normalization differs")
    remote_ref = snapshot.get("remote_ref")
    require(isinstance(remote_ref, str) and "/" in remote_ref,
            "snapshot remote ref is absent")
    remote_name = remote_ref.split("/", 1)[0]
    require(snapshot.get("remote_url") == git("remote", "get-url", remote_name),
            "snapshot remote URL differs from the configured remote")
    remote_tip = git("rev-parse", remote_ref)
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, remote_tip], cwd=ROOT,
        capture_output=True, check=False)
    require(ancestry.returncode == 0,
            "snapshot source commit is not recoverable from its remote ref")
    read = commit_reader(commit)
    expected_paths = material_paths(read)
    fixtures = authorized_fixtures(read)
    require(snapshot.get("ablation_roots") == fixtures,
            "snapshot ablation roots differ")
    hashes = snapshot.get("material_sha256")
    require(isinstance(hashes, dict) and sorted(hashes) == expected_paths,
            "snapshot is not the exact scientific dependency closure")
    require(snapshot.get("lean_import_closure") ==
            lean_import_closure((*LEAN_ROOTS, *fixtures), read),
            "snapshot Lean import closure differs")
    require(snapshot.get("python_roots") == list(PYTHON_ROOTS),
            "snapshot Python roots differ")
    require(snapshot.get("python_import_closure") ==
            python_import_closure(PYTHON_ROOTS, read),
            "snapshot Python import closure differs")
    for relative, expected in hashes.items():
        require(isinstance(expected, str) and SHA256.fullmatch(expected) is not None,
                f"invalid snapshot digest: {relative}")
        require(material_digest(read(relative)) == expected,
                f"snapshot commit material differs: {relative}")
        if check_worktree:
            require(material_digest(working_reader(relative)) == expected,
                    f"executed material differs from snapshot: {relative}")
