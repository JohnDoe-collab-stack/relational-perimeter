#!/usr/bin/env python3
"""Validate the immutable v9 and v10 material at its recoverable source commit."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent.parent
FROZEN_SOURCE_COMMIT = "cb8d9e17b7b9db60c057d1617f1d56321e03ee3c"
V9 = ROOT / "experiments/constitutive-neural-alignment/v9"
V10 = ROOT / "experiments/constitutive-neural-alignment/v10"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def frozen_bytes(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{FROZEN_SOURCE_COMMIT}:{relative}"], cwd=ROOT,
        capture_output=True, check=False)
    require(result.returncode == 0, f"frozen source is unavailable: {relative}")
    return result.stdout


def load_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"JSON root is not an object: {path}")
    return value


def load_module(name: str, relative: str):
    path = ROOT / relative
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None,
            f"cannot load validator: {relative}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_recoverability() -> None:
    commit = subprocess.run(
        ["git", "cat-file", "-t", FROZEN_SOURCE_COMMIT], cwd=ROOT,
        capture_output=True, text=True, check=False)
    require(commit.returncode == 0 and commit.stdout.strip() == "commit",
            "frozen source commit is unavailable")
    remote = subprocess.run(
        ["git", "branch", "-r", "--contains", FROZEN_SOURCE_COMMIT], cwd=ROOT,
        capture_output=True, text=True, check=False)
    require(remote.returncode == 0 and "origin/" in remote.stdout,
            "frozen source commit is not recoverable from an origin ref")


def validate_manifest(manifest: dict, expected_id: str) -> None:
    require(manifest.get("manifest_id") == expected_id, "wrong archive manifest id")
    files = manifest.get("files")
    require(isinstance(files, dict) and files, "archive manifest file map is empty")
    for relative, expected in files.items():
        require(digest(frozen_bytes(relative)) == expected,
                f"archive hash mismatch: {relative}")


def validate_archive_files(relative_paths: list[str]) -> None:
    for relative in relative_paths:
        require((ROOT / relative).read_bytes() == frozen_bytes(relative),
                f"historical protocol material was rewritten: {relative}")


def validate_markers(markers: dict[str, list[str]]) -> None:
    for relative, required in markers.items():
        source = frozen_bytes(relative).decode("utf-8")
        for marker in required:
            require(marker in source,
                    f"missing frozen source marker: {relative}: {marker}")


def validate_v9(v9) -> None:
    learning = load_json(V9 / "learning-transformation-protocol.json")
    comparison = load_json(V9 / "comparison-protocol.json")
    schema = load_json(V9 / "result-schema.json")
    manifest = load_json(V9 / "manifest.json")
    v9.validate_learning(learning)
    v9.validate_comparison(comparison)
    v9.validate_schema(schema)
    validate_manifest(
        manifest, "constitutive-neural-joint-capability-manifest-v9")
    validate_markers(v9.REQUIRED_SOURCE_MARKERS)
    validate_archive_files([
        "experiments/constitutive-neural-alignment/v9/learning-transformation-protocol.json",
        "experiments/constitutive-neural-alignment/v9/comparison-protocol.json",
        "experiments/constitutive-neural-alignment/v9/result-schema.json",
        "experiments/constitutive-neural-alignment/v9/manifest.json",
        "experiments/constitutive-neural-alignment/v9/README.md",
    ])
    require(not (V9 / "comparison-results.ndjson").exists() and
            not (V9 / "result-record.json").exists(),
            "v9 was frozen as not-run but now contains results")


def validate_v10(v10) -> None:
    v10.validate_protocol(load_json(V10 / "comparison-protocol.json"))
    v10.validate_translations(load_json(V10 / "translation-ledger.json"))
    v10.validate_correspondence(load_json(V10 / "method-correspondence.json"))
    v10.validate_matrix(load_json(V10 / "capability-matrix.json"))
    v10.validate_ablations(load_json(V10 / "authorized-ablations.json"))
    v10.validate_criteria(load_json(V10 / "success-criteria.json"))
    v10.validate_schema(load_json(V10 / "result-schema.json"))
    validate_manifest(
        load_json(V10 / "manifest.json"),
        "constitutive-neural-complete-capability-manifest-v10")
    validate_markers(v10.SOURCE_MARKERS)
    validate_archive_files([
        "experiments/constitutive-neural-alignment/v10/README.md",
        "experiments/constitutive-neural-alignment/v10/comparison-protocol.json",
        "experiments/constitutive-neural-alignment/v10/translation-ledger.json",
        "experiments/constitutive-neural-alignment/v10/method-correspondence.json",
        "experiments/constitutive-neural-alignment/v10/authorized-ablations.json",
        "experiments/constitutive-neural-alignment/v10/capability-matrix.json",
        "experiments/constitutive-neural-alignment/v10/success-criteria.json",
        "experiments/constitutive-neural-alignment/v10/COMPARATIVE_SCOPE.md",
        "experiments/constitutive-neural-alignment/v10/result-schema.json",
        "experiments/constitutive-neural-alignment/v10/manifest.json",
    ])
    v10.validate_record_if_present(True)
    validate_v10_record(load_json(V10 / "result-record.json"))


def validate_v10_record(record: dict) -> None:
    require(record.get("repository_commit") == FROZEN_SOURCE_COMMIT,
            "v10 result is not bound to the frozen source commit")


def validate() -> None:
    validate_recoverability()
    v9 = load_module("neural_joint_v9", "scripts/check-neural-joint-protocol-v9.py")
    v10 = load_module(
        "neural_complete_v10", "scripts/check-neural-complete-comparison-v10.py")
    validate_v9(v9)
    validate_v10(v10)


def self_test() -> None:
    validate()
    v9_manifest = load_json(V9 / "manifest.json")
    changed = copy.deepcopy(v9_manifest)
    first = next(iter(changed["files"]))
    changed["files"][first] = "0" * 64
    try:
        validate_manifest(
            changed, "constitutive-neural-joint-capability-manifest-v9")
    except ValueError:
        pass
    else:
        raise ValueError("v9 archive hash mutation survived")
    v10_record = load_json(V10 / "result-record.json")
    changed_record = copy.deepcopy(v10_record)
    changed_record["repository_commit"] = "0" * 40
    try:
        validate_v10_record(changed_record)
    except ValueError:
        pass
    else:
        raise ValueError("v10 result-commit mutation survived")
    print("NEURAL_V9_V10_ARCHIVE_SELFTEST_OK mutations=2")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    if arguments.self_test:
        self_test()
    else:
        validate()
        print("NEURAL_V9_V10_ARCHIVE_OK "
              f"commit={FROZEN_SOURCE_COMMIT[:8]} v9_results=false v10_results=true")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"NEURAL_V9_V10_ARCHIVE_ERROR: {error}")
