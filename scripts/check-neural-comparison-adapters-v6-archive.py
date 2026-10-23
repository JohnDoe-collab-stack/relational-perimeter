#!/usr/bin/env python3
"""Validate the immutable v6 adapter freeze at its recoverable source commit."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v6"
MANIFEST = EXPERIMENT / "manifest.json"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
FROZEN_SOURCE_COMMIT = "6cd785a8bc1b9c1bc0678af651b0a8343787acfb"
CURRENT_PATHS = {
    "experiments/constitutive-neural-alignment/v6/comparison-protocol.json",
    "experiments/constitutive-neural-alignment/v6/adapter-manifest.json",
    "experiments/constitutive-neural-alignment/v6/comparison-result-schema.json",
    "experiments/constitutive-neural-alignment/v6/README.md",
    "experiments/constitutive-neural-alignment/v1/learned-artifact.json",
    "experiments/constitutive-neural-alignment/v1/training-data.json",
}


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def frozen_bytes(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{FROZEN_SOURCE_COMMIT}:{relative}"], cwd=ROOT,
        capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(f"frozen source is unavailable: {relative}")
    return result.stdout


def load_v6_module():
    path = ROOT / "scripts/check-neural-comparison-adapters-v6.py"
    spec = importlib.util.spec_from_file_location("comparison_v6", path)
    if spec is None or spec.loader is None:
        raise ValueError("cannot load the original v6 validator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_manifest(manifest: dict) -> None:
    if manifest.get("status") != "adapters-content-frozen-not-run":
        raise ValueError("wrong archive status")
    for relative, expected in manifest.get("files", {}).items():
        payload = ((ROOT / relative).read_bytes() if relative in CURRENT_PATHS
                   else frozen_bytes(relative))
        if digest(payload) != expected:
            raise ValueError(f"archive hash mismatch: {relative}")


def validate() -> None:
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    load_v6_module().validate_protocol(protocol)
    if (EXPERIMENT / "comparison-results.json").exists():
        raise ValueError("v6 was frozen as not-run but now contains results")
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    validate_manifest(manifest)

    adapter_source = frozen_bytes(
        "RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean"
    ).decode("utf-8")
    runner = frozen_bytes(
        "Tests/Executables/CompiledNeuralComparisonAdapters.lean"
    ).decode("utf-8")
    for baseline, declaration in load_v6_module().BASELINES.items():
        if f"def {declaration}" not in adapter_source:
            raise ValueError(f"missing frozen adapter: {declaration}")
        if f'\\"adapter_id\\":\\"{baseline}\\"' not in runner:
            raise ValueError(f"missing frozen output row: {baseline}")


def self_test() -> None:
    validate()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    changed = copy.deepcopy(manifest)
    changed["status"] = "confirmatory-run-complete"
    try:
        validate_manifest(changed)
    except ValueError:
        pass
    else:
        raise ValueError("archive status mutation survived")
    print("NEURAL_COMPARISON_ADAPTERS_V6_ARCHIVE_SELFTEST_OK mutations=1")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    if arguments.self_test:
        self_test()
    else:
        validate()
        print("NEURAL_COMPARISON_ADAPTERS_V6_ARCHIVE_OK "
              f"commit={FROZEN_SOURCE_COMMIT[:8]} results=false")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"NEURAL_COMPARISON_ADAPTERS_V6_ARCHIVE_ERROR: {error}")
