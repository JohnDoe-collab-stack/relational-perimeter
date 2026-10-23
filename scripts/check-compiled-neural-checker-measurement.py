#!/usr/bin/env python3
"""Validate the frozen measurement produced by the compiled Lean checkers."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v5"
PROTOCOL = EXPERIMENT / "measurement-protocol.json"
RESULT = EXPERIMENT / "measurement-results.json"
README = EXPERIMENT / "README.md"
MANIFEST = EXPERIMENT / "manifest.json"
LEAN_SOURCE = ROOT / "Tests/Executables/CompiledNeuralCheckerMeasure.lean"
RUNNER = ROOT / "scripts/run-compiled-neural-checker-measurement.py"
LAKEFILE = ROOT / "lakefile.toml"
PORTALS = (ROOT / "scripts/verify.sh", ROOT / "scripts/verify.ps1")
FROZEN_SOURCE_COMMIT = "fafd739b7f4718ab9939ccd870eb4983a4655d2e"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frozen_bytes(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{FROZEN_SOURCE_COMMIT}:{relative}"],
        cwd=ROOT, capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(f"frozen source is unavailable: {relative}")
    return result.stdout


def frozen_matches(relative: str, expected: str) -> bool:
    payload = frozen_bytes(relative)
    candidates = (payload, payload.replace(b"\n", b"\r\n"))
    return any(hashlib.sha256(candidate).hexdigest() == expected
               for candidate in candidates)


def fail(message: str) -> None:
    raise SystemExit(f"COMPILED_NEURAL_CHECKER_MEASUREMENT_CHECK_ERROR: {message}")


def at(value: dict, *path: str):
    current = value
    for key in path:
        current = current[key]
    return current


def validate(protocol: dict, result: dict) -> None:
    if protocol.get("protocol_id") != "compiled-neural-checker-measurement-v5":
        raise ValueError("wrong protocol id")
    if protocol.get("status") != "frozen-before-confirmatory-run":
        raise ValueError("protocol was not frozen before the run")
    if result.get("protocol_id") != protocol["protocol_id"]:
        raise ValueError("result names another protocol")
    if result.get("protocol_sha256") != digest(PROTOCOL):
        raise ValueError("result does not name the frozen protocol bytes")
    if result.get("runner_sha256") != protocol.get("runner_sha256"):
        raise ValueError("result and protocol name different runners")
    if result.get("lean_source_sha256") != protocol.get("source_sha256"):
        raise ValueError("result and protocol name different Lean sources")
    if result.get("negative_control", {}).get("rejected") is not True:
        raise ValueError("invalid-selector control was not rejected")
    if result["negative_control"].get("exit_code") == 0:
        raise ValueError("invalid-selector control returned success")

    observation = result["observation"]
    expected = protocol["expected_deterministic_observation"]
    required = (
        (("measurement_id",), "compiled-neural-checker-v5"),
        (("scope",), "fixed-public-update"),
        (("warmup_count",), protocol["warmup_count"]),
        (("measured_count",), protocol["measured_count"]),
        (("incremental", "accepted"), True),
        (("incremental", "checksum"), expected["incremental_checksum"]),
        (("incremental", "affected_cone_size"), expected["affected_cone_size"]),
        (("incremental", "transported_fragments"), expected["transported_fragments"]),
        (("incremental", "recomputed_fragments"), expected["recomputed_fragments"]),
        (("incremental", "assembled_fragments"), expected["assembled_fragments"]),
        (("reference", "accepted"), True),
        (("reference", "checksum"), expected["reference_checksum"]),
        (("exact_result_theorem",), True),
        (("timing_status",), "observational-not-a-theorem"),
    )
    for path, value in required:
        if at(observation, *path) != value:
            raise ValueError(f"unexpected deterministic result at {'.'.join(path)}")
    for checker in ("incremental", "reference"):
        elapsed = observation[checker].get("elapsed_nanoseconds")
        if not isinstance(elapsed, int) or elapsed <= 0:
            raise ValueError(f"{checker} elapsed time is not a positive observation")


def self_test(protocol: dict, result: dict) -> None:
    validate(protocol, result)
    mutations = []
    for name, mutate in (
        ("accepted", lambda item: item["observation"]["incremental"].__setitem__(
            "accepted", False)),
        ("cone", lambda item: item["observation"]["incremental"].__setitem__(
            "affected_cone_size", 0)),
        ("reference", lambda item: item["observation"]["reference"].__setitem__(
            "checksum", 0)),
        ("exactness", lambda item: item["observation"].__setitem__(
            "exact_result_theorem", False)),
        ("negative-control", lambda item: item["negative_control"].__setitem__(
            "rejected", False)),
    ):
        changed = copy.deepcopy(result)
        mutate(changed)
        mutations.append((name, changed))
    for name, changed in mutations:
        try:
            validate(protocol, changed)
        except ValueError:
            continue
        raise ValueError(f"negative self-test survived: {name}")
    print(f"COMPILED_NEURAL_CHECKER_MEASUREMENT_SELFTEST_OK mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    result = json.loads(RESULT.read_text(encoding="utf-8"))
    if arguments.self_test:
        self_test(protocol, result)
        return
    validate(protocol, result)

    if digest(RUNNER) != protocol["runner_sha256"]:
        fail("runner hash differs from the frozen protocol")
    for relative, expected in protocol["source_sha256"].items():
        if not frozen_matches(relative, expected):
            fail(f"frozen source hash is not recoverable: {relative}")

    lean_text = frozen_bytes(
        "Tests/Executables/CompiledNeuralCheckerMeasure.lean").decode("utf-8")
    for required in (
        "checkIncrementalUpdate update",
        "checkReferenceUpdate update",
        "publicIncrementalAndReferenceChecks_exact",
        "selectedIncrementalUpdate selector",
        "IO.monoNanosNow",
    ):
        if required not in lean_text:
            fail(f"compiled measurement source lost direct dependency: {required}")
    runner_text = RUNNER.read_text(encoding="utf-8")
    if "compiled_neural_checker_measure" not in runner_text:
        fail("runner no longer launches the compiled executable")
    for forbidden in ("def check_incremental", "def check_reference"):
        if forbidden in runner_text:
            fail("runner contains a parallel checker implementation")
    lake_text = frozen_bytes("lakefile.toml").decode("utf-8")
    if 'name = "compiled_neural_checker_measure"' not in lake_text or \
            'root = "Tests.Executables.CompiledNeuralCheckerMeasure"' not in lake_text:
        fail("Lake executable target is missing or redirected")

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("manifest_id") != "compiled-neural-checker-measurement-manifest-v5":
        fail("wrong manifest id")
    expected_paths = set(protocol["source_sha256"])
    expected_paths.update({
        "scripts/run-compiled-neural-checker-measurement.py",
        "scripts/check-compiled-neural-checker-measurement.py",
        "experiments/constitutive-neural-alignment/v5/measurement-protocol.json",
        "experiments/constitutive-neural-alignment/v5/measurement-results.json",
        "experiments/constitutive-neural-alignment/v5/README.md",
    })
    if set(manifest.get("files", {})) != expected_paths:
        fail("manifest file set differs from the frozen campaign")
    frozen_paths = set(protocol["source_sha256"]) | {
        "scripts/check-compiled-neural-checker-measurement.py",
    }
    for relative, expected in manifest["files"].items():
        valid = (frozen_matches(relative, expected) if relative in frozen_paths
                 else digest(ROOT / relative) == expected)
        if not valid:
            fail(f"manifest hash changed: {relative}")

    gate = Path(__file__).name
    for portal in PORTALS:
        if gate not in portal.read_text(encoding="utf-8"):
            fail(f"{portal.name} does not execute the v5 measurement gate")

    observation = result["observation"]
    print(
        "COMPILED_NEURAL_CHECKER_MEASUREMENT_OK "
        f"archive_commit={FROZEN_SOURCE_COMMIT[:8]} "
        f"runs={observation['measured_count']} "
        f"affected={observation['incremental']['affected_cone_size']} "
        f"transported={observation['incremental']['transported_fragments']} "
        f"recomputed={observation['incremental']['recomputed_fragments']}"
    )


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        fail(str(error))
