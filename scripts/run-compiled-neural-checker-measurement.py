#!/usr/bin/env python3
"""Build and measure the compiled public Lean checkers without reimplementing them."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"COMPILED_NEURAL_CHECKER_MEASUREMENT_ERROR: {message}")


def executable_path() -> Path:
    stem = ROOT / ".lake/build/bin/compiled_neural_checker_measure"
    candidates = [stem.with_suffix(".exe"), stem]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    fail("compiled executable is absent after the Lake build")
    raise AssertionError("unreachable")


def run_process(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="strict",
        capture_output=True,
        check=False,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--protocol", required=True)
    parser.add_argument("--output", required=True)
    arguments = parser.parse_args()

    protocol_path = ROOT / arguments.protocol
    output_path = ROOT / arguments.output
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    if protocol.get("protocol_id") != "compiled-neural-checker-measurement-v5":
        fail("wrong protocol id")
    if protocol.get("status") != "frozen-before-confirmatory-run":
        fail("protocol is not frozen before the confirmatory run")
    if protocol.get("runner_sha256") != digest(Path(__file__).resolve()):
        fail("runner differs from the frozen runner")
    for relative, expected in protocol.get("source_sha256", {}).items():
        if digest(ROOT / relative) != expected:
            fail(f"source differs from frozen input: {relative}")

    build_command = protocol.get("build_command")
    if build_command != ["lake", "build", "compiled_neural_checker_measure"]:
        fail("unexpected build command")
    built = run_process(build_command)
    if built.returncode != 0:
        sys.stderr.write(built.stdout)
        sys.stderr.write(built.stderr)
        fail("Lake could not build the compiled checker executable")

    executable = executable_path()
    selector = protocol.get("public_update_selector")
    if selector != "public-update-v1":
        fail("unexpected public update selector")

    negative = run_process([str(executable), "invalid-update"])
    if negative.returncode == 0:
        fail("the executable accepted the frozen invalid-selector control")

    measured = run_process([str(executable), selector])
    if measured.returncode != 0:
        sys.stderr.write(measured.stdout)
        sys.stderr.write(measured.stderr)
        fail("the compiled checker measurement failed")
    try:
        observation = json.loads(measured.stdout)
    except json.JSONDecodeError as error:
        fail(f"compiled executable did not emit one JSON value: {error}")

    expected = protocol["expected_deterministic_observation"]
    for path, value in (
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
    ):
        actual = observation
        for key in path:
            actual = actual[key]
        if actual != value:
            fail(f"unexpected compiled observation at {'.'.join(path)}")

    result = {
        "protocol_id": protocol["protocol_id"],
        "protocol_sha256": digest(protocol_path),
        "runner_sha256": digest(Path(__file__).resolve()),
        "lean_source_sha256": protocol["source_sha256"],
        "executable_sha256": digest(executable),
        "build_command": build_command,
        "execution_command": [
            ".lake/build/bin/compiled_neural_checker_measure" +
            (".exe" if os.name == "nt" else ""),
            selector,
        ],
        "negative_control": {
            "selector": "invalid-update",
            "rejected": True,
            "exit_code": negative.returncode,
        },
        "environment": {
            "operating_system": platform.system(),
            "machine": platform.machine(),
            "python": platform.python_version(),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text(
                encoding="utf-8").strip(),
        },
        "observation": observation,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
