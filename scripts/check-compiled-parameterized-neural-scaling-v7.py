#!/usr/bin/env python3
"""Validate the frozen protocol and immutable v7 scaling observations."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v7"
PROTOCOL = EXPERIMENT / "scaling-protocol.json"
RESULTS = EXPERIMENT / "scaling-results.json"
MANIFEST = EXPERIMENT / "frozen-inputs-manifest.json"
ANALYSIS = EXPERIMENT / "SCALING_ANALYSIS.md"
RUNNER = ROOT / "scripts/run-compiled-parameterized-neural-scaling-v7.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_tree() -> list[Path]:
    files = sorted((ROOT / "RelationalPerimeter").rglob("*.lean"))
    files.append(ROOT / "Tests/Executables/CompiledParameterizedNeuralCheckerFamily.lean")
    files.extend((ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                  ROOT / "lean-toolchain"))
    return files


def tree_digest(files: list[Path]) -> str:
    state = hashlib.sha256()
    for path in sorted(files):
        relative = path.relative_to(ROOT).as_posix().encode("utf-8")
        payload = path.read_bytes()
        state.update(len(relative).to_bytes(8, "big"))
        state.update(relative)
        state.update(len(payload).to_bytes(8, "big"))
        state.update(payload)
    return state.hexdigest()


def reject(message: str) -> None:
    raise ValueError(message)


def validate(protocol: dict[str, Any], results: dict[str, Any]) -> None:
    if protocol.get("protocol_id") != "compiled-parameterized-neural-scaling-v7":
        reject("wrong protocol id")
    if protocol.get("status") != "frozen-before-single-confirmatory-run":
        reject("protocol was not pre-frozen")
    if results.get("protocol_id") != protocol["protocol_id"]:
        reject("results point to another protocol")
    if results.get("protocol_sha256") != digest(PROTOCOL):
        reject("protocol hash mismatch")
    if protocol.get("runner_sha256") != digest(RUNNER) or \
            results.get("runner_sha256") != digest(RUNNER):
        reject("runner hash mismatch")
    frozen_tree = lean_tree()
    if protocol.get("lean_tree_file_count") != len(frozen_tree) or \
            results.get("lean_tree_file_count") != len(frozen_tree) or \
            protocol.get("lean_tree_sha256") != tree_digest(frozen_tree) or \
            results.get("lean_tree_sha256") != tree_digest(frozen_tree):
        reject("compiled Lean source tree hash mismatch")
    for relative, expected in protocol["source_sha256"].items():
        if digest(ROOT / relative) != expected:
            reject(f"source hash mismatch: {relative}")
    parameters = protocol["parameters"]
    sizes = parameters["sizes"]
    repetitions = parameters["measured_repetitions"]
    trace_length = parameters["trace_length"]
    runs = results.get("raw_runs", [])
    if len(runs) != len(sizes) * repetitions:
        reject("wrong number of measured runs")
    for size in sizes:
        selected = [run for run in runs if run.get("size") == size]
        if len(selected) != repetitions:
            reject(f"wrong repetition count at size {size}")
        reference = None
        for repetition, run in enumerate(selected):
            if run.get("repetition") != repetition:
                reject(f"noncanonical repetition index at size {size}")
            observations = run.get("observations", [])
            if len(observations) != trace_length:
                reject(f"wrong trace length at size {size}")
            structure = []
            for step, row in enumerate(observations):
                if row.get("status") != "accepted" or row.get("step") != step:
                    reject(f"rejected or misplaced step at size {size}")
                if row["transported_fragments"] + row["recomputed_fragments"] != \
                        row["certificate_delta_entries"]:
                    reject(f"fragment accounting mismatch at size {size}")
                structure.append(tuple(row[key] for key in (
                    "version", "neural_nodes", "profile_width",
                    "causal_graph_nodes", "causal_graph_edges", "affected_cone",
                    "transported_fragments", "recomputed_fragments",
                    "initial_certificate_entries", "certificate_delta_entries")))
            if reference is None:
                reference = structure
            elif structure != reference:
                reject(f"structural observations vary between repetitions at size {size}")
    summaries = results.get("summaries", [])
    if [row.get("size") for row in summaries] != sizes:
        reject("summary sizes differ from the frozen sizes")
    graph_nodes = [row["deterministic_structure"][0]["causal_graph_nodes"]
                   for row in summaries]
    profile_widths = [row["deterministic_structure"][0]["profile_width"]
                      for row in summaries]
    neural_nodes = [row["deterministic_structure"][0]["neural_nodes"]
                    for row in summaries]
    for values, label in ((graph_nodes, "graph"), (profile_widths, "profile"),
                          (neural_nodes, "network")):
        if any(right <= left for left, right in zip(values, values[1:])):
            reject(f"{label} does not grow strictly")
    if not any(step["transported_fragments"] > step["recomputed_fragments"]
               for row in summaries for step in row["deterministic_structure"]
               if step["version"] == "local"):
        reject("no local reuse is observed")
    if not any(step["recomputed_fragments"] > step["transported_fragments"]
               for row in summaries for step in row["deterministic_structure"]
               if step["version"] == "extended"):
        reject("no extended-cone recomputation is observed")
    threshold = protocol["practical_gain_rule"]["maximum_incremental_fraction_of_full"]
    floor = protocol["practical_gain_rule"]["sizes_at_or_above"]
    assessed = [row for row in summaries if row["size"] >= floor]
    recomputed = bool(assessed) and all(
        row["incremental_total_nanoseconds"]["median"] <=
        threshold * row["full_recheck_total_nanoseconds"]["median"]
        for row in assessed)
    if results.get("pre_registered_practical_gain") is not recomputed:
        reject("practical-gain verdict does not follow the frozen rule")
    if results.get("interpretation_boundary") != "observational-not-a-Lean-theorem":
        reject("results overstate observations as a theorem")


def self_test(protocol: dict[str, Any], results: dict[str, Any]) -> None:
    validate(protocol, results)
    mutations = []
    for name, mutate in (
        ("wrong-protocol", lambda item: item.__setitem__("protocol_sha256", "0" * 64)),
        ("drop-run", lambda item: item["raw_runs"].pop()),
        ("fake-accept", lambda item: item["raw_runs"][0]["observations"][0].__setitem__("status", "rejected")),
        ("split-fragments", lambda item: item["raw_runs"][0]["observations"][0].__setitem__("certificate_delta_entries", 999)),
        ("fake-gain", lambda item: item.__setitem__("pre_registered_practical_gain", not item["pre_registered_practical_gain"])),
    ):
        changed = copy.deepcopy(results)
        mutate(changed)
        mutations.append((name, changed))
    for name, changed in mutations:
        try:
            validate(protocol, changed)
        except ValueError:
            continue
        reject(f"negative self-test survived: {name}")
    print(f"PARAMETERIZED_NEURAL_SCALING_V7_SELFTEST_OK mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    results = json.loads(RESULTS.read_text(encoding="utf-8"))
    validate(protocol, results)
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("status") != "frozen-before-confirmatory-run":
        reject("input manifest has the wrong status")
    for relative, expected in manifest.get("files", {}).items():
        if digest(ROOT / relative) != expected:
            reject(f"frozen manifest mismatch: {relative}")
    if not ANALYSIS.exists():
        reject("analysis is absent")
    if arguments.self_test:
        self_test(protocol, results)
        return
    print("PARAMETERIZED_NEURAL_SCALING_V7_OK "
          f"sizes={len(protocol['parameters']['sizes'])} "
          f"runs={len(results['raw_runs'])} "
          f"practical_gain={str(results['pre_registered_practical_gain']).lower()}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"PARAMETERIZED_NEURAL_SCALING_V7_ERROR: {error}")
