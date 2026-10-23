#!/usr/bin/env python3
"""Validate the frozen v8 scaling protocol, raw runs and published analysis."""

from __future__ import annotations

import argparse
import copy
from functools import lru_cache
import hashlib
import json
import statistics
from pathlib import Path
import subprocess
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v8"
PROTOCOL = EXPERIMENT / "scaling-protocol.json"
RESULTS = EXPERIMENT / "scaling-results.json"
MANIFEST = EXPERIMENT / "frozen-inputs-manifest.json"
EVIDENCE = EXPERIMENT / "evidence-manifest.json"
ANALYSIS = EXPERIMENT / "SCALING_ANALYSIS.md"
RUNNER = ROOT / "scripts/run-compiled-parameterized-neural-scaling-v8.py"


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


@lru_cache(maxsize=None)
def frozen_bytes(revision: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{revision}:{relative}"], cwd=ROOT,
        capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(f"frozen source is unavailable: {relative}")
    payload = result.stdout
    if relative == "lean-toolchain":
        payload = payload.replace(b"\n", b"\r\n")
    return payload


@lru_cache(maxsize=None)
def frozen_lean_tree(revision: str) -> tuple[tuple[str, bytes], ...]:
    listing = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", revision, "--",
         "RelationalPerimeter"], cwd=ROOT, capture_output=True, text=True,
        check=False)
    if listing.returncode != 0:
        raise ValueError("frozen Lean tree is unavailable")
    paths = sorted(path for path in listing.stdout.splitlines()
                   if path.endswith(".lean"))
    paths.append("Tests/Executables/CompiledParameterizedNeuralCheckerFamily.lean")
    paths.extend(("lakefile.toml", "lake-manifest.json", "lean-toolchain"))
    return tuple((path, frozen_bytes(revision, path)) for path in paths)


def frozen_tree_digest(entries: tuple[tuple[str, bytes], ...]) -> str:
    state = hashlib.sha256()
    for relative_text, payload in sorted(entries):
        relative = relative_text.encode("utf-8")
        state.update(len(relative).to_bytes(8, "big"))
        state.update(relative)
        state.update(len(payload).to_bytes(8, "big"))
        state.update(payload)
    return state.hexdigest()


def percentile(values: list[int], fraction: float) -> int:
    ordered = sorted(values)
    return ordered[round((len(ordered) - 1) * fraction)]


def distribution(values: list[int]) -> dict[str, int]:
    return {
        "minimum": min(values),
        "q1": percentile(values, 0.25),
        "median": int(statistics.median(values)),
        "q3": percentile(values, 0.75),
        "maximum": max(values),
    }


def recompute_summary(size: int, runs: list[dict[str, Any]]) -> dict[str, Any]:
    incremental = [sum(row["incremental_nanoseconds"] for row in run["observations"])
                   for run in runs]
    full = [sum(row["full_recheck_nanoseconds"] for row in run["observations"])
            for run in runs]
    initial = [run["observations"][0]["initial_nanoseconds"] for run in runs]
    incremental_total = [a + b for a, b in zip(initial, incremental)]
    full_total = [a + b for a, b in zip(initial, full)]
    wall = [run["process"]["wall_nanoseconds"] for run in runs]
    peaks = [run["process"]["peak_resident_bytes"] for run in runs
             if run["process"]["peak_resident_bytes"] is not None]
    structure = [{key: row[key] for key in (
        "step", "version", "neural_nodes", "profile_width",
        "causal_graph_nodes", "causal_graph_edges", "affected_cone",
        "transported_fragments", "recomputed_fragments",
        "initial_certificate_entries", "certificate_delta_entries",
        "execution_units", "verification_units")}
        for row in runs[0]["observations"]]
    med_inc = int(statistics.median(incremental_total))
    med_full = int(statistics.median(full_total))
    return {
        "size": size,
        "deterministic_structure": structure,
        "initial_nanoseconds": distribution(initial),
        "incremental_trace_nanoseconds": distribution(incremental),
        "full_recheck_trace_nanoseconds": distribution(full),
        "incremental_total_nanoseconds": distribution(incremental_total),
        "full_recheck_total_nanoseconds": distribution(full_total),
        "process_wall_nanoseconds": distribution(wall),
        "peak_resident_bytes": distribution(peaks) if peaks else None,
        "median_incremental_over_full": med_inc / med_full if med_full else None,
    }


def validate(protocol: dict[str, Any], results: dict[str, Any],
             require_source: bool = True) -> None:
    if protocol.get("protocol_id") != "compiled-parameterized-neural-scaling-v8":
        raise ValueError("wrong protocol id")
    if protocol.get("status") != "frozen-before-single-confirmatory-run":
        raise ValueError("protocol was not frozen")
    if results.get("protocol_id") != protocol["protocol_id"]:
        raise ValueError("results point to another protocol")
    if results.get("protocol_sha256") != digest(PROTOCOL):
        raise ValueError("protocol hash mismatch")
    if results.get("source_sha256") != protocol.get("source_sha256"):
        raise ValueError("result source hashes differ from protocol")
    if protocol.get("runner_sha256") != digest(RUNNER) or \
            results.get("runner_sha256") != digest(RUNNER):
        raise ValueError("runner hash mismatch")
    if require_source:
        revision = protocol.get("frozen_base_commit")
        if not isinstance(revision, str) or len(revision) != 40:
            raise ValueError("missing frozen source commit")
        tree = frozen_lean_tree(revision)
        actual_tree = frozen_tree_digest(tree)
        if protocol.get("lean_tree_file_count") != len(tree) or \
                results.get("lean_tree_file_count") != len(tree) or \
                protocol.get("lean_tree_sha256") != actual_tree or \
                results.get("lean_tree_sha256") != actual_tree:
            raise ValueError("Lean tree hash mismatch")
        for relative, expected in protocol["source_sha256"].items():
            if hashlib.sha256(frozen_bytes(revision, relative)).hexdigest() != expected:
                raise ValueError(f"frozen source is not recoverable: {relative}")

    parameters = protocol["parameters"]
    sizes = parameters["sizes"]
    repetitions = parameters["measured_repetitions"]
    trace_length = parameters["trace_length"]
    runs = results.get("raw_runs", [])
    if len(runs) != len(sizes) * repetitions:
        raise ValueError("wrong measured-run count")
    for size in sizes:
        selected = [run for run in runs if run.get("size") == size]
        if len(selected) != repetitions:
            raise ValueError(f"wrong repetitions at size {size}")
        structural_reference = None
        for repetition, run in enumerate(selected):
            if run.get("repetition") != repetition:
                raise ValueError(f"wrong repetition index at size {size}")
            rows = run.get("observations", [])
            process = run.get("process", {})
            if process.get("exit_code") != 0 or process.get("timed_out") is not False or \
                    process.get("memory_exceeded") is not False:
                raise ValueError(f"unsuccessful measured process at size {size}")
            if process.get("peak_memory_status") not in ("observed", "unavailable"):
                raise ValueError(f"invalid peak-memory status at size {size}")
            if len(rows) != trace_length:
                raise ValueError(f"wrong trace length at size {size}")
            structure = []
            for step, row in enumerate(rows):
                if row.get("status") != "accepted" or row.get("step") != step:
                    raise ValueError(f"rejected or reordered step at size {size}")
                if row["transported_fragments"] + row["recomputed_fragments"] != \
                        row["certificate_delta_entries"]:
                    raise ValueError(f"fragment accounting mismatch at size {size}")
                structure.append(tuple(row[key] for key in (
                    "version", "neural_nodes", "profile_width",
                    "causal_graph_nodes", "causal_graph_edges", "affected_cone",
                    "transported_fragments", "recomputed_fragments",
                    "initial_certificate_entries", "certificate_delta_entries")))
            if structural_reference is None:
                structural_reference = structure
            elif structure != structural_reference:
                raise ValueError(f"nondeterministic structure at size {size}")

    summaries = results.get("summaries", [])
    if [row.get("size") for row in summaries] != sizes:
        raise ValueError("summary sizes differ from protocol")
    recomputed_summaries = [recompute_summary(
        size, [run for run in runs if run.get("size") == size]) for size in sizes]
    if summaries != recomputed_summaries:
        raise ValueError("published summaries do not equal raw-run aggregation")
    for field in ("neural_nodes", "profile_width", "causal_graph_nodes"):
        values = [row["deterministic_structure"][0][field] for row in summaries]
        if any(right <= left for left, right in zip(values, values[1:])):
            raise ValueError(f"{field} does not grow strictly")
    if not all(any(step["transported_fragments"] > 0
                   for step in row["deterministic_structure"])
               for row in summaries):
        raise ValueError("one family size has no transported fragment")
    if not all(any(step["recomputed_fragments"] > 0
                   for step in row["deterministic_structure"])
               for row in summaries):
        raise ValueError("one family size has no recomputed fragment")

    threshold = protocol["practical_gain_rule"]["maximum_incremental_fraction_of_full"]
    floor = protocol["practical_gain_rule"]["sizes_at_or_above"]
    assessed = [row for row in summaries if row["size"] >= floor]
    gain = bool(assessed) and all(
        row["incremental_total_nanoseconds"]["median"] <=
        threshold * row["full_recheck_total_nanoseconds"]["median"]
        for row in assessed)
    if results.get("pre_registered_practical_gain") is not gain:
        raise ValueError("gain verdict does not follow the frozen rule")
    if results.get("interpretation_boundary") != "observational-not-a-Lean-theorem":
        raise ValueError("observation/theorem boundary changed")


def self_test(protocol: dict[str, Any], results: dict[str, Any],
              require_source: bool = True) -> None:
    validate(protocol, results, require_source=require_source)
    mutations = []
    for name, mutation in (
        ("protocol", lambda item: item.__setitem__("protocol_sha256", "0" * 64)),
        ("missing-run", lambda item: item["raw_runs"].pop()),
        ("rejected-step", lambda item: item["raw_runs"][0]["observations"][0].__setitem__("status", "rejected")),
        ("fragment-accounting", lambda item: item["raw_runs"][0]["observations"][0].__setitem__("certificate_delta_entries", 999)),
        ("summary", lambda item: item["summaries"][0]["incremental_trace_nanoseconds"].__setitem__("median", 0)),
        ("gain", lambda item: item.__setitem__("pre_registered_practical_gain", not item["pre_registered_practical_gain"])),
    ):
        changed = copy.deepcopy(results)
        mutation(changed)
        mutations.append((name, changed))
    for name, changed in mutations:
        try:
            validate(protocol, changed, require_source=require_source)
        except ValueError:
            continue
        raise ValueError(f"negative self-test survived: {name}")
    print(f"PARAMETERIZED_NEURAL_SCALING_V8_SELFTEST_OK mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--archive-metadata", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    results = json.loads(RESULTS.read_text(encoding="utf-8"))
    require_source = not arguments.archive_metadata
    validate(protocol, results, require_source=require_source)
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("status") != "frozen-before-confirmatory-run":
        raise ValueError("wrong frozen manifest status")
    frozen_paths = set(protocol["source_sha256"])
    for relative, expected in manifest.get("files", {}).items():
        if arguments.archive_metadata and relative in frozen_paths:
            continue
        actual = (hashlib.sha256(frozen_bytes(
            protocol["frozen_base_commit"], relative)).hexdigest()
            if relative in frozen_paths else digest(ROOT / relative))
        if actual != expected:
            raise ValueError(f"manifest mismatch: {relative}")
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    if evidence.get("status") != "confirmatory-run-complete":
        raise ValueError("wrong evidence manifest status")
    for relative, expected in evidence.get("files", {}).items():
        if digest(ROOT / relative) != expected:
            raise ValueError(f"evidence mismatch: {relative}")
    if not ANALYSIS.exists():
        raise ValueError("analysis is absent")
    if arguments.self_test:
        self_test(protocol, results, require_source=require_source)
    else:
        print("PARAMETERIZED_NEURAL_SCALING_V8_OK "
              f"archive_commit={protocol['frozen_base_commit'][:8]} "
              f"source_reconstructable={str(require_source).lower()} "
              f"sizes={len(protocol['parameters']['sizes'])} "
              f"runs={len(results['raw_runs'])} "
              f"practical_gain={str(results['pre_registered_practical_gain']).lower()}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"PARAMETERIZED_NEURAL_SCALING_V8_ERROR: {error}")
