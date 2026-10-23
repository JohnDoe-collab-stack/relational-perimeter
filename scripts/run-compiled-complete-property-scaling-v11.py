#!/usr/bin/env python3
"""Run the frozen v11 complete-property scaling campaign.

The Python layer never implements either checker.  It builds and invokes the
compiled Lean executable, monitors the process, retains every outcome and
aggregates only the measures fixed by the protocol.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import os
import platform
import statistics
import subprocess
import threading
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
PROTOCOL_ID = "compiled-complete-property-scaling-v11"
EXECUTABLE_NAME = "compiled_complete_property_neural_scaling"


def fail(message: str) -> None:
    raise SystemExit(f"COMPLETE_PROPERTY_SCALING_V11_ERROR: {message}")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_files() -> list[Path]:
    files = sorted((ROOT / "RelationalPerimeter").rglob("*.lean"))
    files.extend(sorted((ROOT / "Tests").rglob("*.lean")))
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


def git_text(*arguments: str) -> str:
    result = subprocess.run(["git", *arguments], cwd=ROOT, text=True,
                            encoding="utf-8", capture_output=True, check=False)
    if result.returncode != 0:
        fail(f"git {' '.join(arguments)} failed")
    return result.stdout.strip()


def executable_path() -> Path:
    stem = ROOT / ".lake/build/bin" / EXECUTABLE_NAME
    for candidate in (stem.with_suffix(".exe"), stem):
        if candidate.exists():
            return candidate
    fail("compiled executable is absent after build")
    raise AssertionError("unreachable")


def windows_rss(process: subprocess.Popen[str]) -> int | None:
    if os.name != "nt":
        return None

    class Counters(ctypes.Structure):
        _fields_ = [
            ("cb", ctypes.c_ulong), ("PageFaultCount", ctypes.c_ulong),
            ("PeakWorkingSetSize", ctypes.c_size_t),
            ("WorkingSetSize", ctypes.c_size_t),
            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPagedPoolUsage", ctypes.c_size_t),
            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
            ("PagefileUsage", ctypes.c_size_t),
            ("PeakPagefileUsage", ctypes.c_size_t),
            ("PrivateUsage", ctypes.c_size_t),
        ]
    counters = Counters()
    counters.cb = ctypes.sizeof(Counters)
    handle = ctypes.c_void_p(int(process._handle))  # type: ignore[attr-defined]
    ok = ctypes.windll.psapi.GetProcessMemoryInfo(  # type: ignore[attr-defined]
        handle, ctypes.byref(counters), counters.cb)
    return int(counters.WorkingSetSize) if ok else None


def linux_rss(process: subprocess.Popen[str]) -> int | None:
    status = Path(f"/proc/{process.pid}/status")
    if not status.exists():
        return None
    for line in status.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("VmRSS:"):
            return int(line.split()[1]) * 1024
    return None


def observed_rss(process: subprocess.Popen[str]) -> int | None:
    try:
        return windows_rss(process) if os.name == "nt" else linux_rss(process)
    except (OSError, ValueError):
        return None


def run_monitored(command: list[str], timeout_seconds: float,
                  memory_limit_bytes: int) -> dict[str, Any]:
    started = time.perf_counter_ns()
    process = subprocess.Popen(command, cwd=ROOT, text=True, encoding="utf-8",
                               errors="strict", stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    captured: dict[str, str] = {}

    def communicate() -> None:
        stdout, stderr = process.communicate()
        captured["stdout"] = stdout
        captured["stderr"] = stderr

    reader = threading.Thread(target=communicate, daemon=True)
    reader.start()
    peak = 0
    timed_out = False
    memory_exceeded = False
    while reader.is_alive():
        rss = observed_rss(process)
        if rss is not None:
            peak = max(peak, rss)
            if rss > memory_limit_bytes:
                memory_exceeded = True
                process.kill()
                break
        if (time.perf_counter_ns() - started) / 1_000_000_000 > timeout_seconds:
            timed_out = True
            process.kill()
            break
        time.sleep(0.001)
    reader.join(timeout=5)
    if reader.is_alive():
        process.kill()
        reader.join()
    return {
        "exit_code": process.returncode,
        "stdout": captured.get("stdout", ""),
        "stderr": captured.get("stderr", ""),
        "wall_nanoseconds": time.perf_counter_ns() - started,
        "peak_resident_bytes": peak if peak else None,
        "peak_memory_status": "observed" if peak else "unavailable",
        "timed_out": timed_out,
        "memory_exceeded": memory_exceeded,
    }


INTEGER_FIELDS = (
    "initial_nanoseconds", "incremental_nanoseconds",
    "full_recheck_nanoseconds", "neural_nodes", "profile_width",
    "causal_graph_nodes", "causal_graph_edges", "affected_cone",
    "transported_fragments", "recomputed_fragments",
    "other_necessary_calculations", "initial_certificate_entries",
    "initial_semantic_checksum", "incremental_semantic_checksum",
    "full_semantic_checksum", "conversion_units", "initialization_units",
    "construction_units", "verification_units", "assembly_units",
    "installation_units", "execution_units", "complete_obligations",
    "full_conversion_units", "full_initialization_units",
    "full_construction_units", "full_verification_units",
    "full_assembly_units", "full_installation_units",
    "full_execution_units",
    "future_trace_length", "certificate_serialized_bytes",
    "delta_serialized_bytes", "transported_serialized_bytes",
    "recomputed_serialized_bytes",
)

INCREMENTAL_PHASE_FIELDS = (
    "conversion_units", "initialization_units", "construction_units",
    "verification_units", "assembly_units", "installation_units",
    "execution_units",
)

FULL_PHASE_FIELDS = (
    "full_conversion_units", "full_initialization_units",
    "full_construction_units", "full_verification_units",
    "full_assembly_units", "full_installation_units",
    "full_execution_units",
)

PHASE_FIELDS = INCREMENTAL_PHASE_FIELDS + FULL_PHASE_FIELDS


def parse_observations(raw: str, size: int,
                       trace_length: int) -> list[dict[str, Any]]:
    lines = [line for line in raw.splitlines() if line.strip()]
    if len(lines) != trace_length:
        raise ValueError(f"expected {trace_length} rows, got {len(lines)}")
    rows: list[dict[str, Any]] = []
    versions = ("local", "source", "extended")
    for step, line in enumerate(lines):
        row = json.loads(line)
        expected = {
            "family_id": PROTOCOL_ID, "status": "accepted", "size": size,
            "step": step, "version": versions[step % 3],
            "timing_status": "raw-observation-not-a-theorem",
        }
        for key, value in expected.items():
            if row.get(key) != value:
                raise ValueError(f"step {step}: unexpected {key}")
        for key in INTEGER_FIELDS:
            if not isinstance(row.get(key), int) or row[key] < 0:
                raise ValueError(f"step {step}: invalid {key}")
        if row["incremental_semantic_checksum"] != row["full_semantic_checksum"]:
            raise ValueError(f"step {step}: semantic disagreement")
        if row["assembly_units"] != (
                row["transported_fragments"] + row["recomputed_fragments"]):
            raise ValueError(f"step {step}: assembly accounting mismatch")
        if row["future_trace_length"] != step + 1:
            raise ValueError(f"step {step}: future trace does not grow")
        rows.append(row)
    return rows


def percentile(values: list[int], fraction: float) -> int:
    ordered = sorted(values)
    return ordered[round((len(ordered) - 1) * fraction)]


def distribution(values: list[int]) -> dict[str, int]:
    return {"minimum": min(values), "q1": percentile(values, .25),
            "median": int(statistics.median(values)),
            "q3": percentile(values, .75), "maximum": max(values)}


def summarize(point: dict[str, int], runs: list[dict[str, Any]]) -> dict[str, Any]:
    successful = [run for run in runs if run["status"] == "accepted"]
    summary: dict[str, Any] = {
        "size": point["size"], "trace_length": point["trace_length"],
        "attempted_repetitions": len(runs),
        "accepted_repetitions": len(successful),
        "failures": [run["failure"] for run in runs
                     if run["status"] != "accepted"],
    }
    if not successful:
        summary["measurement_status"] = "no-complete-run-within-budget"
        return summary
    summary["measurement_status"] = "complete"
    inc = [sum(row["incremental_nanoseconds"] for row in run["observations"])
           for run in successful]
    full = [sum(row["full_recheck_nanoseconds"] for row in run["observations"])
            for run in successful]
    initial = [run["observations"][0]["initial_nanoseconds"]
               for run in successful]
    inc_total = [a + b for a, b in zip(initial, inc)]
    full_total = [a + b for a, b in zip(initial, full)]
    peaks = [run["process"]["peak_resident_bytes"] for run in successful
             if run["process"]["peak_resident_bytes"] is not None]
    structure = [{key: row[key] for key in (
        "step", "version", "neural_nodes", "profile_width",
        "causal_graph_nodes", "causal_graph_edges", "affected_cone",
        "transported_fragments", "recomputed_fragments",
        "other_necessary_calculations", "complete_obligations",
        "future_trace_length", "certificate_serialized_bytes",
        "delta_serialized_bytes", "transported_serialized_bytes",
        "recomputed_serialized_bytes", *PHASE_FIELDS)}
        for row in successful[0]["observations"]]
    incremental_phase_totals = {
        field: sum(row[field] for row in structure)
        for field in INCREMENTAL_PHASE_FIELDS}
    full_phase_totals = {
        field: sum(row[field] for row in structure)
        for field in FULL_PHASE_FIELDS}
    incremental_phase_amortized = {
        field: total / point["trace_length"]
        for field, total in incremental_phase_totals.items()}
    full_phase_amortized = {
        field: total / point["trace_length"]
        for field, total in full_phase_totals.items()}
    summary.update({
        "deterministic_structure": structure,
        "initial_nanoseconds": distribution(initial),
        "incremental_trace_nanoseconds": distribution(inc),
        "full_recheck_trace_nanoseconds": distribution(full),
        "incremental_cumulative_nanoseconds": distribution(inc_total),
        "full_recheck_cumulative_nanoseconds": distribution(full_total),
        "incremental_amortized_nanoseconds_per_step": distribution(
            [value // point["trace_length"] for value in inc_total]),
        "full_recheck_amortized_nanoseconds_per_step": distribution(
            [value // point["trace_length"] for value in full_total]),
        "process_wall_nanoseconds": distribution(
            [run["process"]["wall_nanoseconds"] for run in successful]),
        "peak_resident_bytes": distribution(peaks) if peaks else None,
        "incremental_cumulative_phase_units": incremental_phase_totals,
        "full_recheck_cumulative_phase_units": full_phase_totals,
        "incremental_amortized_phase_units_per_step":
            incremental_phase_amortized,
        "full_recheck_amortized_phase_units_per_step":
            full_phase_amortized,
        "median_incremental_over_full":
            int(statistics.median(inc_total)) /
            int(statistics.median(full_total)),
    })
    return summary


def validate_frozen_source(protocol: dict[str, Any], protocol_path: Path) -> None:
    if protocol.get("protocol_id") != PROTOCOL_ID:
        fail("wrong protocol id")
    if protocol.get("status") != "frozen-before-confirmatory-run":
        fail("protocol is not frozen")
    revision = protocol.get("frozen_source_commit")
    if not isinstance(revision, str) or len(revision) != 40:
        fail("missing recoverable source commit")
    if git_text("status", "--porcelain"):
        fail("working tree is not clean")
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", revision, "HEAD"], cwd=ROOT,
        capture_output=True, check=False)
    if ancestor.returncode != 0:
        fail("frozen source commit is not an ancestor of HEAD")
    frozen_tree = git_text("rev-parse", f"{revision}^{{tree}}")
    if protocol.get("frozen_source_git_tree") != frozen_tree:
        fail("frozen source commit does not recover the preregistered Git tree")
    if protocol.get("runner_sha256") != digest(Path(__file__).resolve()):
        fail("runner differs from frozen runner")
    files = tree_files()
    if protocol.get("source_tree_file_count") != len(files) or \
            protocol.get("source_tree_sha256") != tree_digest(files):
        fail("compiled source tree differs from frozen snapshot")
    for relative, expected in protocol.get("source_sha256", {}).items():
        if digest(ROOT / relative) != expected:
            fail(f"source differs from frozen input: {relative}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--protocol", required=True)
    parser.add_argument("--output", required=True)
    arguments = parser.parse_args()
    protocol_path = ROOT / arguments.protocol
    output_path = ROOT / arguments.output
    if output_path.exists():
        fail("confirmatory output exists; refusing to overwrite it")
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    validate_frozen_source(protocol, protocol_path)
    build = subprocess.run(protocol["build_command"], cwd=ROOT, text=True,
                           encoding="utf-8", capture_output=True, check=False)
    if build.returncode != 0:
        fail("Lake could not build the frozen executable")
    executable = executable_path()
    negative = subprocess.run([str(executable), "invalid", "1"], cwd=ROOT,
                              text=True, encoding="utf-8", capture_output=True,
                              check=False)
    if negative.returncode == 0:
        fail("invalid-argument control was accepted")

    budget = protocol["resource_budget"]
    repetitions = protocol["parameters"]["measured_repetitions"]
    warmups = protocol["parameters"]["warmup_repetitions"]
    raw_runs: list[dict[str, Any]] = []
    for point in protocol["parameters"]["points"]:
        command = [str(executable), str(point["size"]),
                   str(point["trace_length"])]
        for _ in range(warmups):
            warm = run_monitored(command, budget["timeout_seconds_per_process"],
                                 budget["resident_memory_limit_bytes"])
            if warm["exit_code"] != 0 or warm["timed_out"] or warm["memory_exceeded"]:
                break
        for repetition in range(repetitions):
            measured = run_monitored(command, budget["timeout_seconds_per_process"],
                                     budget["resident_memory_limit_bytes"])
            record: dict[str, Any] = {
                "size": point["size"], "trace_length": point["trace_length"],
                "repetition": repetition, "process": {
                    key: measured[key] for key in (
                        "exit_code", "wall_nanoseconds", "peak_resident_bytes",
                        "peak_memory_status", "timed_out", "memory_exceeded")}}
            try:
                if measured["exit_code"] != 0 or measured["timed_out"] or \
                        measured["memory_exceeded"]:
                    raise ValueError("process did not complete within frozen budget")
                if measured["peak_resident_bytes"] is None:
                    raise ValueError("resident memory measurement is unavailable")
                record["observations"] = parse_observations(
                    measured["stdout"], point["size"], point["trace_length"])
                record["status"] = "accepted"
            except (ValueError, json.JSONDecodeError) as error:
                record["status"] = "failed"
                record["failure"] = {
                    "reason": str(error), "stderr": measured["stderr"][:4096]}
            raw_runs.append(record)

    summaries = [summarize(point, [run for run in raw_runs
                                   if run["size"] == point["size"] and
                                   run["trace_length"] == point["trace_length"]])
                 for point in protocol["parameters"]["points"]]
    rule = protocol["practical_gain_rule"]
    assessed = [row for row in summaries
                if row["size"] >= rule["sizes_at_or_above"]]
    practical_gain = bool(assessed) and all(
        row.get("measurement_status") == "complete" and
        row["accepted_repetitions"] == repetitions and
        row["incremental_cumulative_nanoseconds"]["median"] <=
        rule["maximum_incremental_fraction_of_full"] *
        row["full_recheck_cumulative_nanoseconds"]["median"]
        for row in assessed)
    result = {
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": digest(protocol_path),
        "frozen_source_commit": protocol["frozen_source_commit"],
        "runner_sha256": digest(Path(__file__).resolve()),
        "source_tree_file_count": protocol["source_tree_file_count"],
        "source_tree_sha256": protocol["source_tree_sha256"],
        "executable_sha256": digest(executable),
        "environment": {"operating_system": platform.platform(),
                        "machine": platform.machine(),
                        "python": platform.python_version(),
                        "lean_toolchain": (ROOT / "lean-toolchain").read_text(
                            encoding="utf-8").strip()},
        "negative_control": {"rejected": True,
                             "exit_code": negative.returncode},
        "raw_runs": raw_runs, "summaries": summaries,
        "pre_registered_practical_gain": practical_gain,
        "result_status": "confirmatory-complete",
        "interpretation_boundary": "observational-not-a-Lean-theorem",
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
