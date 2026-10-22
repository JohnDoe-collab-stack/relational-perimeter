#!/usr/bin/env python3
"""Run the one-shot confirmatory scaling campaign for the compiled Lean checker.

This runner does not reimplement either checker.  It builds and invokes the
Lean executable frozen by the v7 protocol, records every emitted observation,
and reports process-level wall time and peak resident memory.
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
import sys
import threading
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
PROTOCOL_ID = "compiled-parameterized-neural-scaling-v7"


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


def fail(message: str) -> None:
    raise SystemExit(f"PARAMETERIZED_NEURAL_SCALING_V7_ERROR: {message}")


def executable_path() -> Path:
    stem = ROOT / ".lake/build/bin/compiled_parameterized_neural_checker"
    for candidate in (stem.with_suffix(".exe"), stem):
        if candidate.exists():
            return candidate
    fail("compiled executable is absent after the Lake build")
    raise AssertionError("unreachable")


def windows_rss(process: subprocess.Popen[str]) -> int | None:
    if os.name != "nt":
        return None

    class Counters(ctypes.Structure):
        _fields_ = [
            ("cb", ctypes.c_ulong),
            ("PageFaultCount", ctypes.c_ulong),
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
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="strict",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    result: dict[str, str] = {}

    def communicate() -> None:
        stdout, stderr = process.communicate()
        result["stdout"] = stdout
        result["stderr"] = stderr

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
    finished = time.perf_counter_ns()
    return {
        "exit_code": process.returncode,
        "stdout": result.get("stdout", ""),
        "stderr": result.get("stderr", ""),
        "wall_nanoseconds": finished - started,
        "peak_resident_bytes": peak if peak > 0 else None,
        "peak_memory_status": "observed" if peak > 0 else "unavailable",
        "timed_out": timed_out,
        "memory_exceeded": memory_exceeded,
    }


def parse_observations(raw: str, size: int, trace_length: int) -> list[dict[str, Any]]:
    lines = [line for line in raw.splitlines() if line.strip()]
    if len(lines) != trace_length:
        fail(f"size {size}: expected {trace_length} observations, got {len(lines)}")
    observations: list[dict[str, Any]] = []
    versions = ("local", "source", "extended")
    for step, line in enumerate(lines):
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            fail(f"size {size}: invalid NDJSON at step {step}: {error}")
        expected = {
            "family_id": "compiled-parameterized-constitutive-checker-v1",
            "status": "accepted",
            "size": size,
            "step": step,
            "version": versions[step % 3],
            "timing_status": "raw-observation-not-a-theorem",
        }
        for key, value in expected.items():
            if row.get(key) != value:
                fail(f"size {size} step {step}: unexpected {key}")
        for key in (
            "initial_nanoseconds", "incremental_nanoseconds",
            "full_recheck_nanoseconds", "neural_nodes", "profile_width",
            "causal_graph_nodes", "causal_graph_edges", "affected_cone",
            "transported_fragments", "recomputed_fragments",
            "initial_certificate_entries", "certificate_delta_entries",
            "execution_units", "verification_units",
        ):
            if not isinstance(row.get(key), int) or row[key] < 0:
                fail(f"size {size} step {step}: invalid {key}")
        if row["transported_fragments"] + row["recomputed_fragments"] != \
                row["certificate_delta_entries"]:
            fail(f"size {size} step {step}: fragment accounting mismatch")
        observations.append(row)
    return observations


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


def summarize(size: int, runs: list[dict[str, Any]]) -> dict[str, Any]:
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--protocol", required=True)
    parser.add_argument("--output", required=True)
    arguments = parser.parse_args()
    protocol_path = ROOT / arguments.protocol
    output_path = ROOT / arguments.output
    if output_path.exists():
        fail("confirmatory output already exists; refusing to overwrite it")
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    if protocol.get("protocol_id") != PROTOCOL_ID:
        fail("wrong protocol id")
    if protocol.get("status") != "frozen-before-single-confirmatory-run":
        fail("protocol is not frozen before one confirmatory run")
    if protocol.get("runner_sha256") != digest(Path(__file__).resolve()):
        fail("runner differs from frozen runner")
    frozen_tree = lean_tree()
    if protocol.get("lean_tree_file_count") != len(frozen_tree) or \
            protocol.get("lean_tree_sha256") != tree_digest(frozen_tree):
        fail("compiled Lean source tree differs from the frozen tree")
    for relative, expected in protocol.get("source_sha256", {}).items():
        if digest(ROOT / relative) != expected:
            fail(f"source differs from frozen input: {relative}")

    build = subprocess.run(protocol["build_command"], cwd=ROOT, text=True,
                           encoding="utf-8", capture_output=True, check=False)
    if build.returncode != 0:
        sys.stderr.write(build.stdout + build.stderr)
        fail("Lake could not build the compiled checker")
    executable = executable_path()
    negative = subprocess.run([str(executable), "invalid", "1"], cwd=ROOT,
                              text=True, encoding="utf-8", capture_output=True,
                              check=False)
    if negative.returncode == 0:
        fail("invalid-size negative control was accepted")

    sizes = protocol["parameters"]["sizes"]
    trace_length = protocol["parameters"]["trace_length"]
    repetitions = protocol["parameters"]["measured_repetitions"]
    warmups = protocol["parameters"]["warmup_repetitions"]
    timeout = protocol["resource_budget"]["timeout_seconds_per_process"]
    memory = protocol["resource_budget"]["resident_memory_limit_bytes"]
    raw_runs: list[dict[str, Any]] = []
    for size in sizes:
        for _ in range(warmups):
            warm = run_monitored([str(executable), str(size), str(trace_length)],
                                 timeout, memory)
            if warm["exit_code"] != 0 or warm["timed_out"] or warm["memory_exceeded"]:
                fail(f"warmup failed at size {size}: {warm['stderr']}")
            parse_observations(warm["stdout"], size, trace_length)
        for repetition in range(repetitions):
            measured = run_monitored(
                [str(executable), str(size), str(trace_length)], timeout, memory)
            if measured["timed_out"]:
                fail(f"timeout at size {size} repetition {repetition}")
            if measured["memory_exceeded"]:
                fail(f"memory limit at size {size} repetition {repetition}")
            if measured["exit_code"] != 0:
                fail(f"checker failed at size {size}: {measured['stderr']}")
            observations = parse_observations(measured.pop("stdout"), size, trace_length)
            measured.pop("stderr", None)
            raw_runs.append({
                "size": size,
                "repetition": repetition,
                "observations": observations,
                "process": measured,
            })

    summaries = [summarize(size, [run for run in raw_runs if run["size"] == size])
                 for size in sizes]
    threshold = protocol["practical_gain_rule"]["maximum_incremental_fraction_of_full"]
    threshold_sizes = protocol["practical_gain_rule"]["sizes_at_or_above"]
    assessed = [row for row in summaries if row["size"] >= threshold_sizes]
    practical_gain = bool(assessed) and all(
        row["incremental_total_nanoseconds"]["median"] <=
        threshold * row["full_recheck_total_nanoseconds"]["median"]
        for row in assessed)
    result = {
        "protocol_id": PROTOCOL_ID,
        "protocol_sha256": digest(protocol_path),
        "runner_sha256": digest(Path(__file__).resolve()),
        "source_sha256": protocol["source_sha256"],
        "lean_tree_file_count": len(frozen_tree),
        "lean_tree_sha256": tree_digest(frozen_tree),
        "executable_sha256": digest(executable),
        "environment": {
            "operating_system": platform.platform(),
            "machine": platform.machine(),
            "python": platform.python_version(),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        },
        "negative_control": {"rejected": True, "exit_code": negative.returncode},
        "raw_runs": raw_runs,
        "summaries": summaries,
        "pre_registered_practical_gain": practical_gain,
        "interpretation_boundary": "observational-not-a-Lean-theorem",
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
