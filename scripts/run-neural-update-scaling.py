#!/usr/bin/env python3
"""Frozen confirmatory comparison of local and complete artifact rechecking.

The measured property is identical in both paths: every source reference of
the target chain is in range and its output names the final produced node.
The incremental path may reuse only the certified, byte-identical prefix; it
checks every node in the affected suffix.  Deterministic work counters are the
primary measurements.  Wall-clock timings are observations, not proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter_ns

ROOT = Path(__file__).resolve().parent.parent


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def neuron(index: int, threshold: int) -> dict:
    source = {"kind": "received-input", "index": 0} if index == 0 else {
        "kind": "prior-neuron", "index": index - 1
    }
    return {"inputs": [{"source": source, "weight": 1}], "bias": 0,
            "threshold": threshold}


def generate(size: int, cone: int) -> tuple[dict, dict, int]:
    if size < cone or cone < 1:
        raise ValueError("size must be at least the positive cone size")
    source = {"inputCount": 1,
              "neurons": [neuron(i, 0) for i in range(size)],
              "outputs": [size - 1]}
    split = size - cone
    target = {"inputCount": 1,
              "neurons": source["neurons"][:split] +
                  [neuron(i, 1) for i in range(split, size)],
              "outputs": [size - 1]}
    return source, target, split


def check_node(node: dict, produced: int, input_count: int) -> tuple[bool, int]:
    work = 1
    for edge in node["inputs"]:
        work += 1
        src = edge["source"]
        if edge["weight"] == 0:
            return False, work
        if src["kind"] == "received-input":
            if not 0 <= src["index"] < input_count:
                return False, work
        elif src["kind"] == "prior-neuron":
            if not 0 <= src["index"] < produced:
                return False, work
        else:
            return False, work
    return True, work


def full_recheck(artifact: dict) -> tuple[bool, int]:
    work = 1
    if artifact["inputCount"] != 1 or not artifact["neurons"]:
        return False, work
    for index, node in enumerate(artifact["neurons"]):
        valid, local = check_node(node, index, artifact["inputCount"])
        work += local
        if not valid:
            return False, work
    work += len(artifact["outputs"])
    return artifact["outputs"] == [len(artifact["neurons"]) - 1], work


def initial_certificate(source: dict) -> dict:
    valid, work = full_recheck(source)
    if not valid:
        raise ValueError("generator produced an invalid initial artifact")
    return {"property": "serialized-native-system-well-formed",
            "certifiedPrefixLength": len(source["neurons"]),
            "checkedUnits": work}


def incremental_recheck(source: dict, target: dict, split: int,
                        certificate: dict) -> tuple[bool, int, int, int]:
    work = 2
    if certificate["property"] != "serialized-native-system-well-formed":
        return False, work, 0, 0
    if certificate["certifiedPrefixLength"] < split:
        return False, work, 0, 0
    # Equality of every reused fragment is checked, not asserted.
    for old, new in zip(source["neurons"][:split], target["neurons"][:split]):
        work += 1
        if old != new:
            return False, work, 0, 0
    recomputed = 0
    for index, node in enumerate(target["neurons"][split:], start=split):
        valid, local = check_node(node, index, target["inputCount"])
        work += local
        recomputed += 1
        if not valid:
            return False, work, split, recomputed
    work += 1
    valid_output = target["outputs"] == [len(target["neurons"]) - 1]
    return valid_output, work, split, recomputed


def median(values: list[int]) -> int:
    ordered = sorted(values)
    return ordered[len(ordered) // 2]


def serialized_size(value: object) -> int:
    return len(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def measure(size: int, cone: int, repetitions: int) -> dict:
    source, target, split = generate(size, cone)
    generation_times = []
    initial_times = []
    incremental_times = []
    full_times = []
    for _ in range(repetitions):
        start = perf_counter_ns()
        measured_source, measured_target, measured_split = generate(size, cone)
        generation_times.append(perf_counter_ns() - start)
        start = perf_counter_ns()
        certificate = initial_certificate(measured_source)
        initial_times.append(perf_counter_ns() - start)
        start = perf_counter_ns()
        incremental = incremental_recheck(
            measured_source, measured_target, measured_split, certificate)
        incremental_times.append(perf_counter_ns() - start)
        start = perf_counter_ns()
        complete = full_recheck(measured_target)
        full_times.append(perf_counter_ns() - start)
        if not incremental[0] or not complete[0] or incremental[0] != complete[0]:
            raise ValueError("incremental and complete verification disagree")
    certificate = initial_certificate(source)
    incremental = incremental_recheck(source, target, split, certificate)
    complete = full_recheck(target)
    delta_certificate = {
        "property": certificate["property"],
        "reusedPrefixLength": incremental[2],
        "recomputedSuffixLength": incremental[3],
        "targetOutput": target["outputs"],
    }
    return {
        "network_size": size,
        "affected_cone_size": cone,
        "reconfiguration_trace_length": 1,
        "initial_certificate_bytes": serialized_size(certificate),
        "certificate_delta_bytes": serialized_size(delta_certificate),
        "execution_time_ns_median": median(generation_times),
        "initial_verification_time_ns_median": median(initial_times),
        "incremental_recheck_time_ns_median": median(incremental_times),
        "complete_recheck_time_ns_median": median(full_times),
        "incremental_checked_units": incremental[1],
        "complete_checked_units": complete[1],
        "reused_fragments": incremental[2],
        "recomputed_fragments": incremental[3],
        "same_property": certificate["property"],
        "verdicts_equal": incremental[0] == complete[0],
        "target_well_formed": complete[0],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--protocol", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    protocol_path = ROOT / args.protocol
    output_path = ROOT / args.output
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    if protocol["status"] != "frozen-before-confirmatory-run":
        raise ValueError("protocol is not frozen")
    if protocol["script_sha256"] != sha256(Path(__file__)):
        raise ValueError("runner differs from the frozen protocol")
    rows = [measure(size, protocol["affected_cone_size"],
                    protocol["repetitions"]) for size in protocol["sizes"]]
    result = {
        "protocol_id": protocol["protocol_id"],
        "protocol_sha256": sha256(protocol_path),
        "script_sha256": sha256(Path(__file__)),
        "command": protocol["command"],
        "randomness": "none",
        "primary_measure": "deterministic-checked-units",
        "timing_status": "observational-median-not-a-theorem",
        "rows": rows,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
