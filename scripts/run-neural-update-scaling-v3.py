#!/usr/bin/env python3
"""Confirmatory local-reuse comparison frozen by the v3 protocol.

The source certificate is tied to the exact in-memory source object, as the
Lean certificate is tied to its indexed source.  The target is materialized
only by applying a suffix delta to that source.  Consequently the incremental
checker may transport the unchanged prefix without reading it again, while the
complete checker validates the same target well-formedness property from zero.
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
    source = ({"kind": "received-input", "index": 0} if index == 0 else
              {"kind": "prior-neuron", "index": index - 1})
    return {"inputs": [{"source": source, "weight": 1}],
            "bias": 0, "threshold": threshold}


def generate(size: int, cone: int) -> tuple[dict, dict]:
    if cone < 1 or size < cone:
        raise ValueError("size must be at least the positive cone size")
    source = {"inputCount": 1,
              "neurons": [neuron(i, 0) for i in range(size)],
              "outputs": [size - 1]}
    split = size - cone
    delta = {"split": split,
             "replacement": [neuron(i, 1) for i in range(split, size)],
             "outputs": [size - 1]}
    return source, delta


def materialize(source: dict, delta: dict) -> dict:
    return {"inputCount": source["inputCount"],
            "neurons": source["neurons"][:delta["split"]] + delta["replacement"],
            "outputs": delta["outputs"]}


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
    work += 1
    return artifact["outputs"] == [len(artifact["neurons"]) - 1], work


def initial_certificate(source: dict) -> dict:
    valid, work = full_recheck(source)
    if not valid:
        raise ValueError("generator produced an invalid initial artifact")
    return {"_source_object": source,
            "property": "serialized-native-system-well-formed",
            "fragments": [1 for _ in source["neurons"]],
            "checkedUnits": work}


def incremental_recheck(source: dict, delta: dict,
                        certificate: dict) -> tuple[bool, int, int, int]:
    work = 3
    if certificate.get("_source_object") is not source:
        return False, work, 0, 0
    if certificate.get("property") != "serialized-native-system-well-formed":
        return False, work, 0, 0
    split = delta["split"]
    if split < 0 or split > len(source["neurons"]):
        return False, work, 0, 0
    if len(certificate["fragments"]) != len(source["neurons"]):
        return False, work, 0, 0
    recomputed = 0
    for index, node in enumerate(delta["replacement"], start=split):
        valid, local = check_node(node, index, source["inputCount"])
        work += local
        recomputed += 1
        if not valid:
            return False, work, split, recomputed
    work += 1
    valid_output = delta["outputs"] == [split + len(delta["replacement"]) - 1]
    return valid_output, work, split, recomputed


def median(values: list[int]) -> int:
    values.sort()
    return values[len(values) // 2]


def size_without_runtime_index(certificate: dict) -> int:
    external = {key: value for key, value in certificate.items()
                if key != "_source_object"}
    return len(json.dumps(external, sort_keys=True, separators=(",", ":")).encode())


def measure(size: int, cone: int, repetitions: int) -> dict:
    execution_times: list[int] = []
    initial_times: list[int] = []
    incremental_times: list[int] = []
    complete_times: list[int] = []
    final = None
    for _ in range(repetitions):
        source, delta = generate(size, cone)
        started = perf_counter_ns()
        target = materialize(source, delta)
        execution_times.append(perf_counter_ns() - started)
        started = perf_counter_ns()
        certificate = initial_certificate(source)
        initial_times.append(perf_counter_ns() - started)
        started = perf_counter_ns()
        incremental = incremental_recheck(source, delta, certificate)
        incremental_times.append(perf_counter_ns() - started)
        started = perf_counter_ns()
        complete = full_recheck(target)
        complete_times.append(perf_counter_ns() - started)
        if not incremental[0] or not complete[0] or incremental[0] != complete[0]:
            raise ValueError("incremental and complete verification disagree")
        final = (source, delta, certificate, incremental, complete)
    assert final is not None
    source, delta, certificate, incremental, complete = final
    delta_certificate = {"property": certificate["property"],
                         "reusedPrefixLength": incremental[2],
                         "recomputedSuffix": [1 for _ in delta["replacement"]],
                         "targetOutput": delta["outputs"]}
    return {
        "network_size": size,
        "affected_cone_size": cone,
        "reconfiguration_trace_length": 1,
        "initial_certificate_bytes": size_without_runtime_index(certificate),
        "certificate_delta_bytes": size_without_runtime_index(delta_certificate),
        "execution_time_ns_median": median(execution_times),
        "initial_verification_time_ns_median": median(initial_times),
        "incremental_recheck_time_ns_median": median(incremental_times),
        "complete_recheck_time_ns_median": median(complete_times),
        "incremental_checked_units": incremental[1],
        "complete_checked_units": complete[1],
        "reused_fragments": incremental[2],
        "recomputed_fragments": incremental[3],
        "same_property": certificate["property"],
        "verdicts_equal": incremental[0] == complete[0],
        "target_well_formed": complete[0]
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
    rows = [measure(size, protocol["affected_cone_size"], protocol["repetitions"])
            for size in protocol["sizes"]]
    result = {"protocol_id": protocol["protocol_id"],
              "protocol_sha256": sha256(protocol_path),
              "script_sha256": sha256(Path(__file__)),
              "command": protocol["command"],
              "randomness": "none",
              "primary_measure": "deterministic-checked-units",
              "timing_status": "observational-median-not-a-theorem",
              "rows": rows}
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
