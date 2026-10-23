#!/usr/bin/env python3
"""Validate the v11 preregistration and, when present, all published evidence."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v11"
PROTOCOL = EXPERIMENT / "scaling-protocol.json"
RESULTS = EXPERIMENT / "scaling-results.json"
PROTOCOL_ID = "compiled-complete-property-scaling-v11"
EXPECTED_OBLIGATIONS = {
    "requirement encoding incorporation",
    "executed causal role",
    "proposal-to-action execution",
    "incorporated authorization",
    "produced effect",
    "finite covered future",
    "exact native run history",
}
REQUIRED_PHASES = {
    "conversion_units", "initialization_units", "construction_units",
    "verification_units", "assembly_units", "installation_units",
    "execution_units", "full_conversion_units",
    "full_initialization_units", "full_construction_units",
    "full_verification_units", "full_assembly_units",
    "full_installation_units", "full_execution_units",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def validate_protocol(protocol: dict[str, Any], allow_draft: bool) -> None:
    require(protocol.get("protocol_id") == PROTOCOL_ID, "wrong protocol id")
    expected_status = ("draft-awaiting-stable-source-commit",
                       "frozen-before-confirmatory-run") if allow_draft else (
                           "frozen-before-confirmatory-run",)
    require(protocol.get("status") in expected_status, "invalid protocol status")
    points = protocol["parameters"]["points"]
    require(len(points) >= 5, "fewer than five scale points")
    sizes = [point["size"] for point in points]
    traces = [point["trace_length"] for point in points]
    require(all(right > left for left, right in zip(sizes, sizes[1:])),
            "sizes do not strictly grow")
    require(all(right > left for left, right in zip(traces, traces[1:])),
            "trace lengths do not strictly grow")
    require(protocol["parameters"]["measured_repetitions"] >= 5,
            "insufficient repetitions")
    obligations = protocol["complete_property"]["contract_obligations"]
    require(set(obligations) == EXPECTED_OBLIGATIONS,
            "complete contract obligations changed")
    require(protocol["complete_property"].get("unit_obligations_forbidden") is True,
            "unit-obligation substitution is not forbidden")
    require(set(protocol["accounting"]["phase_units"]) == REQUIRED_PHASES,
            "phase accounting is incomplete")
    require(protocol["practical_gain_rule"].get(
        "selection_counts_never_establish_gain") is True,
        "selection count can masquerade as gain")
    require(protocol["resource_budget"]["failure_policy"],
            "failure policy is absent")
    for relative, expected in protocol["historical_evidence_preserved"].items():
        path = ROOT / relative
        require(path.exists() and digest(path) == expected,
                f"historical evidence changed: {relative}")
    if protocol["status"] == "frozen-before-confirmatory-run":
        revision = protocol.get("frozen_source_commit")
        require(isinstance(revision, str) and len(revision) == 40,
                "frozen source commit is absent")
        require(isinstance(protocol.get("source_tree_file_count"), int),
                "source file count is absent")
        require(isinstance(protocol.get("source_tree_sha256"), str),
                "source tree hash is absent")
        require(isinstance(protocol.get("frozen_source_git_tree"), str) and
                len(protocol["frozen_source_git_tree"]) == 40,
                "recoverable Git tree is absent")
        require(isinstance(protocol.get("runner_sha256"), str),
                "runner hash is absent")
        require(len(protocol.get("source_sha256", {})) >= 9,
                "frozen source inventory is incomplete")


def validate_result(protocol: dict[str, Any], result: dict[str, Any]) -> None:
    require(protocol["status"] == "frozen-before-confirmatory-run",
            "results exist for an unfrozen protocol")
    require(result.get("protocol_id") == PROTOCOL_ID, "result protocol mismatch")
    require(result.get("protocol_sha256") == digest(PROTOCOL),
            "result protocol hash mismatch")
    require(result.get("frozen_source_commit") == protocol["frozen_source_commit"],
            "result source commit mismatch")
    require(result.get("result_status") == "confirmatory-complete",
            "result status is not final")
    require(result.get("interpretation_boundary") ==
            "observational-not-a-Lean-theorem", "theorem boundary changed")
    require(result.get("negative_control", {}).get("rejected") is True,
            "negative control was not rejected")
    repetitions = protocol["parameters"]["measured_repetitions"]
    raw = result.get("raw_runs", [])
    points = protocol["parameters"]["points"]
    require(len(raw) == repetitions * len(points), "wrong raw-run count")
    summaries = result.get("summaries", [])
    require(len(summaries) == len(points), "wrong summary count")
    for point, summary in zip(points, summaries):
        require(summary.get("size") == point["size"] and
                summary.get("trace_length") == point["trace_length"],
                "summary point mismatch")
        selected = [run for run in raw if run.get("size") == point["size"] and
                    run.get("trace_length") == point["trace_length"]]
        require(len(selected) == repetitions, "wrong repetitions at point")
        for run in selected:
            if run.get("status") != "accepted":
                require("failure" in run, "failed run lacks published reason")
                continue
            rows = run.get("observations", [])
            require(len(rows) == point["trace_length"], "wrong trace length")
            for step, row in enumerate(rows):
                for field in REQUIRED_PHASES:
                    require(isinstance(row.get(field), int) and row[field] >= 0,
                            f"invalid phase count: {field}")
                require(row["future_trace_length"] == step + 1,
                        "future trace does not grow")
                require(row["incremental_semantic_checksum"] ==
                        row["full_semantic_checksum"], "semantic disagreement")
                require(row["assembly_units"] == row["transported_fragments"] +
                        row["recomputed_fragments"], "assembly mismatch")
                require(row["full_assembly_units"] >=
                        row["transported_fragments"] +
                        row["recomputed_fragments"],
                        "full assembly understates the complete target")
                require(row["complete_obligations"] > 7,
                        "unit-like complete property")
                require(row["certificate_serialized_bytes"] > 0 and
                        row["delta_serialized_bytes"] > 0,
                        "serialized sizes are absent")
                require(run["process"].get("peak_memory_status") == "observed" and
                        isinstance(run["process"].get("peak_resident_bytes"), int) and
                        run["process"]["peak_resident_bytes"] > 0,
                        "resident memory was not measured")
            obligation_counts = [row["complete_obligations"] for row in rows]
            require(all(right > left for left, right in
                        zip(obligation_counts, obligation_counts[1:])),
                    "complete obligations do not grow through the trace")
            local_rows = [row for row in rows if row.get("version") == "local"]
            extended_rows = [row for row in rows
                             if row.get("version") == "extended"]
            require(local_rows and any(row["transported_fragments"] > 0
                                       for row in local_rows),
                    "local cone transports no fragment")
            require(extended_rows and any(row["recomputed_fragments"] > 0
                                          for row in extended_rows),
                    "extended cone recomputes no fragment")
        require("failures" in summary, "summary does not publish failures")
        if summary.get("measurement_status") == "complete":
            require("incremental_cumulative_phase_units" in summary and
                    "full_recheck_cumulative_phase_units" in summary and
                    "incremental_amortized_phase_units_per_step" in summary and
                    "full_recheck_amortized_phase_units_per_step" in summary,
                    "paired cumulative or amortized costs are absent")
    complete = [summary for summary in summaries
                if summary.get("measurement_status") == "complete"]
    if complete:
        first_rows = [summary["deterministic_structure"][0]
                      for summary in complete]
        for field in ("neural_nodes", "causal_graph_nodes", "causal_graph_edges",
                      "complete_obligations"):
            values = [row[field] for row in first_rows]
            require(all(right > left for left, right in zip(values, values[1:])),
                    f"{field} does not grow")
        require(all(any(row["transported_fragments"] > 0
                        for row in summary["deterministic_structure"])
                    for summary in complete), "local transport is absent")
        require(all(any(row["recomputed_fragments"] > 0
                        for row in summary["deterministic_structure"])
                    for summary in complete), "extended recomputation is absent")
    rule = protocol["practical_gain_rule"]
    assessed = [summary for summary in summaries
                if summary["size"] >= rule["sizes_at_or_above"]]
    expected_gain = bool(assessed) and all(
        summary.get("measurement_status") == "complete" and
        summary.get("accepted_repetitions") == repetitions and
        summary["incremental_cumulative_nanoseconds"]["median"] <=
        rule["maximum_incremental_fraction_of_full"] *
        summary["full_recheck_cumulative_nanoseconds"]["median"]
        for summary in assessed)
    require(result.get("pre_registered_practical_gain") is expected_gain,
            "gain verdict does not follow the preregistered rule")


def self_test(protocol: dict[str, Any]) -> None:
    mutations: list[tuple[str, dict[str, Any]]] = []
    changed = copy.deepcopy(protocol)
    changed["complete_property"]["contract_obligations"].pop()
    mutations.append(("missing-obligation", changed))
    changed = copy.deepcopy(protocol)
    changed["parameters"]["points"][1]["size"] = 0
    mutations.append(("nongrowing-size", changed))
    changed = copy.deepcopy(protocol)
    changed["historical_evidence_preserved"][next(iter(
        changed["historical_evidence_preserved"]))] = "0" * 64
    mutations.append(("historical-rewrite", changed))
    changed = copy.deepcopy(protocol)
    changed["accounting"]["phase_units"].remove("full_verification_units")
    mutations.append(("missing-full-reference-phase", changed))
    changed = copy.deepcopy(protocol)
    changed["practical_gain_rule"]["selection_counts_never_establish_gain"] = False
    mutations.append(("selection-count-gain", changed))
    for name, mutation in mutations:
        try:
            validate_protocol(mutation, allow_draft=True)
        except ValueError:
            continue
        raise ValueError(f"negative self-test survived: {name}")
    print(f"COMPLETE_PROPERTY_SCALING_V11_SELFTEST_OK mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-draft", action="store_true")
    parser.add_argument("--require-results", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    validate_protocol(protocol, allow_draft=arguments.allow_draft)
    if RESULTS.exists():
        validate_result(protocol, json.loads(RESULTS.read_text(encoding="utf-8")))
        result_state = "present"
    else:
        require(not arguments.require_results, "confirmatory results are absent")
        result_state = "absent"
    if arguments.self_test:
        self_test(protocol)
    else:
        print("COMPLETE_PROPERTY_SCALING_V11_OK "
              f"status={protocol['status']} results={result_state}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"COMPLETE_PROPERTY_SCALING_V11_ERROR: {error}")
