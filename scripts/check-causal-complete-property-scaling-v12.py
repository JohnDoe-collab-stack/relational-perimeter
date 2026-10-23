#!/usr/bin/env python3
"""Validate the frozen v12 causal protocol and its optional results."""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
LEGACY = ROOT / "scripts/check-complete-property-scaling-v11.py"
SPEC = importlib.util.spec_from_file_location("complete_property_v11_checker", LEGACY)
if SPEC is None or SPEC.loader is None:
    raise SystemExit("CAUSAL_COMPLETE_PROPERTY_SCALING_V12_ERROR: v11 checker unavailable")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)

CHECKER.EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v12"
CHECKER.PROTOCOL = CHECKER.EXPERIMENT / "scaling-protocol.json"
CHECKER.RESULTS = CHECKER.EXPERIMENT / "scaling-results.json"
CHECKER.PROTOCOL_ID = "compiled-causal-complete-property-scaling-v12"

legacy_validate_protocol = CHECKER.validate_protocol
legacy_validate_result = CHECKER.validate_result


def validate_protocol(protocol: dict[str, Any], allow_draft: bool) -> None:
    legacy_validate_protocol(protocol, allow_draft)
    causal = protocol.get("causal_transition_property", {})
    CHECKER.require(causal.get("source_consumed_by_action") is True,
                    "action is not required to consume the checked source")
    CHECKER.require(causal.get("effective_register_progress") is True,
                    "transition is not required to change the produced state")
    CHECKER.require(causal.get("action_consumed_by_effect") is True,
                    "effect is not required to consume the produced action")
    CHECKER.require(causal.get("effect_consumed_by_successor") is True,
                    "successor is not required to consume the produced effect")
    CHECKER.require(causal.get("trace_continues_from_installed_successor") is True,
                    "trace continuation is not source indexed")
    CHECKER.require(causal.get("v11_remains_historical_negative") is True,
                    "v11 has been reclassified")


def validate_result(protocol: dict[str, Any], result: dict[str, Any]) -> None:
    legacy_validate_result(protocol, result)
    for run in result.get("raw_runs", []):
        if run.get("status") != "accepted":
            continue
        for row in run.get("observations", []):
            CHECKER.require(row.get("transition_force_checksum", 0) > 0,
                            "causal transition was not forced")
            CHECKER.require(isinstance(row.get("source_register_length"), int),
                            "source state was not observed")
            CHECKER.require(isinstance(row.get("target_register_length"), int),
                            "produced successor was not observed")
            CHECKER.require(
                row["target_register_length"] ==
                row["source_register_length"] + 1,
                "produced successor did not execute exactly one live step")


def self_test(protocol: dict[str, Any]) -> None:
    # Retain every v11 structural/protocol mutation, then attack each causal
    # addition independently.  The legacy function prints its own label, so
    # reproduce its five mutations here rather than reporting v11 as v12.
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
    for field in ("source_consumed_by_action", "effective_register_progress",
                  "action_consumed_by_effect",
                  "effect_consumed_by_successor",
                  "trace_continues_from_installed_successor",
                  "v11_remains_historical_negative"):
        changed = copy.deepcopy(protocol)
        changed["causal_transition_property"][field] = False
        mutations.append((f"causal-{field}", changed))
    for name, mutation in mutations:
        try:
            validate_protocol(mutation, allow_draft=True)
        except ValueError:
            continue
        raise ValueError(f"negative self-test survived: {name}")
    print(f"CAUSAL_COMPLETE_PROPERTY_SCALING_V12_SELFTEST_OK "
          f"mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-draft", action="store_true")
    parser.add_argument("--require-results", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(CHECKER.PROTOCOL.read_text(encoding="utf-8"))
    validate_protocol(protocol, allow_draft=arguments.allow_draft)
    if CHECKER.RESULTS.exists():
        validate_result(protocol,
                        json.loads(CHECKER.RESULTS.read_text(encoding="utf-8")))
        result_state = "present"
    else:
        CHECKER.require(not arguments.require_results,
                        "confirmatory results are absent")
        result_state = "absent"
    if arguments.self_test:
        self_test(protocol)
    else:
        print("CAUSAL_COMPLETE_PROPERTY_SCALING_V12_OK "
              f"status={protocol['status']} results={result_state}")

if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError,
            json.JSONDecodeError) as error:
        raise SystemExit(f"CAUSAL_COMPLETE_PROPERTY_SCALING_V12_ERROR: {error}")
