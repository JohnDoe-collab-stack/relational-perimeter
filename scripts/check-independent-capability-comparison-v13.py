#!/usr/bin/env python3
"""Validate the v13 oracle-independent comparison protocol and evidence."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v13"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
LEDGER = EXPERIMENT / "evidence-ledger.json"
SCHEMA = EXPERIMENT / "result-schema.json"
MATRIX = EXPERIMENT / "capability-matrix.json"
CRITERIA = EXPERIMENT / "success-criteria.json"
RAW = EXPERIMENT / "comparison-results.ndjson"
RECORD = EXPERIMENT / "result-record.json"

METHODS = [
    "extensional-current-behavior-verification",
    "fixed-network-interventional-causal-analysis",
    "pre-execution-action-shielding",
    "guaranteed-self-adaptive-system",
    "incremental-neural-verification-with-proof-reuse",
    "deployment-chain-certificate-propagation",
    "relational-execution-comparison",
    "explicit-reference-combination",
    "independent-complete-recheck",
]
TRANSLATIONS = [2, 2, 2, 3, 4, 3, 4, 6, 4]
FIELDS = {
    METHODS[0]: {"current_cases", "tables_equal"},
    METHODS[1]: {"aligned_authorization_dependency", "bypass_authorization_dependency"},
    METHODS[2]: {"aligned_decision", "bypass_decision"},
    METHODS[3]: {"aligned_submission", "bypass_submission"},
    METHODS[4]: {"aligned_submission", "bypass_submission", "transported_structural_fragments", "recomputed_structural_fragments"},
    METHODS[5]: {"accepted_transitions", "bypass_submission"},
    METHODS[6]: {"current_tables_equal", "future_requests", "future_outputs_different", "aligned_future_satisfies", "bypass_future_satisfies"},
    METHODS[7]: {"current_tables_equal", "aligned_authorization_dependency", "bypass_authorization_dependency", "aligned_mutation_decision", "bypass_mutation_decision", "aligned_future_satisfies", "bypass_future_satisfies", "aligned_decision", "bypass_decision"},
    METHODS[8]: {"aligned_decision", "bypass_decision"},
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"JSON object required: {path}")
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_protocol(protocol: dict[str, Any], allow_draft: bool) -> None:
    require(protocol.get("protocol_id") ==
            "constitutive-neural-oracle-independent-capability-comparison-v13",
            "wrong protocol id")
    status = protocol.get("status")
    require(status in {"draft-awaiting-stable-source-commit",
                       "frozen-before-confirmatory-run"}, "invalid status")
    require(allow_draft or status == "frozen-before-confirmatory-run",
            "protocol remains a draft")
    require(protocol.get("confirmatory_results_present") is False,
            "protocol claims results before the run")
    require(protocol.get("confirmatory_run_permitted") is False,
            "protocol permits an unfrozen run")
    require(protocol.get("methods") == METHODS, "method set or order changed")
    require(protocol.get("translation_counts") == TRANSLATIONS,
            "translation counts changed")
    require(protocol.get("covered_probes") == [f"P{i}" for i in range(1, 8)],
            "P1-P7 coverage changed")
    require(protocol.get("covered_criteria") ==
            ["S1", "S2", "S3", "S4", "S5", "S7", "S8"],
            "S1-S5/S7-S8 coverage changed")
    delegated = protocol.get("delegated_without_reclassification", {})
    require(set(delegated) == {"P8", "S6"}, "P8/S6 delegation changed")
    forbidden = protocol.get("corrections", {}).get("forbidden_reference_inputs")
    require(isinstance(forbidden, list) and len(forbidden) == 5,
            "reference-oracle exclusion is incomplete")
    require(protocol.get("executed_command") ==
            ["lake", "exe", "compiled_independent_complete_neural_comparison"],
            "compiled command changed")
    require(protocol.get("output_policy", {}).get("rows") == 9,
            "nine output rows are not required")
    require(protocol.get("output_policy", {}).get("overwrite") is False,
            "output overwrite is permitted")
    for relative, expected in protocol.get("historical_v10_preserved", {}).items():
        path = ROOT / relative
        require(path.is_file(), f"historical v10 evidence missing: {relative}")
        require(digest(path) == expected, f"historical v10 evidence changed: {relative}")
    if status == "frozen-before-confirmatory-run":
        require(len(protocol.get("frozen_source_commit", "")) == 40,
                "frozen source commit is missing")
        hashes = protocol.get("source_sha256")
        require(isinstance(hashes, dict) and hashes,
                "frozen source hashes are missing")
        for relative, expected in hashes.items():
            path = ROOT / relative
            require(path.is_file(), f"frozen source missing: {relative}")
            require(digest(path) == expected, f"frozen source changed: {relative}")


def validate_ledger(ledger: dict[str, Any]) -> None:
    require(ledger.get("ledger_id") ==
            "constitutive-neural-oracle-independent-evidence-v13",
            "wrong evidence ledger")
    rows = ledger.get("emitted_fields")
    require(isinstance(rows, dict) and list(rows) == METHODS,
            "evidence methods are missing or reordered")
    for method in METHODS:
        require(set(rows[method]) == FIELDS[method],
                f"field-to-producer mapping mismatch: {method}")
        require(all(bool(value) for value in rows[method].values()),
                f"empty producer mapping: {method}")
    proofs = ledger.get("proof_only_evidence")
    require(isinstance(proofs, list) and len(proofs) == 7,
            "proof-only evidence set changed")
    emitted_names = {field for row in rows.values() for field in row}
    for proof in proofs:
        require(bool(proof.get("property")) and bool(proof.get("declaration")),
                "proof-only evidence is incomplete")
        require(proof.get("property") not in emitted_names,
                "proof-only property is masquerading as an emitted field")


def validate_schema(schema: dict[str, Any]) -> None:
    require(schema.get("$id") ==
            "constitutive-neural-oracle-independent-result-v13",
            "wrong result schema")
    rows = schema.get("properties", {}).get("rows", {})
    require(rows.get("minItems") == 9 and rows.get("maxItems") == 9,
            "schema does not require nine rows")
    require("raw_output_sha256" in schema.get("required", []),
            "raw hash is not required")


def validate_matrix(matrix: dict[str, Any]) -> None:
    vocabulary = {"certified", "observed", "not-certified",
                  "out-of-interface", "adapter-unavailable"}
    require(set(matrix.get("status_vocabulary", [])) == vocabulary,
            "matrix status vocabulary changed")
    cells = matrix.get("cells")
    require(isinstance(cells, list) and len(cells) == 63,
            "matrix must contain exactly 9 x 7 cells")
    expected = [(f"P{probe}", method)
                for probe in range(1, 8) for method in METHODS]
    require([(cell.get("probe"), cell.get("method")) for cell in cells] == expected,
            "matrix cells are missing, duplicated or reordered")
    for cell in cells:
        require(cell.get("status") in vocabulary, f"invalid matrix cell: {cell}")
        require(bool(cell.get("evidence")), f"missing matrix evidence: {cell}")
    reference_cells = [cell for cell in cells
                       if cell.get("method") == "explicit-reference-combination"]
    require(all("runReferenceCombination" not in cell["evidence"]
                for cell in reference_cells),
            "matrix still cites the oracle-dependent v10 reference producer")
    require(all(cell.get("status") == "not-certified" for cell in cells[-9:]),
            "P7 was promoted before the confirmatory run")


def validate_criteria(criteria: dict[str, Any]) -> None:
    expected = ["S1", "S2", "S3", "S4", "S5", "S7", "S8"]
    rows = criteria.get("criteria")
    require(isinstance(rows, list) and
            [row.get("id") for row in rows] == expected,
            "success criteria set changed")
    require(all(row.get("status") == "not-certified" for row in rows),
            "a success criterion was promoted before the run and audits")
    require(bool(criteria.get("conclusion_rule")), "conclusion rule is absent")


def validate_sources() -> None:
    implementation = (ROOT / "RelationalPerimeter/Agents/Neural/IndependentCapabilityComparison.lean").read_text(encoding="utf-8")
    emitter = (ROOT / "Tests/Executables/CompiledIndependentCompleteNeuralComparison.lean").read_text(encoding="utf-8")
    for marker in ["def independentReferenceDecision",
                   "def computeIndependentReferenceObservation",
                   "def runIndependentReferenceCombination",
                   "def independentCompleteComparisonBundle"]:
        require(marker in implementation, f"implementation marker missing: {marker}")
    require("learnedAlignedRuntimeSubmissionDecision" not in implementation,
            "independent module names the historical runtime oracle")
    require("learnedBypassRuntimeSubmissionDecision" not in implementation,
            "independent module names the historical runtime oracle")
    for marker in ["def emitClassRows", "def emitRelationalRow",
                   "def emitReferenceCombinationRow", "def emitFullRecheckRow"]:
        require(marker in emitter, f"emitter marker missing: {marker}")


def parse_rows(raw: str) -> list[dict[str, Any]]:
    lines = raw.splitlines()
    require(len(lines) == 9 and all(line.strip() for line in lines),
            "exactly nine nonempty rows are required")
    rows = [json.loads(line) for line in lines]
    for index, (row, method, translations) in enumerate(
            zip(rows, METHODS, TRANSLATIONS, strict=True)):
        require(row.get("method_id") == method,
                f"wrong method at row {index + 1}")
        require(row.get("translation_count") == translations,
                f"wrong translation count at row {index + 1}")
        require(set(row) == {"method_id", "translation_count"} | FIELDS[method],
                f"unmapped or missing emitted field: {method}")
    return rows


def validate_results(protocol: dict[str, Any], allow_results: bool) -> None:
    present = RAW.exists() or RECORD.exists()
    if not present:
        return
    require(allow_results, "reserved result exists without explicit validation")
    require(protocol.get("status") == "frozen-before-confirmatory-run",
            "result exists for an unfrozen protocol")
    require(RAW.is_file() and RECORD.is_file(), "raw and record must coexist")
    rows = parse_rows(RAW.read_text(encoding="utf-8"))
    record = load(RECORD)
    require(record.get("protocol_id") == protocol.get("protocol_id"),
            "result protocol differs")
    require(record.get("rows") == rows, "record differs from raw rows")
    require(record.get("raw_output_sha256") == digest(RAW),
            "raw result hash differs")


def validate_all(allow_draft: bool, allow_results: bool) -> None:
    protocol = load(PROTOCOL)
    validate_protocol(protocol, allow_draft)
    validate_ledger(load(LEDGER))
    validate_schema(load(SCHEMA))
    validate_matrix(load(MATRIX))
    validate_criteria(load(CRITERIA))
    validate_sources()
    validate_results(protocol, allow_results)


def expect_failure(action, name: str) -> None:
    try:
        action()
    except ValueError:
        return
    raise ValueError(f"negative mutation survived: {name}")


def self_test() -> None:
    protocol = load(PROTOCOL)
    ledger = load(LEDGER)
    changed = copy.deepcopy(protocol)
    changed["corrections"]["forbidden_reference_inputs"].pop()
    expect_failure(lambda: validate_protocol(changed, True), "erased oracle exclusion")
    changed = copy.deepcopy(protocol)
    changed["methods"].pop()
    expect_failure(lambda: validate_protocol(changed, True), "missing method")
    changed = copy.deepcopy(protocol)
    historical = next(iter(changed["historical_v10_preserved"]))
    changed["historical_v10_preserved"][historical] = "0" * 64
    expect_failure(lambda: validate_protocol(changed, True), "rewritten v10")
    changed_ledger = copy.deepcopy(ledger)
    changed_ledger["emitted_fields"][METHODS[7]].pop("aligned_decision")
    expect_failure(lambda: validate_ledger(changed_ledger), "unmapped result")
    changed_ledger = copy.deepcopy(ledger)
    changed_ledger["proof_only_evidence"].pop()
    expect_failure(lambda: validate_ledger(changed_ledger), "erased proof distinction")
    matrix = load(MATRIX)
    changed_matrix = copy.deepcopy(matrix)
    changed_matrix["cells"][-1]["status"] = "certified"
    expect_failure(lambda: validate_matrix(changed_matrix), "premature P7 promotion")
    criteria = load(CRITERIA)
    changed_criteria = copy.deepcopy(criteria)
    changed_criteria["criteria"][0]["status"] = "certified"
    expect_failure(lambda: validate_criteria(changed_criteria), "premature criterion promotion")
    print("INDEPENDENT_CAPABILITY_COMPARISON_V13_SELFTEST_OK mutations=7")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-draft", action="store_true")
    parser.add_argument("--allow-results", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    validate_all(arguments.allow_draft, arguments.allow_results)
    if arguments.self_test:
        self_test()
    else:
        protocol = load(PROTOCOL)
        print("INDEPENDENT_CAPABILITY_COMPARISON_V13_OK "
              f"status={protocol['status']} results={RAW.exists()}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError,
            json.JSONDecodeError) as error:
        raise SystemExit(f"INDEPENDENT_CAPABILITY_COMPARISON_V13_ERROR: {error}")
