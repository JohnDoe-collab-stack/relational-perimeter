#!/usr/bin/env python3
"""Validate the frozen, pre-run v10 complete capability comparison."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Dict, List


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v10"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
TRANSLATIONS = EXPERIMENT / "translation-ledger.json"
CORRESPONDENCE = EXPERIMENT / "method-correspondence.json"
COMPARATIVE_SCOPE = EXPERIMENT / "COMPARATIVE_SCOPE.md"
MATRIX = EXPERIMENT / "capability-matrix.json"
ABLATIONS = EXPERIMENT / "authorized-ablations.json"
CRITERIA = EXPERIMENT / "success-criteria.json"
SCHEMA = EXPERIMENT / "result-schema.json"
MANIFEST = EXPERIMENT / "manifest.json"
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
PROBES = [f"P{i}" for i in range(1, 8)]
CRITERION_IDS = ["S1", "S2", "S3", "S4", "S5", "S7", "S8"]
STATUSES = {
    "certified", "observed", "not-certified", "out-of-interface",
    "adapter-unavailable",
}
EXPECTED_TRANSLATIONS = [2, 2, 2, 3, 4, 3, 4, 6, 4]

SOURCE_MARKERS = {
    "RelationalPerimeter/Agents/Neural/CompleteCapabilityComparison.lean": [
        "structure FrozenCompleteComparisonMaterial",
        "def runRelationalExecutionComparison",
        "def runReferenceCombination",
        "def runIndependentFullRecheckComparison",
        "acceptedWithoutIncrementalOracle",
        "def methodTranslationLedgers",
        "def frozenCompleteComparisonBundle",
    ],
    "Tests/Executables/CompiledCompleteNeuralComparison.lean": [
        "def emitClassRows",
        "def emitRelationalRow",
        "def emitReferenceCombinationRow",
        "def emitFullRecheckRow",
    ],
    "Tests/Mechanisms/NeuralCompleteCapabilityComparisonRegression.lean": [
        "methodTranslationLedgers.length = 9",
        "referenceCombination.alignedPreEffectDecision",
        "fullRecheck.bypassDecision",
    ],
    "scripts/run-neural-complete-comparison-v10.py": [
        "EXPECTED_METHODS = [",
        "repository working tree is not clean",
        "expected exactly nine nonempty NDJSON rows",
        "with RAW_OUTPUT.open(\"xb\")",
        "with RESULT_RECORD.open(\"x\"",
    ],
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load(path: Path) -> Dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"JSON root is not an object: {path}")
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_protocol(protocol: Dict[str, Any]) -> None:
    require(protocol.get("protocol_id") ==
            "constitutive-neural-complete-capability-comparison-v10",
            "wrong protocol id")
    require(protocol.get("status") == "frozen-before-confirmatory-run",
            "protocol is not frozen")
    require(protocol.get("confirmatory_results_present") is False,
            "protocol claims a result before execution")
    require(protocol.get("confirmatory_run_permitted") is False,
            "protocol permits execution before a stable commit")
    require(protocol.get("methods") == METHODS, "method order changed")
    require(protocol.get("covered_probes") == PROBES, "P1-P7 changed")
    require(protocol.get("covered_criteria") == CRITERION_IDS,
            "S1-S5/S7-S8 changed")
    require(protocol.get("executed_command") ==
            ["lake", "exe", "compiled_complete_neural_comparison"],
            "compiled command changed")
    require(protocol.get("output_policy", {}).get("rows") == 9,
            "protocol does not retain nine rows")
    require(protocol.get("output_policy", {}).get("overwrite") is False,
            "results may be overwritten")


def validate_translations(ledger: Dict[str, Any]) -> None:
    rows = ledger.get("methods")
    require(isinstance(rows, list) and len(rows) == 9,
            "translation ledger must have nine rows")
    require([row.get("method_id") for row in rows] == METHODS,
            "translation method order changed")
    require([row.get("translation_count") for row in rows] ==
            EXPECTED_TRANSLATIONS, "translation counts changed")
    for row in rows:
        require(row.get("translation_count") == len(row.get("inputs", [])),
                f"translation count mismatch: {row.get('method_id')}")


def validate_correspondence(correspondence: Dict[str, Any]) -> None:
    require("repository-local typed adapter" in
            correspondence.get("scope_rule", ""),
            "local-adapter scope rule is missing")
    require(bool(correspondence.get("shared_arithmetic")),
            "shared arithmetic is missing")
    require(bool(correspondence.get("shared_version_boundary")),
            "shared version boundary is missing")
    rows = correspondence.get("methods")
    require(isinstance(rows, list) and len(rows) == 9,
            "method correspondence must have nine rows")
    require([row.get("method_id") for row in rows] == METHODS,
            "correspondence method order changed")
    require([row.get("translation_count") for row in rows] ==
            EXPECTED_TRANSLATIONS,
            "correspondence translation counts changed")
    for index, row in enumerate(rows):
        for key in ["domain", "property", "trust_boundary",
                    "external_class_equivalence"]:
            require(bool(row.get(key)),
                    f"missing {key} correspondence: {row.get('method_id')}")
        expected = "not-certified" if index < 6 else "local-exact"
        require(row.get("external_class_equivalence") == expected,
                f"external-class scope overclaimed: {row.get('method_id')}")


def validate_matrix(matrix: Dict[str, Any]) -> None:
    require(set(matrix.get("status_vocabulary", [])) == STATUSES,
            "matrix status vocabulary changed")
    cells = matrix.get("cells")
    require(isinstance(cells, list) and len(cells) == 63,
            "matrix must contain exactly 9 x 7 cells")
    keys = [(cell.get("probe"), cell.get("method")) for cell in cells]
    expected = [(probe, method) for probe in PROBES for method in METHODS]
    require(keys == expected, "matrix cells are missing, duplicated or reordered")
    for cell in cells:
        require(cell.get("status") in STATUSES,
                f"unknown matrix status: {cell}")
        require(bool(cell.get("evidence")), f"missing evidence: {cell}")
    extensional_p1 = cells[0]
    require(extensional_p1.get("status") == "observed",
            "current-table equality was promoted to certification")
    for cell in cells[-9:]:
        require(cell.get("status") == "not-certified",
                "P7 was claimed before the reserved execution")


def validate_ablations(ablations: Dict[str, Any]) -> None:
    rows = ablations.get("ablations")
    require(isinstance(rows, list) and len(rows) == 7,
            "wrong authorized ablation count")
    require([row.get("id") for row in rows] == [f"A{i}-" + suffix for i, suffix in [
        (1, "missing-requirement-role"),
        (2, "foreign-effect"),
        (3, "wrong-version-fragments"),
        (4, "recover-forgotten-origin"),
        (5, "incremental-oracle-in-full-recheck"),
        (6, "substitute-second-production"),
        (7, "reconstruct-effect"),
    ]], "ablation identities changed")
    for row in rows:
        require(row.get("expected") == "rejected", "unsafe ablation expectation")
        fixture = ROOT / str(row.get("fixture"))
        require(fixture.is_file(), f"ablation fixture missing: {fixture}")


def validate_criteria(criteria: Dict[str, Any]) -> None:
    rows = criteria.get("criteria")
    require(isinstance(rows, list) and
            [row.get("id") for row in rows] == CRITERION_IDS,
            "criteria set changed")
    for row in rows:
        require(row.get("status") in STATUSES, f"invalid criterion status: {row}")
    by_id = {row["id"]: row for row in rows}
    for identifier in CRITERION_IDS:
        require(by_id[identifier]["status"] == "not-certified",
                f"{identifier} was overclaimed before execution/audit")


def validate_schema(schema: Dict[str, Any]) -> None:
    require(schema.get("$id") ==
            "constitutive-neural-complete-capability-result-v10",
            "wrong result schema id")
    rows = schema.get("properties", {}).get("rows", {})
    require(rows.get("minItems") == 9 and rows.get("maxItems") == 9,
            "schema does not require nine rows")
    required = schema.get("required", [])
    require("raw_output_sha256" in required, "raw output hash is not required")


def validate_sources() -> None:
    for relative, markers in SOURCE_MARKERS.items():
        source = (ROOT / relative).read_text(encoding="utf-8")
        for marker in markers:
            require(marker in source, f"missing source marker: {relative}: {marker}")
    complete = (ROOT / "RelationalPerimeter/Agents/Neural/CompleteCapabilityComparison.lean").read_text(encoding="utf-8")
    require("learnedConstitutiveAlignmentClosure" not in complete,
            "comparison receives the final constitutive closure as an oracle")
    scope = COMPARATIVE_SCOPE.read_text(encoding="utf-8")
    normalized_scope = " ".join(scope.split())
    for marker in [
        "No unique discriminatory advantage is currently certified for P1",
        "may not declare a residual scientific gain",
        "never becomes an impossibility statement",
        "bookkeeping, not runtime cost",
    ]:
        require(marker in normalized_scope,
                f"comparative-scope limitation is missing: {marker}")


def validate_manifest(manifest: Dict[str, Any]) -> None:
    require(manifest.get("manifest_id") ==
            "constitutive-neural-complete-capability-manifest-v10",
            "wrong manifest id")
    require(manifest.get("status") == "inputs-frozen-not-run",
            "manifest is not pre-run")
    require(manifest.get("repository_commit_status") ==
            "required-before-confirmatory-run",
            "stable commit is not required")
    files = manifest.get("files")
    require(isinstance(files, dict) and len(files) >= 15,
            "manifest input set is incomplete")
    for relative, expected in files.items():
        path = ROOT / relative
        require(path.is_file(), f"frozen input missing: {relative}")
        require(digest(path) == expected, f"input hash mismatch: {relative}")


def validate_record_if_present(allow_results: bool) -> None:
    present = RAW.exists() or RECORD.exists()
    if not present:
        return
    require(allow_results, "reserved result exists before the frozen run")
    require(RAW.is_file() and RECORD.is_file(),
            "raw output and result record must appear together")
    lines = RAW.read_text(encoding="utf-8").splitlines()
    require(len(lines) == 9, "stored raw output does not have nine rows")
    rows = [json.loads(line) for line in lines]
    require([row.get("method_id") for row in rows] == METHODS,
            "stored method order changed")
    record = load(RECORD)
    require(record.get("protocol_id") ==
            "constitutive-neural-complete-capability-comparison-v10",
            "stored record has wrong protocol")
    require(record.get("rows") == rows, "stored record rows differ from raw output")
    require(record.get("raw_output_sha256") == digest(RAW),
            "stored raw output hash differs")


def validate_all(allow_results: bool = False) -> None:
    validate_protocol(load(PROTOCOL))
    validate_translations(load(TRANSLATIONS))
    validate_correspondence(load(CORRESPONDENCE))
    validate_matrix(load(MATRIX))
    validate_ablations(load(ABLATIONS))
    validate_criteria(load(CRITERIA))
    validate_schema(load(SCHEMA))
    validate_sources()
    validate_manifest(load(MANIFEST))
    validate_record_if_present(allow_results)


def expect_failure(action, label: str) -> None:
    try:
        action()
    except ValueError:
        return
    raise ValueError(f"self-test mutation survived: {label}")


def self_test(allow_results: bool = False) -> None:
    validate_all(allow_results)
    protocol = load(PROTOCOL)
    changed = copy.deepcopy(protocol)
    changed["methods"] = changed["methods"][:-1]
    expect_failure(lambda: validate_protocol(changed), "missing method")
    changed = copy.deepcopy(protocol)
    changed["confirmatory_results_present"] = True
    expect_failure(lambda: validate_protocol(changed), "premature result")
    matrix = load(MATRIX)
    changed_matrix = copy.deepcopy(matrix)
    changed_matrix["cells"][0]["status"] = "certified"
    expect_failure(lambda: validate_matrix(changed_matrix), "extensional overclaim")
    changed_matrix = copy.deepcopy(matrix)
    changed_matrix["cells"].pop()
    expect_failure(lambda: validate_matrix(changed_matrix), "missing matrix cell")
    translations = load(TRANSLATIONS)
    changed_translations = copy.deepcopy(translations)
    changed_translations["methods"][0]["translation_count"] = 0
    expect_failure(lambda: validate_translations(changed_translations),
                   "erased translation")
    correspondence = load(CORRESPONDENCE)
    changed_correspondence = copy.deepcopy(correspondence)
    changed_correspondence["methods"][0]["external_class_equivalence"] = \
        "local-exact"
    expect_failure(lambda: validate_correspondence(changed_correspondence),
                   "external-class overclaim")
    criteria = load(CRITERIA)
    changed_criteria = copy.deepcopy(criteria)
    changed_criteria["criteria"][0]["status"] = "certified"
    expect_failure(lambda: validate_criteria(changed_criteria),
                   "premature corpus certification")
    print("NEURAL_COMPLETE_COMPARISON_V10_SELFTEST_OK mutations=7")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--allow-results", action="store_true")
    arguments = parser.parse_args()
    if arguments.self_test:
        self_test(arguments.allow_results)
    else:
        validate_all(arguments.allow_results)
        print("NEURAL_COMPLETE_COMPARISON_V10_OK methods=9 cells=63 "
              f"ablations=7 criteria=7 results={RAW.exists()}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"NEURAL_COMPLETE_COMPARISON_V10_ERROR: {error}")

