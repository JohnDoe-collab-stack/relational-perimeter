#!/usr/bin/env python3
"""Validate the pre-run v9 joint learned-instance protocol freeze.

This checker deliberately does not execute the confirmatory command.  It
checks that every declared input is frozen before a result exists, and that
the compiled Lean sources contain the exact joint dependencies whose future
measurement is being frozen.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any, Dict, Iterable, List


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v9"
LEARNING = EXPERIMENT / "learning-transformation-protocol.json"
COMPARISON = EXPERIMENT / "comparison-protocol.json"
SCHEMA = EXPERIMENT / "result-schema.json"
MANIFEST = EXPERIMENT / "manifest.json"
RAW_RESULT = EXPERIMENT / "comparison-results.ndjson"
RESULT_RECORD = EXPERIMENT / "result-record.json"

EXPECTED_CLASSES = [
    "extensional-current-behavior-verification",
    "fixed-network-interventional-causal-analysis",
    "pre-execution-action-shielding",
    "guaranteed-self-adaptive-system",
    "incremental-neural-verification-with-proof-reuse",
    "deployment-chain-certificate-propagation",
]
EXPECTED_TRANSFORMS = [
    "initial-to-aligned",
    "aligned-to-extended",
    "initial-to-bypass-counterfactual",
]
EXPECTED_REFERENCES = [f"R{index}" for index in range(1, 9)]
EXPECTED_PROBES = [f"P{index}" for index in range(1, 9)]
EXPECTED_CRITERIA = [f"S{index}" for index in range(1, 9)]
EXPECTED_RC = [f"RC{index}" for index in range(1, 7)]
EXPECTED_G = [f"G{index}" for index in range(1, 11)]

REQUIRED_SOURCE_MARKERS = {
    "RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean": [
        "structure LearnedConstitutiveAlignmentClosureCertificate",
        "learningDataExact : learningData = independentLearningDataSha256",
        "learningGeneratorExact : learningGenerator = independentLearningGeneratorSha256",
        "firstProductionExact : firstProduction = learnedReferenceTransitionProduction",
        "secondProduction = learnedExtendedReferenceTransitionProduction",
        "localReuseLicenses = learnedLicensedStructuralTransports",
        "licensedStructuralEntries localReuseLicenses =",
        "localReuseInstalled :",
        "firstProduction.targetState = alignedRuntime.current.state",
        "secondProduction.targetState = extendedRuntime.current.state",
        "futureSourceFromInstalledRuntime :",
        "bypassHasNoInstalledSuccessor :",
        "def learnedConstitutiveAlignmentClosure",
    ],
    "RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean": [
        "structure FrozenNeuralComparisonMaterial",
        "transportedStructuralCountExact : transportedStructuralCount = 3",
        "recomputedStructuralCountExact : recomputedStructuralCount = 10",
        "learnedReuseExact :",
        "def frozenNeuralComparisonAdapterBundle",
    ],
    "Tests/Executables/CompiledNeuralComparisonAdapters.lean": [
        "reuse_claimed\\\":true",
        "def emitExtensional",
        "def emitInterventional",
        "def emitShielding",
        "def emitSelfAdaptive",
        "def emitIncremental",
        "def emitDeployment",
    ],
    "Tests/Mechanisms/NeuralLearnedFutureConstitutiveClosureRegression.lean": [
        "learned_joint_closure_uses_frozen_learning_inputs",
        "learned_joint_closure_consumes_both_executed_productions",
        "learned_joint_closure_transport_is_source_licensed",
        "learned_joint_closure_installs_the_assembled_certificate",
        "learned_joint_closure_installs_produced_successors",
        "learned_joint_closure_candidates_share_intent_and_current_domain",
        "learned_joint_closure_discriminating_continuation_is_nonempty",
    ],
    "scripts/run-neural-joint-confirmatory-v9.py": [
        "EXPECTED_ADAPTERS = [",
        "if RAW_OUTPUT.exists() or RESULT_RECORD.exists()",
        "repository working tree is not clean",
        "rows = parse_rows(produced.stdout)",
        "raw_digest = hashlib.sha256(raw_bytes).hexdigest()",
        "with RAW_OUTPUT.open(\"xb\")",
        "with RESULT_RECORD.open(\"x\"",
    ],
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_json(path: Path) -> Dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"JSON root is not an object: {path}")
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_prefixed(values: Iterable[str], prefixes: List[str], label: str) -> None:
    actual = [str(value).split("-", 1)[0] for value in values]
    require(actual == prefixes, f"wrong {label}: {actual}")


def validate_learning(learning: Dict[str, Any]) -> None:
    require(
        learning.get("protocol_id") ==
        "constitutive-neural-learning-transformation-v9",
        "wrong learning protocol id",
    )
    require(
        learning.get("status") ==
        "frozen-before-any-new-confirmatory-production",
        "learning protocol is not frozen before production",
    )
    provenance = learning.get("provenance", {})
    require(provenance.get("external_material") is False,
            "external learning material is not excluded")
    require(bool(provenance.get("reuse_rights")), "reuse rights are missing")
    require(provenance.get("manual_weight_selection_after_observation") is False,
            "post-observation weight selection is not excluded")
    require(learning.get("randomness", {}).get("used") is False,
            "unexpected randomness")
    require(learning.get("randomness", {}).get("seeds") == [],
            "deterministic protocol must record an empty seed list")
    transforms = learning.get("transformations", [])
    require([entry.get("id") for entry in transforms] == EXPECTED_TRANSFORMS,
            "wrong learned transformation lineage")
    require(transforms[0].get("executed_production") ==
            "learnedReferenceTransitionProduction",
            "first executed production is not frozen")
    require(transforms[1].get("executed_production") ==
            "learnedExtendedReferenceTransitionProduction",
            "second executed production is not frozen")
    require("never installed" in transforms[2].get("status", ""),
            "bypass purity is not frozen")
    require(learning.get("new_confirmatory_production_present") is False,
            "learning protocol incorrectly records a new production")


def validate_comparison(comparison: Dict[str, Any]) -> None:
    require(
        comparison.get("protocol_id") ==
        "constitutive-neural-joint-capability-comparison-v9",
        "wrong comparison protocol id",
    )
    require(comparison.get("status") == "frozen-before-confirmatory-run",
            "comparison protocol is not frozen before the run")
    require(comparison.get("confirmatory_results_present") is False,
            "comparison protocol claims a result before the run")
    require(comparison.get("confirmatory_run_permitted") is False,
            "comparison run is enabled before a stable commit")
    require(comparison.get("reference_classes") == EXPECTED_CLASSES,
            "the six comparison classes changed")
    references = comparison.get("literature_references", [])
    require([entry.get("id") for entry in references] == EXPECTED_REFERENCES,
            "R1-R8 changed")
    exact_prefixed(comparison.get("discriminating_probes", []),
                   EXPECTED_PROBES, "P1-P8")
    exact_prefixed(comparison.get("success_criteria", []),
                   EXPECTED_CRITERIA, "S1-S8")
    methods = comparison.get("comparison_methods", {})
    require(set(methods) == {"relational_method", "reference_combination",
                             "full_recheck"},
            "comparison methods changed")
    shared = comparison.get("shared_material", {})
    require(shared.get("joint_certificate") ==
            "ConstitutiveSearch.NeuralAgent.learnedConstitutiveAlignmentClosure",
            "wrong joint certificate")
    require(shared.get("aligned_update") ==
            "ConstitutiveSearch.NeuralAgent.alignedUpdate",
            "wrong aligned update")
    require(shared.get("bypass_update") ==
            "ConstitutiveSearch.NeuralAgent.bypassUpdate",
            "wrong bypass update")
    require(shared.get("current_domain_cardinality") == 4,
            "wrong canonical current domain")
    require(shared.get("future_cardinality") == 1,
            "the discriminating continuation is not nonempty and exact")
    joint = comparison.get("joint_closure", {})
    require(joint.get("requirements") == EXPECTED_RC, "RC1-RC6 changed")
    require(joint.get("guarantees") == EXPECTED_G, "G1-G10 changed")
    require(joint.get("transported_structural_fragments") == 3,
            "wrong transported fragment count")
    require(joint.get("recomputed_structural_fragments") == 10,
            "wrong recomputed fragment count")
    require(joint.get("accepted_successive_updates") == 2,
            "the successive learned lineage is incomplete")
    require(joint.get("bypass_rejection") ==
            "missingConstitutiveDependency before any installed successor",
            "bypass rejection is not caused by the missing dependency")
    require(comparison.get("confirmatory_command") ==
            ["python3", "scripts/run-neural-joint-confirmatory-v9.py"],
            "confirmatory command changed")
    require(comparison.get("executed_adapter_command") ==
            ["lake", "exe", "compiled_neural_comparison_adapters"],
            "executed adapter command changed")
    require(comparison.get("output_paths_reserved") == {
        "raw": "experiments/constitutive-neural-alignment/v9/comparison-results.ndjson",
        "record": "experiments/constitutive-neural-alignment/v9/result-record.json",
    }, "reserved output paths changed")
    require(comparison.get("output_policy", {}).get("overwrite") is False,
            "confirmatory outputs may be overwritten")
    require(comparison.get("output_policy", {}).get("self_hashing") is False,
            "protocol attempts to place an output hash inside the hashed output")


def validate_schema(schema: Dict[str, Any]) -> None:
    require(schema.get("$id") ==
            "constitutive-neural-joint-capability-result-v9",
            "wrong result schema")
    rows = schema.get("properties", {}).get("rows", {})
    require(rows.get("minItems") == 6 and rows.get("maxItems") == 6,
            "schema does not require exactly six rows")
    enum = rows.get("items", {}).get("properties", {}).get(
        "adapter_id", {}).get("enum")
    require(enum == EXPECTED_CLASSES, "schema classes differ from protocol")
    required = schema.get("required", [])
    require("raw_output_sha256" in required and "output_sha256" not in required,
            "schema must hash the separate raw output without self-hashing")
    require(schema.get("properties", {}).get("raw_output_path", {}).get("const") ==
            "experiments/constitutive-neural-alignment/v9/comparison-results.ndjson",
            "schema raw output path changed")


def validate_sources() -> None:
    for relative, markers in REQUIRED_SOURCE_MARKERS.items():
        source = (ROOT / relative).read_text(encoding="utf-8")
        for marker in markers:
            require(marker in source, f"missing compiled-source marker: {relative}: {marker}")


def validate_manifest(manifest: Dict[str, Any]) -> None:
    require(manifest.get("manifest_id") ==
            "constitutive-neural-joint-capability-manifest-v9",
            "wrong manifest id")
    require(manifest.get("status") == "inputs-frozen-not-run",
            "manifest is not a pre-run input freeze")
    require(manifest.get("hash_algorithm") == "sha256",
            "wrong hash algorithm")
    require(manifest.get("result_status") == "absent-by-protocol",
            "manifest does not record result absence")
    require(manifest.get("repository_commit_status") ==
            "required-before-confirmatory-run",
            "stable repository commit is not required")
    files = manifest.get("files")
    require(isinstance(files, dict) and files, "manifest file map is empty")
    required = set(REQUIRED_SOURCE_MARKERS) | {
        "experiments/constitutive-neural-alignment/v9/learning-transformation-protocol.json",
        "experiments/constitutive-neural-alignment/v9/comparison-protocol.json",
        "experiments/constitutive-neural-alignment/v9/result-schema.json",
        "experiments/constitutive-neural-alignment/v9/README.md",
        "scripts/check-neural-joint-protocol-v9.py",
        "scripts/train-independent-neural-artifact.py",
        "experiments/constitutive-neural-alignment/v1/training-data.json",
        "experiments/constitutive-neural-alignment/v1/comparison-protocol.json",
        "experiments/constitutive-neural-alignment/v1/learned-artifact.json",
        "experiments/constitutive-neural-alignment/v1/manifest.json",
        "RelationalPerimeter/Agents/Neural/IndependentLearnedArtifact.lean",
        "RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean",
        "RelationalPerimeter/Agents/Neural/LearnedUpdateSeparation.lean",
        "RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean",
        "RelationalPerimeter/Agents/Neural/AutonomousCheckerClosure.lean",
    }
    require(set(files) == required,
            "manifest file set differs from the complete frozen input set")
    for relative, expected in files.items():
        path = ROOT / relative
        require(path.is_file(), f"frozen input is missing: {relative}")
        require(digest(path) == expected, f"input hash mismatch: {relative}")


def validate_bundle(learning: Dict[str, Any], comparison: Dict[str, Any],
                    schema: Dict[str, Any], manifest: Dict[str, Any]) -> None:
    validate_learning(learning)
    validate_comparison(comparison)
    validate_schema(schema)
    validate_sources()
    validate_manifest(manifest)
    require(comparison.get("shared_material", {}).get("learning_protocol") ==
            learning.get("protocol_id"),
            "comparison and learning freezes are disconnected")
    require(not RAW_RESULT.exists(),
            "raw confirmatory result exists before the frozen run")
    require(not RESULT_RECORD.exists(),
            "post-run result record exists before the frozen run")


def validate() -> None:
    validate_bundle(load_json(LEARNING), load_json(COMPARISON),
                    load_json(SCHEMA), load_json(MANIFEST))


def expect_failure(action, label: str) -> None:
    try:
        action()
    except ValueError:
        return
    raise ValueError(f"self-test mutation survived: {label}")


def self_test() -> None:
    learning = load_json(LEARNING)
    comparison = load_json(COMPARISON)
    schema = load_json(SCHEMA)
    manifest = load_json(MANIFEST)
    validate_bundle(learning, comparison, schema, manifest)

    changed = copy.deepcopy(learning)
    changed["provenance"]["manual_weight_selection_after_observation"] = True
    expect_failure(lambda: validate_learning(changed), "manual learned weights")

    changed = copy.deepcopy(learning)
    changed["transformations"][2]["status"] = "installed"
    expect_failure(lambda: validate_learning(changed), "installed bypass")

    changed = copy.deepcopy(comparison)
    changed["reference_classes"] = changed["reference_classes"][:-1]
    expect_failure(lambda: validate_comparison(changed), "missing comparison class")

    changed = copy.deepcopy(comparison)
    changed["joint_closure"]["transported_structural_fragments"] = 0
    expect_failure(lambda: validate_comparison(changed), "erased local reuse")

    changed = copy.deepcopy(comparison)
    changed["shared_material"]["future_cardinality"] = 0
    expect_failure(lambda: validate_comparison(changed), "empty continuation")

    changed = copy.deepcopy(comparison)
    changed["confirmatory_run_permitted"] = True
    expect_failure(lambda: validate_comparison(changed), "premature run permission")

    changed = copy.deepcopy(schema)
    changed["properties"]["rows"]["minItems"] = 1
    expect_failure(lambda: validate_schema(changed), "partial output schema")

    changed = copy.deepcopy(manifest)
    first = next(iter(changed["files"]))
    changed["files"][first] = "0" * 64
    expect_failure(lambda: validate_manifest(changed), "changed frozen input")

    print("NEURAL_JOINT_PROTOCOL_V9_SELFTEST_OK mutations=8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    if arguments.self_test:
        self_test()
    else:
        validate()
        print("NEURAL_JOINT_PROTOCOL_V9_OK files=20 classes=6 "
              "references=8 probes=8 criteria=8 results=false")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"NEURAL_JOINT_PROTOCOL_V9_ERROR: {error}")
