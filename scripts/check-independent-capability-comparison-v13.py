#!/usr/bin/env python3
"""Validate v13 scope, evidence, transitive freeze and immutable results."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Callable

from independent_capability_snapshot_v13 import (
    ROOT, canonical_digest, digest, git, lean_import_closure, material_paths,
    validate_snapshot, working_reader,
)


EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v13"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
LEDGER = EXPERIMENT / "evidence-ledger.json"
SCHEMA = EXPERIMENT / "result-schema.json"
MATRIX = EXPERIMENT / "capability-matrix.json"
CRITERIA = EXPERIMENT / "success-criteria.json"
PROBES = EXPERIMENT / "probe-specification.json"
ABLATIONS = EXPERIMENT / "authorized-ablations.json"
SNAPSHOT = EXPERIMENT / "frozen-snapshot.json"
RAW = EXPERIMENT / "comparison-results.ndjson"
RECORD = EXPERIMENT / "result-record.json"
ABLATION_RESULTS = EXPERIMENT / "ablation-results.json"
REGISTRY = ROOT / "scripts/expected-failures.tsv"

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
    METHODS[1]: {"aligned_authorization_dependency", "bypass_authorization_dependency", "p2_canonical_decoder_action", "p2_admissible_modified_decoder_action", "p2_forbidden_modified_decoder_action", "p2_admissible_empty_output_changed", "p2_forbidden_proposals_different", "p2_local_recheck_agree"},
    METHODS[2]: {"aligned_decision", "bypass_decision"},
    METHODS[3]: {"aligned_submission", "bypass_submission", "p5_accepted_contract_change", "p5_rejected_contract_change"},
    METHODS[4]: {"aligned_submission", "bypass_submission", "transported_structural_fragments", "recomputed_structural_fragments", "p6_successive_decision", "p6_successive_transported_structural_fragments", "p6_successive_recomputed_structural_fragments", "p2_canonical_consumer", "p2_admissible_consumer", "p2_forbidden_consumer", "p3_allowed_contract_transition", "p3_rejected_contract_transition", "p5_accepted_contract_change", "p5_rejected_contract_change"},
    METHODS[5]: {"accepted_transitions", "bypass_submission"},
    METHODS[6]: {"current_tables_equal", "future_requests", "future_outputs_different", "aligned_future_satisfies", "bypass_future_satisfies", "p4_separator_nonempty", "p4_incorrect_forgetting_fff_collapses", "p4_separator_reveals_required_distinction"},
    METHODS[7]: {"current_tables_equal", "aligned_authorization_dependency", "bypass_authorization_dependency", "aligned_mutation_decision", "bypass_mutation_decision", "aligned_future_satisfies", "bypass_future_satisfies", "aligned_decision", "bypass_decision"},
    METHODS[8]: {"aligned_decision", "bypass_decision", "p2_canonical_consumer", "p2_admissible_consumer", "p2_forbidden_consumer", "p3_allowed_contract_transition", "p3_rejected_contract_transition", "p5_accepted_contract_change", "p5_rejected_contract_change", "p6_successive_decision"},
}
VOCABULARY = {"certified", "observed", "not-certified",
              "out-of-interface", "adapter-unavailable"}
NAMESPACE = "ConstitutiveSearch.NeuralAgent."
COMPILED_NAMESPACE = NAMESPACE + "CompiledIndependentCompleteComparison."

# Exact scientific wiring.  This is intentionally redundant with the ledger:
# changing a label in the JSON cannot retarget a cell to a different producer
# or proof without changing and reviewing this executable gate as well.
EVIDENCE_CONTRACTS = {
    "P1-extensional-observed": (
        "P1", METHODS[0],
        [COMPILED_NAMESPACE + "emitClassRows"], [],
        ["current_cases", "tables_equal"]),
    "P1-fixed-network-certified": (
        "P1", METHODS[1], [NAMESPACE + "runFixedNetworkInterventionalAdapter"],
        [NAMESPACE + "FixedNetworkInterventionalAdapterOutput"],
        ["aligned_authorization_dependency", "bypass_authorization_dependency"]),
    "P1-shield-certified": (
        "P1", METHODS[2], [NAMESPACE + "runPreExecutionActionShieldAdapter"],
        [NAMESPACE + "PreExecutionActionShieldAdapterOutput"],
        ["aligned_decision", "bypass_decision"]),
    "P1-self-adaptive-certified": (
        "P1", METHODS[3], [NAMESPACE + "observeRuntimeSubmission"],
        [NAMESPACE + "GuaranteedSelfAdaptiveAdapterOutput"],
        ["aligned_submission", "bypass_submission"]),
    "P1-incremental-certified": (
        "P1", METHODS[4], [NAMESPACE + "observeGenericIncremental"],
        [NAMESPACE + "IncrementalProofReuseAdapterOutput"],
        ["aligned_submission", "bypass_submission"]),
    "P1-deployment-certified": (
        "P1", METHODS[5], [NAMESPACE + "runDeploymentChainPropagationAdapter"],
        [NAMESPACE + "DeploymentChainPropagationAdapterOutput"],
        ["accepted_transitions", "bypass_submission"]),
    "P1-relational-certified": (
        "P1", METHODS[6], [NAMESPACE + "runRelationalExecutionComparison"],
        [NAMESPACE + "RelationalExecutionComparisonOutput"],
        ["future_outputs_different", "aligned_future_satisfies",
         "bypass_future_satisfies"]),
    "P1-reference-certified": (
        "P1", METHODS[7], [NAMESPACE + "runIndependentReferenceCombination"],
        [NAMESPACE + "IndependentReferenceCombinationOutput"],
        ["aligned_decision", "bypass_decision"]),
    "P1-full-certified": (
        "P1", METHODS[8], [NAMESPACE + "runIndependentFullRecheckComparison"],
        [NAMESPACE + "IndependentFullRecheckComparisonOutput"],
        ["aligned_decision", "bypass_decision"]),
    "P2-fixed-network-exact-certified": (
        "P2", METHODS[1],
        [NAMESPACE + "checkLearnedP2Path", NAMESPACE + "recheckLearnedP2Path"],
        [NAMESPACE + "learnedP2AdmissibleDecoderChanged",
         NAMESPACE + "learnedP2AdmissiblePathAccepted",
         NAMESPACE + "checkLearnedP2AdmissibleFragment_exact",
         NAMESPACE + "learnedP2AdmissibleRecheckAccepted",
         NAMESPACE + "learnedP2ModifiedPathRejected",
         NAMESPACE + "learnedP2ModifiedRecheckRejected"],
        ["p2_canonical_decoder_action", "p2_admissible_modified_decoder_action",
         "p2_forbidden_modified_decoder_action",
         "p2_admissible_empty_output_changed",
         "p2_forbidden_proposals_different", "p2_local_recheck_agree"]),
    "P2-incremental-exact-certified": (
        "P2", METHODS[4], [NAMESPACE + "observeLearnedP2Incremental"],
        [NAMESPACE + "learnedP2CanonicalIncrementalPathAccepted",
         NAMESPACE + "learnedP2AdmissibleIncrementalPathAccepted",
         NAMESPACE + "learnedP2ForbiddenIncrementalPathRejected",
         NAMESPACE + "learnedP2AdmissibleIncrementalAction_exact",
         NAMESPACE + "learnedP2AdmissibleIncrementalEffect_consumes_action",
         NAMESPACE + "learnedP2AdmissibleIncrementalAndFullSuccessor_exact",
         NAMESPACE + "learnedP2AdmissibleIncrementalAndFullCertificate_exact"],
        ["p2_canonical_consumer", "p2_admissible_consumer",
         "p2_forbidden_consumer"]),
    "P2-full-recheck-exact-certified": (
        "P2", METHODS[8], [NAMESPACE + "observeLearnedP2FullRecheck"],
        [NAMESPACE + "learnedP2CanonicalFullRecheckPathAccepted",
         NAMESPACE + "learnedP2AdmissibleFullRecheckPathAccepted",
         NAMESPACE + "learnedP2ForbiddenFullRecheckPathRejected",
         NAMESPACE + "learnedP2AdmissibleFullRecheckAction_exact",
         NAMESPACE + "learnedP2AdmissibleFullRecheckEffect_consumes_action",
         NAMESPACE + "learnedP2AdmissibleIncrementalAndFullSuccessor_exact",
         NAMESPACE + "learnedP2AdmissibleIncrementalAndFullCertificate_exact"],
        ["p2_canonical_consumer", "p2_admissible_consumer",
         "p2_forbidden_consumer"]),
    "P3-incremental-certified": (
        "P3", METHODS[4], [NAMESPACE + "observeGenericIncremental"],
        [NAMESPACE + "learnedP3ArtifactHeldFixed",
         NAMESPACE + "learnedP3TransitionChanged",
         NAMESPACE + "learnedP3AllowedIncrementalAccepted",
         NAMESPACE + "learnedP3ChangedIncrementalRejected"],
        ["p3_allowed_contract_transition", "p3_rejected_contract_transition"]),
    "P3-full-certified": (
        "P3", METHODS[8], [NAMESPACE + "observeIndependentFullRecheck"],
        [NAMESPACE + "learnedP3ArtifactHeldFixed",
         NAMESPACE + "learnedP3TransitionChanged",
         NAMESPACE + "learnedP3AllowedFullRecheckAccepted",
         NAMESPACE + "learnedP3ChangedFullRecheckRejected"],
        ["p3_allowed_contract_transition", "p3_rejected_contract_transition"]),
    "P4-relational-certified": (
        "P4", METHODS[6],
        [NAMESPACE + "learnedAlignedExecutedFutureForgetting",
         NAMESPACE + "learnedP4IncorrectForgetting"],
        [NAMESPACE + "learnedExecutedFutureForgetting_preserves_every_finite_future",
         NAMESPACE + "learnedExecutedFutureForgetting_origin_not_recoverable",
         NAMESPACE + "learnedP4SeparatorRevealsRequiredDistinction",
         NAMESPACE + "learnedP4IncorrectForgettingCannotBeExact"],
        ["p4_separator_nonempty", "p4_incorrect_forgetting_fff_collapses",
         "p4_separator_reveals_required_distinction"]),
    "P5-self-adaptive-certified": (
        "P5", METHODS[3], [NAMESPACE + "observeRuntimeSubmission"],
        [NAMESPACE + "learnedPostForgettingOperationalClosure",
         NAMESPACE + "learnedPostForgettingBadChange_rejected_without_successor"],
        ["p5_accepted_contract_change", "p5_rejected_contract_change"]),
    "P5-incremental-certified": (
        "P5", METHODS[4], [NAMESPACE + "observePostForgettingIncremental"],
        [NAMESPACE + "learnedPostForgettingExtendedChange_incremental"],
        ["p5_accepted_contract_change", "p5_rejected_contract_change"]),
    "P5-full-certified": (
        "P5", METHODS[8], [NAMESPACE + "observePostForgettingFullRecheck"],
        [NAMESPACE + "learnedPostForgettingExtendedChange_full",
         NAMESPACE + "learnedClosedPostForgettingFullRecheck_successor_exact"],
        ["p5_accepted_contract_change", "p5_rejected_contract_change"]),
    "P6-incremental-certified": (
        "P6", METHODS[4], [NAMESPACE + "runLearnedP6SuccessiveComparison"],
        [NAMESPACE + "learnedSuccessiveInstalledStructuralAssembly_exact",
         NAMESPACE + "learnedSuccessiveTransport_reads_checked_source"],
        ["p6_successive_decision", "p6_successive_transported_structural_fragments",
         "p6_successive_recomputed_structural_fragments"]),
    "P6-full-certified": (
        "P6", METHODS[8], [NAMESPACE + "runLearnedP6SuccessiveComparison"],
        [NAMESPACE + "learnedSuccessiveIncrementalAndFullSuccessor_exact",
         NAMESPACE + "learnedSuccessiveIncrementalAndFullCertificate_exact"],
        ["p6_successive_decision"]),
}

# Proof-only rows are bound to complete Lean names.  A basename is not an
# identity: accepting `Fake.Namespace.foo` because some unrelated `foo` exists
# would let the evidence ledger cite a declaration Lean itself rejects.
PROOF_ONLY_CONTRACTS = [
    ("self-adaptive installed history is checked",
     NAMESPACE + "GuaranteedSelfAdaptiveAdapterOutput.everyInstalledStepChecked"),
    ("self-adaptive installed history preserves contracts",
     NAMESPACE + "GuaranteedSelfAdaptiveAdapterOutput.everyInstalledStepPreservesContracts"),
    ("incremental structural fragments are source-transported",
     NAMESPACE + "IncrementalProofReuseAdapterOutput.learnedReuseExact"),
    ("deployment history is checked",
     NAMESPACE + "DeploymentChainPropagationAdapterOutput.checkedHistory"),
    ("deployment history preserves contracts",
     NAMESPACE + "DeploymentChainPropagationAdapterOutput.preservedContracts"),
    ("complete-recheck successor equals incremental successor",
     NAMESPACE + "IndependentFullRecheckComparisonOutput.alignedSuccessorMatchesIncremental"),
    ("complete recheck accepts without incremental oracle",
     NAMESPACE + "IndependentFullRecheckComparisonOutput.acceptedWithoutIncrementalOracle"),
    ("executed forgetting preserves every covered finite future",
     NAMESPACE + "learnedExecutedFutureForgetting_preserves_every_finite_future"),
    ("historical origin is not recoverable after executed forgetting",
     NAMESPACE + "learnedExecutedFutureForgetting_origin_not_recoverable"),
    ("refused post-forgetting contract change has no successor",
     NAMESPACE + "LearnedPostForgettingOperationalClosure.refusedContractChangeHasNoSuccessor"),
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"JSON object required: {path}")
    return value


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
            "protocol claims results before immutable result creation")
    require(protocol.get("methods") == METHODS, "method order changed")
    require(protocol.get("translation_counts") == TRANSLATIONS,
            "translation counts changed")
    require(bool(protocol.get("common_material")) and
            bool(protocol.get("common_property")),
            "common material or common property is absent")
    trust = protocol.get("trust_boundaries")
    require(isinstance(trust, dict) and list(trust) == METHODS and
            all(isinstance(trust[method], str) and trust[method].strip()
                for method in METHODS),
            "method trust boundaries are incomplete or reordered")
    require("no runtime, memory, speedup or asymptotic claim" in
            protocol.get("cost_policy", ""),
            "cost non-claim is absent")
    require(protocol.get("covered_probes") == [f"P{i}" for i in range(1, 9)],
            "P1-P8 coverage inventory changed")
    require(protocol.get("covered_criteria") ==
            ["S1", "S2", "S3", "S4", "S5", "S7", "S8"],
            "criterion inventory changed")
    delegated = protocol.get("delegated_without_reclassification", {})
    require(set(delegated) == {"P8", "S6"} and
            all("draft" in value and "no confirmatory result" in value
                for value in delegated.values()),
            "P8/S6 draft status is not explicit")
    forbidden = protocol.get("corrections", {}).get("forbidden_reference_inputs")
    require(isinstance(forbidden, list) and len(forbidden) == 5,
            "reference-oracle exclusion is incomplete")
    require("same executed network outputs" in
            protocol.get("corrections", {}).get("p2_scope", ""),
            "P2 exact fixed-network scope is absent")
    require("incorrect collapsing projection" in
            protocol.get("corrections", {}).get("p4_scope", ""),
            "P4 incorrect-forgetting scope is absent")
    require("Ordinary continuation" in
            protocol.get("corrections", {}).get("p5_scope", ""),
            "P5 exact installed-transition scope is absent")
    require("learnedExtendedSerializedUpdate" in
            protocol.get("corrections", {}).get("p6_scope", ""),
            "P6 exact successive execution scope is absent")
    require(protocol.get("build_command") ==
            ["lake", "-K", 'moreLeanArgs=["-M=8192"]', "build",
             "compiled_independent_complete_neural_comparison"],
            "memory-bounded compiled build command changed")
    require(protocol.get("reference_audit_command") ==
            ["lake", "env", "lean", "-M", "8192",
             "Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean"],
            "memory-bounded reference audit command changed")
    require(protocol.get("executed_command") ==
            ["lake", "-K", 'moreLeanArgs=["-M=8192"]', "exe",
             "compiled_independent_complete_neural_comparison"],
            "compiled command changed")
    require(protocol.get("output_policy", {}).get("rows") == 9,
            "nine output rows are not required")
    require(protocol.get("output_policy", {}).get("overwrite") is False,
            "output overwrite is permitted")
    for relative, expected in protocol.get("historical_v10_preserved", {}).items():
        path = ROOT / relative
        require(path.is_file(), f"historical v10 evidence missing: {relative}")
        require(digest(path.read_bytes()) == expected,
                f"historical v10 evidence changed: {relative}")
    if status == "draft-awaiting-stable-source-commit":
        require(protocol.get("confirmatory_run_permitted") is False,
                "draft protocol permits a confirmatory run")
        require(not SNAPSHOT.exists(), "draft unexpectedly has a frozen snapshot")
        material_paths(working_reader)
    else:
        require(protocol.get("confirmatory_run_permitted") is True,
                "frozen protocol does not permit its preregistered run")
        require(protocol.get("protocol_sha256") ==
                canonical_digest(protocol, "protocol_sha256"),
                "frozen protocol seal differs")
        require(protocol.get("frozen_snapshot") ==
                SNAPSHOT.relative_to(ROOT).as_posix(),
                "frozen snapshot path differs")
        require(SNAPSHOT.is_file(), "frozen snapshot is missing")
        require(protocol.get("frozen_snapshot_sha256") ==
                digest(SNAPSHOT.read_bytes()), "frozen snapshot file hash differs")
        snapshot = load(SNAPSHOT)
        validate_snapshot(snapshot, check_worktree=True)
        require(protocol.get("frozen_source_commit") == snapshot["source_commit"],
                "protocol and snapshot commits differ")
        require(protocol.get("frozen_source_git_tree") == snapshot["source_tree"],
                "protocol and snapshot trees differ")


def lean_declaration_basenames() -> set[str]:
    declaration_pattern = re.compile(
        r"(?m)^\s*(?:def|theorem|structure|inductive|abbrev)\s+"
        r"([A-Za-z_][A-Za-z_0-9']*)")
    field_pattern = re.compile(
        r"(?m)^\s{2,}([A-Za-z_][A-Za-z_0-9']*)\s*:")
    declarations: set[str] = set()
    for path in ROOT.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        source = path.read_text(encoding="utf-8")
        declarations.update(declaration_pattern.findall(source))
        declarations.update(field_pattern.findall(source))
    return declarations


def validate_ledger(ledger: dict[str, Any]) -> dict[str, dict[str, Any]]:
    require(ledger.get("ledger_id") ==
            "constitutive-neural-oracle-independent-evidence-v13",
            "wrong evidence ledger")
    rows = ledger.get("emitted_fields")
    require(isinstance(rows, dict) and list(rows) == METHODS,
            "evidence methods are missing or reordered")
    for method in METHODS:
        require(set(rows[method]) == FIELDS[method],
                f"field-to-producer mapping mismatch: {method}")
        require(all(isinstance(value, str) and value.strip()
                    for value in rows[method].values()),
                f"empty producer mapping: {method}")
    evidence = ledger.get("probe_evidence")
    require(isinstance(evidence, list) and evidence,
            "structured probe evidence is missing")
    evidence_by_id: dict[str, dict[str, Any]] = {}
    emitted_by_method = {method: set(fields) for method, fields in rows.items()}
    declarations = lean_declaration_basenames()
    for row in evidence:
        identifier = row.get("id")
        require(isinstance(identifier, str) and identifier not in evidence_by_id,
                "duplicate or absent evidence id")
        require(all(key in row for key in
                    ("probe", "method", "input", "execution", "producers",
                     "proofs", "result_fields", "scope")),
                f"incomplete structured evidence: {identifier}")
        method = row["method"]
        require(method in METHODS, f"unknown evidence method: {identifier}")
        require(bool(row["input"]) and bool(row["execution"]) and bool(row["scope"]),
                f"empty structured evidence: {identifier}")
        require(isinstance(row["producers"], list) and row["producers"] and
                isinstance(row["proofs"], list) and
                isinstance(row["result_fields"], list),
                f"invalid evidence lists: {identifier}")
        require(set(row["result_fields"]) <= emitted_by_method[method],
                f"evidence cites a field emitted by another method: {identifier}")
        require(identifier in EVIDENCE_CONTRACTS,
                f"unreviewed evidence record: {identifier}")
        expected = EVIDENCE_CONTRACTS[identifier]
        actual = (row["probe"], row["method"], row["producers"],
                  row["proofs"], row["result_fields"])
        require(actual == expected,
                f"evidence wiring differs from its reviewed contract: {identifier}")
        for declaration in row["producers"] + row["proofs"]:
            require(isinstance(declaration, str) and
                    declaration.rsplit(".", 1)[-1] in declarations,
                    f"evidence declaration does not exist: {declaration}")
        evidence_by_id[identifier] = row
    require(set(evidence_by_id) == set(EVIDENCE_CONTRACTS),
            "reviewed evidence records are missing or extra")
    proofs = ledger.get("proof_only_evidence")
    require(isinstance(proofs, list), "proof-only evidence set is absent")
    actual_proofs = [(proof.get("property"), proof.get("declaration"))
                     for proof in proofs if isinstance(proof, dict)]
    require(actual_proofs == PROOF_ONLY_CONTRACTS,
            "proof-only evidence differs from its reviewed fully-qualified contract")
    return evidence_by_id


def validate_probes(probes: dict[str, Any]) -> None:
    require(probes.get("specification_id") ==
            "constitutive-neural-independent-capability-probes-v13",
            "wrong probe specification")
    rows = probes.get("probes")
    require(isinstance(rows, list) and
            [row.get("id") for row in rows] == [f"P{i}" for i in range(1, 9)],
            "P1-P8 are not specified exactly once in order")
    for row in rows:
        require(bool(row.get("question")) and row.get("held_fixed") and
                row.get("varied") and row.get("required_outcomes"),
                f"probe is underspecified: {row.get('id')}")
    p2 = rows[1]
    require("shared output list" in p2.get("exact_control", "") and
            "exact learned network execution" in p2.get("interface_limit", "") and
            "does not claim" in p2.get("interface_limit", ""),
            "P2 exact control or its interface boundary is absent")
    require("admissible" in " ".join(p2["required_outcomes"]) and
            "cross-version" in " ".join(p2["required_outcomes"]) and
            "independent complete recheck" in " ".join(p2["required_outcomes"]),
            "P2 admissible, invalidation or recheck obligation is absent")
    require("incorrect collapsing projection" in
            " ".join(rows[3]["required_outcomes"]),
            "P4 incorrect-forgetting control is absent")
    require(all(term in " ".join(rows[5]["required_outcomes"])
                for term in ("other-version", "substituted successor",
                             "incompatible fragments")),
            "P6 negative substitutions are absent")
    require(rows[6].get("current_status", "").startswith("not-certified"),
            "P7 was promoted before confirmation")
    require(rows[7].get("current_status", "").startswith("not-certified"),
            "P8 was promoted without v12 confirmation")


def validate_ablations(specification: dict[str, Any]) -> None:
    require(specification.get("campaign_id") ==
            "constitutive-neural-independent-capability-ablations-v13",
            "wrong ablation campaign")
    rows = specification.get("ablations")
    require(isinstance(rows, list) and
            {row.get("probe") for row in rows} == {f"P{i}" for i in range(1, 9)},
            "semantic ablations do not cover P1-P8")
    registry = REGISTRY.read_text(encoding="utf-8")
    required_fixtures = {
        "P2": {
            "Tests/ExpectedFailure/LearnedP2ModifiedDecoderCannotSatisfyCanonicalPath.lean.fail",
            "Tests/ExpectedFailure/LearnedP2FragmentCannotCrossConsumerVersions.lean.fail",
            "Tests/ExpectedFailure/LearnedP2IncrementalAnalysisCannotCrossConsumerVersions.lean.fail",
            "Tests/ExpectedFailure/LearnedP2FullDecodedArtifactCannotCrossConsumerVersions.lean.fail",
        },
        "P4": {
            "Tests/ExpectedFailure/PostForgettingCannotRecoverHistoricalIdentity.lean.fail",
            "Tests/ExpectedFailure/SeparatedLearnedFutureCannotShareExactMemory.lean.fail",
        },
        "P6": {
            "Tests/ExpectedFailure/RecomputedFragmentCannotReplaceLicensedTransport.lean.fail",
            "Tests/ExpectedFailure/LearnedExtendedFragmentsCannotReplaceAlignedFragments.lean.fail",
            "Tests/ExpectedFailure/ReconstructedLearnedSuccessorCannotInstall.lean.fail",
        },
    }
    for row in rows:
        require(bool(row.get("mutation")), "ablation mutation is absent")
        fixture = row.get("fixture")
        gate = row.get("gate")
        require((fixture is None) != (gate is None),
                "ablation must name exactly one fixture or gate")
        if fixture:
            require((ROOT / fixture).is_file(), f"ablation fixture missing: {fixture}")
            require(any(line.startswith(fixture + "\t") and
                        len(line.split("\t")) == 6 and line.split("\t")[5].strip()
                        for line in registry.splitlines()),
                    f"ablation fixture lacks an exact semantic registry row: {fixture}")
        else:
            require((ROOT / gate).is_file(), f"ablation gate missing: {gate}")
    for probe, required in required_fixtures.items():
        actual = {row.get("fixture") for row in rows if row.get("probe") == probe}
        require(required <= actual,
                f"{probe} mandatory semantic mutations are incomplete")


def validate_matrix(
    matrix: dict[str, Any], evidence_by_id: dict[str, dict[str, Any]]
) -> None:
    require(matrix.get("matrix_id") ==
            "constitutive-neural-exact-capability-matrix-v13",
            "wrong matrix id")
    require(set(matrix.get("status_vocabulary", [])) == VOCABULARY,
            "matrix status vocabulary changed")
    require("Nonempty" not in matrix.get("evidence_policy", "") and
            "never sufficient" in matrix.get("evidence_policy", ""),
            "matrix evidence policy is absent")
    cells = matrix.get("cells")
    require(isinstance(cells, list) and len(cells) == 72,
            "matrix must contain exactly 9 x 8 cells")
    expected = [(f"P{probe}", method)
                for probe in range(1, 9) for method in METHODS]
    require([(cell.get("probe"), cell.get("method")) for cell in cells] == expected,
            "matrix cells are missing, duplicated or reordered")
    for cell in cells:
        require(cell.get("status") in VOCABULARY and bool(cell.get("evidence")),
                f"invalid or unexplained matrix cell: {cell}")
        positive = cell["status"] in {"certified", "observed"}
        require((cell.get("evidence_id") in evidence_by_id) if positive
                else ("evidence_id" not in cell),
                f"cell evidence contract differs: {cell['probe']} {cell['method']}")
        if positive:
            evidence = evidence_by_id[cell["evidence_id"]]
            require(evidence["probe"] == cell["probe"] and
                    evidence["method"] == cell["method"],
                    f"cell points to evidence from another probe or method: "
                    f"{cell['probe']} {cell['method']}")
    lookup = {(cell["probe"], cell["method"]): cell for cell in cells}
    require(lookup[("P2", METHODS[1])].get("evidence_id") ==
            "P2-fixed-network-exact-certified",
            "exact fixed-network P2 evidence is absent")
    require(lookup[("P2", METHODS[4])].get("evidence_id") ==
            "P2-incremental-exact-certified",
            "P2 incremental exact-execution evidence is absent")
    require(lookup[("P2", METHODS[8])].get("evidence_id") ==
            "P2-full-recheck-exact-certified",
            "P2 independent full-recheck evidence is absent")
    require(lookup[("P5", METHODS[6])]["status"] == "not-certified",
            "permission-only evidence incorrectly certifies P5")
    require(lookup[("P5", METHODS[3])].get("evidence_id") ==
            "P5-self-adaptive-certified", "installed P5 runtime evidence is absent")
    for probe in ("P7", "P8"):
        require(all(lookup[(probe, method)]["status"] == "not-certified"
                    for method in METHODS), f"{probe} promoted before its run")


def validate_schema(schema: dict[str, Any]) -> None:
    require(schema.get("$id") ==
            "constitutive-neural-oracle-independent-result-v13",
            "wrong result schema")
    required = set(schema.get("required", []))
    require({"frozen_source_commit", "frozen_source_tree", "snapshot_sha256",
             "protocol_sha256", "command", "build_command",
             "reference_audit_command",
             "ablation_results", "ablation_output_sha256"}
            <= required, "result does not bind snapshot, protocol and ablations")
    properties = schema.get("properties", {})
    require(properties.get("command", {}).get("const") ==
            ["lake", "-K", 'moreLeanArgs=["-M=8192"]', "exe",
             "compiled_independent_complete_neural_comparison"],
            "result schema does not fix the execution command")
    require(properties.get("build_command", {}).get("const") ==
            ["lake", "-K", 'moreLeanArgs=["-M=8192"]', "build",
             "compiled_independent_complete_neural_comparison"],
            "result schema does not fix the build command")
    require(properties.get("reference_audit_command", {}).get("const") ==
            ["lake", "env", "lean", "-M", "8192",
             "Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean"],
            "result schema does not fix the reference audit command")
    rows = properties.get("rows", {})
    require(rows.get("minItems") == 9 and rows.get("maxItems") == 9,
            "schema does not require nine rows")
    ablation_results = properties.get("ablation_results", {})
    require(ablation_results.get("minItems") == 17 and
            ablation_results.get("maxItems") == 17,
            "schema does not require exactly every authorized semantic ablation")


def validate_criteria(criteria: dict[str, Any]) -> None:
    expected = ["S1", "S2", "S3", "S4", "S5", "S7", "S8"]
    rows = criteria.get("criteria")
    require(isinstance(rows, list) and
            [row.get("id") for row in rows] == expected,
            "success criteria set changed")
    require(all(row.get("status") == "not-certified" for row in rows),
            "criterion promoted before results and audits")
    require(bool(criteria.get("conclusion_rule")), "conclusion rule is absent")


def validate_sources() -> None:
    implementation = (ROOT / "RelationalPerimeter/Agents/Neural/IndependentCapabilityComparison.lean").read_text(encoding="utf-8")
    controls = (ROOT / "RelationalPerimeter/Agents/Neural/IndependentCapabilityProbeControls.lean").read_text(encoding="utf-8")
    emitter = (ROOT / "Tests/Executables/CompiledIndependentCompleteNeuralComparison.lean").read_text(encoding="utf-8")
    regression = (ROOT / "Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean").read_text(encoding="utf-8")
    for marker in ["def independentReferenceDecision",
                   "def computeIndependentReferenceObservation",
                   "def runIndependentReferenceCombination",
                   "def independentCompleteComparisonBundle"]:
        require(marker in implementation, f"implementation marker missing: {marker}")
    for marker in ["def learnedP2FixedNetworkOutputs",
                   "def learnedP2AdmissibleDecoder",
                   "def learnedP2ModifiedDecoder",
                   "def checkLearnedP2Path",
                   "def recheckLearnedP2Path",
                   "theorem learnedP2CanonicalRequest_is_executed",
                   "theorem learnedP2AdmissiblePathAccepted",
                   "theorem learnedP2ModifiedPathRejected",
                   "def learnedP4IncorrectForgetting",
                   "theorem learnedP4IncorrectForgettingCannotBeExact",
                   "def runLearnedP6SuccessiveComparison",
                   "def learnedP2IncrementalCheckerEngine",
                   "def learnedP2FullRecheckEngine",
                   "def learnedP2ReceivedTargetAnalysis",
                   "def LearnedP2ConsumerFragment.action",
                   "def LearnedP2ConsumerFragment.effect",
                   "def LearnedP2DecodedArtifact.fragments",
                   "theorem learnedP2AdmissibleIncrementalAndFullSuccessor_exact",
                   "def learnedP3RejectedContractTransitionUpdate",
                   "def observePostForgettingIncremental"]:
        require(marker in controls, f"control marker missing: {marker}")
    for forbidden in ["learnedAlignedRuntimeSubmissionDecision",
                      "learnedBypassRuntimeSubmissionDecision"]:
        require(forbidden not in implementation,
                "independent module names a historical runtime oracle")
    for marker in ["def emitClassRows", "def emitRelationalRow",
                   "def emitReferenceCombinationRow", "def emitFullRecheckRow",
                   "p2_canonical_decoder_action",
                   "p2_admissible_modified_decoder_action",
                   "p2_forbidden_modified_decoder_action",
                    "p2_admissible_consumer",
                    "p2_forbidden_consumer",
                   "p4_separator_reveals_required_distinction",
                   "p6_successive_decision",
                   "p3_allowed_contract_transition",
                   "p5_accepted_contract_change"]:
        require(marker in emitter, f"emitter marker missing: {marker}")
    audited_sources = regression + "\n" + emitter
    reviewed_declarations = []
    for contract in EVIDENCE_CONTRACTS.values():
        reviewed_declarations.extend(contract[2])
        reviewed_declarations.extend(contract[3])
    reviewed_declarations.extend(
        declaration for _property, declaration in PROOF_ONLY_CONTRACTS)
    for declaration in dict.fromkeys(reviewed_declarations):
        require(f"#print axioms {declaration}" in audited_sources,
                f"fully-qualified evidence declaration is not resolved by Lean: {declaration}")


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
    present = RAW.exists() or RECORD.exists() or ABLATION_RESULTS.exists()
    if not present:
        return
    require(allow_results, "reserved result exists without explicit validation")
    require(protocol.get("status") == "frozen-before-confirmatory-run",
            "result exists for an unfrozen protocol")
    require(RAW.is_file() and RECORD.is_file() and ABLATION_RESULTS.is_file(),
            "raw, record and ablation results must coexist")
    rows = parse_rows(RAW.read_text(encoding="utf-8"))
    ablations = load(ABLATION_RESULTS)
    record = load(RECORD)
    require(record.get("protocol_id") == protocol.get("protocol_id"),
            "result protocol differs")
    require(record.get("command") == protocol.get("executed_command"),
            "recorded execution command differs from the frozen protocol")
    require(record.get("build_command") == protocol.get("build_command"),
            "recorded build command differs from the frozen protocol")
    require(record.get("reference_audit_command") ==
            protocol.get("reference_audit_command"),
            "recorded reference audit command differs from the frozen protocol")
    require(record.get("rows") == rows, "record differs from raw rows")
    repository_commit = record.get("repository_commit")
    source_commit = record.get("frozen_source_commit")
    require(isinstance(repository_commit, str) and len(repository_commit) == 40,
            "recorded evidence commit is absent")
    require(git("cat-file", "-t", repository_commit) == "commit",
            "recorded evidence commit is unavailable")
    snapshot = load(SNAPSHOT)
    git("merge-base", "--is-ancestor", repository_commit,
        snapshot["remote_ref"])
    require(source_commit == protocol.get("frozen_source_commit"),
            "recorded frozen source commit differs")
    git("merge-base", "--is-ancestor", source_commit, repository_commit)
    require(record.get("frozen_source_tree") ==
            protocol.get("frozen_source_git_tree"),
            "recorded frozen source tree differs")
    require(record.get("raw_output_sha256") == digest(RAW.read_bytes()),
            "raw result hash differs")
    require(record.get("ablation_results") == ablations.get("results"),
            "record differs from ablation output")
    specification = load(ABLATIONS)["ablations"]
    expected_ablations = [
        (row["probe"], row["mutation"])
        for row in specification if "fixture" in row
    ] + [
        (row["probe"], "transitive audited-verdict injection")
        for row in specification if "gate" in row
    ]
    actual_ablations = [
        (row.get("probe"), row.get("mutation"))
        for row in ablations.get("results", [])
    ]
    require(actual_ablations == expected_ablations and
            all(row.get("outcome") == "rejected"
                for row in ablations.get("results", [])),
            "semantic ablation output is incomplete, reordered or non-rejecting")
    require(record.get("ablation_output_sha256") ==
            digest(ABLATION_RESULTS.read_bytes()), "ablation result hash differs")
    require(record.get("snapshot_sha256") == protocol["frozen_snapshot_sha256"],
            "result snapshot differs")
    require(record.get("protocol_sha256") == protocol["protocol_sha256"],
            "result protocol seal differs")


def validate_all(allow_draft: bool, allow_results: bool) -> None:
    protocol = load(PROTOCOL)
    validate_protocol(protocol, allow_draft)
    evidence_by_id = validate_ledger(load(LEDGER))
    validate_probes(load(PROBES))
    validate_ablations(load(ABLATIONS))
    validate_matrix(load(MATRIX), evidence_by_id)
    validate_schema(load(SCHEMA))
    validate_criteria(load(CRITERIA))
    validate_sources()
    validate_results(protocol, allow_results)


def expect_failure(action: Callable[[], None], name: str) -> None:
    try:
        action()
    except ValueError:
        return
    raise ValueError(f"negative mutation survived: {name}")


def self_test() -> None:
    protocol = load(PROTOCOL)
    ledger = load(LEDGER)
    matrix = load(MATRIX)
    evidence_by_id = validate_ledger(ledger)

    changed = copy.deepcopy(protocol)
    changed["corrections"]["forbidden_reference_inputs"].pop()
    expect_failure(lambda: validate_protocol(changed, True),
                   "erased transitive oracle exclusion")
    changed = copy.deepcopy(protocol)
    changed["covered_probes"].remove("P8")
    expect_failure(lambda: validate_protocol(changed, True), "missing P8")
    changed = copy.deepcopy(protocol)
    changed.pop("reference_audit_command")
    expect_failure(lambda: validate_protocol(changed, True),
                   "reference audit omitted from confirmatory runner")
    changed_ledger = copy.deepcopy(ledger)
    changed_ledger["emitted_fields"][METHODS[3]].pop("p5_accepted_contract_change")
    expect_failure(lambda: validate_ledger(changed_ledger),
                   "erased installed P5 observation")
    changed_ledger = copy.deepcopy(ledger)
    changed_ledger["probe_evidence"][0].pop("input")
    expect_failure(lambda: validate_ledger(changed_ledger),
                   "evidence label without exact input")
    changed_ledger = copy.deepcopy(ledger)
    changed_ledger["probe_evidence"][0]["producers"] = [
        NAMESPACE + "producerThatDoesNotExist"]
    changed_ledger["probe_evidence"][0]["proofs"] = [
        NAMESPACE + "proofThatDoesNotExist"]
    expect_failure(lambda: validate_ledger(changed_ledger),
                   "nonexistent producer and proof")
    changed_ledger = copy.deepcopy(ledger)
    changed_ledger["proof_only_evidence"][7]["declaration"] = (
        "Nonexistent.AuditNamespace."
        "learnedExecutedFutureForgetting_preserves_every_finite_future")
    expect_failure(lambda: validate_ledger(changed_ledger),
                   "nonexistent fully-qualified proof-only declaration")
    changed_ledger = copy.deepcopy(ledger)
    p3 = next(row for row in changed_ledger["probe_evidence"]
              if row["id"] == "P3-incremental-certified")
    p3["proofs"] = list(EVIDENCE_CONTRACTS["P1-incremental-certified"][3])
    expect_failure(lambda: validate_ledger(changed_ledger),
                   "P3 evidence replaced by P1 proof")
    changed_matrix = copy.deepcopy(matrix)
    cell = next(row for row in changed_matrix["cells"]
                if row["probe"] == "P2" and row["method"] == METHODS[4])
    cell["evidence_id"] = "P1-incremental-certified"
    expect_failure(lambda: validate_matrix(changed_matrix, evidence_by_id),
                   "P1 proof substituted for P2 checker evidence")
    changed_matrix = copy.deepcopy(matrix)
    cell = next(row for row in changed_matrix["cells"]
                if row["probe"] == "P5" and row["method"] == METHODS[6])
    cell["status"] = "certified"
    cell["evidence_id"] = "P4-relational-certified"
    expect_failure(lambda: validate_matrix(changed_matrix, evidence_by_id),
                   "permission-only evidence promoted to P5")
    changed_matrix = copy.deepcopy(matrix)
    cell = next(row for row in changed_matrix["cells"]
                if row["probe"] == "P7" and row["method"] == METHODS[8])
    cell["status"] = "certified"
    cell["evidence_id"] = "P1-full-certified"
    expect_failure(lambda: validate_matrix(changed_matrix, evidence_by_id),
                   "premature P7 promotion")
    fake_sources = {
        "Root.lean": b"import Dep -- local dependency\n\ndef root := 0\n",
        "Dep.lean": b"def dep := 0\n",
    }
    def fake_reader(relative: str) -> bytes:
        if relative not in fake_sources:
            raise ValueError(f"missing fake material: {relative}")
        return fake_sources[relative]
    require(lean_import_closure(["Root.lean"], fake_reader) ==
            ["Dep.lean", "Root.lean"],
            "Lean import closure drops a trailing-comment dependency")
    print("INDEPENDENT_CAPABILITY_COMPARISON_V13_SELFTEST_OK mutations=11 "
          "import_comment=covered")


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
