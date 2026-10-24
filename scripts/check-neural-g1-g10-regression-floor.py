#!/usr/bin/env python3
"""Reject removal or disconnection of the constructive G1--G10 floor."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEAN_FLOOR = ROOT / "Tests/Mechanisms/NeuralG1G10RegressionFloor.lean"
LEARNED_CLOSURE = (
    ROOT
    / "RelationalPerimeter/Agents/Neural/LearnedFutureConstitutiveClosure.lean"
)
AUTONOMOUS_CLOSURE = (
    ROOT
    / "RelationalPerimeter/Agents/Neural/AutonomousCheckerClosure.lean"
)
ALL_CONSTANTS = ROOT / "Tests/AllConstantsAudit.lean"
C1_C17_GATE = ROOT / "scripts/check-neural-c1-c17-regression-floor.py"
SH_PORTAL = ROOT / "scripts/verify.sh"
PS_PORTAL = ROOT / "scripts/verify.ps1"
NEGATIVE_REGISTRY = ROOT / "scripts/expected-failures.tsv"

REQUIRED_LEAN_NAMES = (
    "g1_authorized_update_is_installed",
    "g1_every_installed_step_preserves_contracts",
    "g2_executed_chain_is_constructed",
    "g2_internal_transformation_is_nonidentity",
    "g2_extended_internal_transformation_is_nonidentity",
    "g3_source_resource_changes_the_reconfiguration",
    "g3_requirement_resource_changes_the_reconfiguration",
    "g3_authorization_is_constitutively_consumed",
    "g3_source_occurrence_is_the_transformed_prior_proposal",
    "g3_context_resource_changes_the_reconfiguration",
    "g4_every_finite_executed_program_is_accepted",
    "g5_installed_runtime_is_accessible",
    "g5_rejected_update_has_no_installed_successor",
    "g6_historical_inputs_are_distinct",
    "g6_outputs_converge_only_after_execution",
    "g6_forgotten_origin_is_not_recoverable",
    "g6_every_covered_finite_future_is_preserved",
    "g7_public_success_iff_autonomous_local_conditions",
    "g7_learned_success_iff_autonomous_local_conditions",
    "g7_successive_incremental_and_full_recheck_agree",
    "g7_successive_incremental_and_full_successor_exact",
    "g7_post_forgetting_continuation_is_relatively_complete",
    "g7_post_forgetting_contract_change_is_relatively_complete",
    "g7_post_forgetting_contract_change_is_effectfully_installed",
    "g7_post_forgetting_contract_change_consumes_transport_and_recheck",
    "g7_post_forgetting_contract_change_consumes_executed_reduction",
    "g7_post_forgetting_contract_change_resources_feed_installed_certificate",
    "g7_post_forgetting_contract_change_matches_full_recheck",
    "g7_post_forgetting_contract_change_shares_action_with_effect",
    "g7_post_forgetting_bad_change_has_no_successor",
    "g8_unaffected_fragment_is_transported",
    "g8_incremental_and_full_recheck_are_equal",
    "g9_independent_learned_artifact_is_decodable",
    "g9_positive_continuation_has_two_executed_steps",
    "g10_latent_bypass_is_distinguished",
)

REQUIRED_NEGATIVE_FIXTURES = (
    "ReverseOperationalContractTransitionCannotBeAuthorized.lean.fail",
    "PostHocConstantTransformCannotWitnessExecution.lean.fail",
    "ZeroWeightEdgeCannotWitnessCausalParticipation.lean.fail",
    "FixedSystemCannotCertifyReconfiguredTail.lean.fail",
    "RejectedUpdateCannotWitnessRuntimeReachability.lean.fail",
    "AlreadyForgottenInputCannotWitnessExecutedForgetting.lean.fail",
    "ConstantProjectionCannotWitnessExecutedForgetting.lean.fail",
    "AnalyzerSuccessCannotDefineLocalConditions.lean.fail",
    "CompletedTargetCannotReplacePublicExecutedAnalysis.lean.fail",
    "CompletedTargetCannotReplaceLearnedExecutedAnalysis.lean.fail",
    "AffectedNodeCannotBeReused.lean.fail",
    "RecomputedFragmentCannotReplaceLicensedTransport.lean.fail",
    "SingletonLearnedDomainCannotReplaceCanonicalDomain.lean.fail",
    "BypassCannotSatisfyExactLearnedFutureContract.lean.fail",
    "ForeignLearnedRuntimeCannotEnterJointClosure.lean.fail",
    "JointClosureCannotSubstituteSecondProduction.lean.fail",
    "LearnedSourceRoleCannotBeOmittedFromReconfiguration.lean.fail",
    "LearnedRequirementCannotBeBypassedInReconfiguration.lean.fail",
    "LearnedAdmissionCannotReplaceIncorporatedAuthorization.lean.fail",
    "ForeignLearnedActionCannotReplaceInstallingAction.lean.fail",
    "ForeignCurrentCannotDriveLearnedInstallation.lean.fail",
    "ForeignLearnedEffectCannotReplaceInstallingEffect.lean.fail",
    "ReconstructedLearnedEffectCannotReplaceProducedEffect.lean.fail",
    "ReconstructedLearnedSuccessorCannotInstall.lean.fail",
    "PostForgettingRefusedRequestCannotSatisfyLocalConditions.lean.fail",
    "PostForgettingFullRecheckCannotConsumeIncrementalVerdict.lean.fail",
    "PostForgettingContinuationCannotMasqueradeAsContractUpdate.lean.fail",
    "PostForgettingContinuationCannotReplaceExecutionReceipt.lean.fail",
    "PostForgettingReceiptCannotBeErasedFromTargetAnalysis.lean.fail",
    "PostForgettingContractChangeCannotStartFromInitial.lean.fail",
    "PostForgettingPermissionCannotReplaceClosedChange.lean.fail",
)

REQUIRED_JOINT_CLOSURE_NAMES = (
    "LearnedArtifactExecutionLineage",
    "LearnedConstitutiveAlignmentClosureCertificate",
    "learnedConstitutiveAlignmentClosure",
    "lineagePreservesContracts",
    "learningDataExact",
    "learningGeneratorExact",
    "firstProductionExact",
    "secondProductionExact",
    "localReuseLicensesExact",
    "localReusePayloadFromLicenses",
    "extendedAccessible",
    "localReuseExact",
    "localReuseInstalled",
    "firstProducedStateInstalled",
    "secondProducedStateInstalled",
    "incrementalFullSuccessorExact",
    "futureSourceFromInstalledRuntime",
    "forgettingConsumesAlignedRuntime",
    "bypassHasNoInstalledSuccessor",
)

REQUIRED_POST_FORGETTING_CLOSURE_NAMES = (
    "LearnedPostForgettingOperationalClosure",
    "learnedPostForgettingOperationalClosure",
    "submitLearnedPostForgettingContinuation",
    "learnedInstalledPostForgettingContinuation_consumes_reducedMemory",
    "learnedInstalledPostForgettingContinuation_nextMemory_consumes_reducedMemory",
    "learnedPostForgettingExecutionReceipt_outcome_is_installed",
    "learnedPostForgettingExecutionReceipt_nextMemory_is_installed",
    "submitUpdate_postForgettingExtended_exact",
    "learnedClosedPostForgettingExtendedChange",
    "reducedMemoryProduced",
    "resourcePhaseConsumesReducedMemory",
    "targetConsumesTransportedIntent",
    "targetConsumesRecheckedAuthorization",
    "targetSharesActionWithEffect",
    "targetActionConsumesReceipt",
    "fullRecheckSuccessorExact",
    "checkLearnedPostForgettingExtendedRuntimeUpdate_exact",
    "learnedPostForgettingExtendedRuntime_reachable",
    "learnedPostForgettingBadChange_rejected_without_successor",
)

FORBIDDEN_MIXED_FLOOR_NAMES = (
    "publicSubstantiveAlignment",
    "publicReconfiguration",
    "public_terminal_memory_preserves_every_future",
    "publicIncrementalAndReferenceChecks_exact",
    "constitutiveChecker_detectsLatentBypass",
)


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_G1_G10_REGRESSION_FLOOR_ERROR: {message}")


def require_all(text: str, required: tuple[str, ...], label: str) -> None:
    missing = [item for item in required if item not in text]
    if missing:
        fail(f"{label} missing: {', '.join(missing)}")


def main() -> None:
    lean_text = LEAN_FLOOR.read_text(encoding="utf-8")
    require_all(lean_text, REQUIRED_LEAN_NAMES, "named Lean floor")
    require_all(
        lean_text,
        ("learnedConstitutiveAlignmentClosure",),
        "joint learned regression floor",
    )
    mixed = [name for name in FORBIDDEN_MIXED_FLOOR_NAMES if name in lean_text]
    if mixed:
        fail(f"mixed public/learned evidence returned: {', '.join(mixed)}")

    closure_text = LEARNED_CLOSURE.read_text(encoding="utf-8")
    require_all(
        closure_text,
        REQUIRED_JOINT_CLOSURE_NAMES,
        "joint learned closure",
    )
    require_all(
        AUTONOMOUS_CLOSURE.read_text(encoding="utf-8"),
        REQUIRED_POST_FORGETTING_CLOSURE_NAMES,
        "post-forgetting operational closure",
    )

    import_name = "import Tests.Mechanisms.NeuralG1G10RegressionFloor"
    if import_name not in ALL_CONSTANTS.read_text(encoding="utf-8"):
        fail("the exhaustive constant audit does not import the G1--G10 floor")

    if not C1_C17_GATE.is_file():
        fail("the C1--C17 regression gate is missing")

    gate = Path(__file__).name
    c1_gate = C1_C17_GATE.name
    for portal in (SH_PORTAL, PS_PORTAL):
        portal_text = portal.read_text(encoding="utf-8")
        require_all(portal_text, (gate, c1_gate), portal.name)

    registry_text = NEGATIVE_REGISTRY.read_text(encoding="utf-8")
    require_all(
        registry_text,
        REQUIRED_NEGATIVE_FIXTURES,
        "G1--G10 negative registry",
    )

    print(
        "NEURAL_G1_G10_REGRESSION_FLOOR_OK "
        f"lean={len(REQUIRED_LEAN_NAMES)} portals=2 "
        f"negative={len(REQUIRED_NEGATIVE_FIXTURES)} "
        "joint_learned=connected c1_c17=connected"
    )


if __name__ == "__main__":
    main()
