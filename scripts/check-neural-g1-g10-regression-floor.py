#!/usr/bin/env python3
"""Reject removal or disconnection of the constructive G1--G10 floor."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEAN_FLOOR = ROOT / "Tests/Mechanisms/NeuralG1G10RegressionFloor.lean"
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
    "g3_source_resource_changes_the_reconfiguration",
    "g3_requirement_resource_changes_the_reconfiguration",
    "g3_authorization_is_constitutively_consumed",
    "g4_every_finite_executed_program_is_accepted",
    "g5_installed_runtime_is_accessible",
    "g5_rejected_update_has_no_installed_successor",
    "g6_historical_inputs_are_distinct",
    "g6_outputs_converge_only_after_execution",
    "g6_forgotten_origin_is_not_recoverable",
    "g6_every_covered_finite_future_is_preserved",
    "g7_public_success_iff_autonomous_local_conditions",
    "g7_learned_success_iff_autonomous_local_conditions",
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
        f"negative={len(REQUIRED_NEGATIVE_FIXTURES)} c1_c17=connected"
    )


if __name__ == "__main__":
    main()
