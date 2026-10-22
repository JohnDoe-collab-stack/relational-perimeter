#!/usr/bin/env python3
"""Reject removal or disconnection of the established C1--C17 floor."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEAN_FLOOR = ROOT / "Tests/Mechanisms/NeuralC1C17RegressionFloor.lean"
SH_PORTAL = ROOT / "scripts/verify.sh"
PS_PORTAL = ROOT / "scripts/verify.ps1"
NEGATIVE_REGISTRY = ROOT / "scripts/expected-failures.tsv"

REQUIRED_LEAN_NAMES = (
    "complete_serialized_artifact_decoding_is_preserved",
    "every_covered_finite_future_is_preserved",
    "requirement_identity_survives_reindexing",
    "requirement_is_outside_the_computed_affected_cone",
    "authorization_is_inside_the_computed_affected_cone",
    "proposal_is_inside_the_computed_affected_cone",
    "action_is_inside_the_computed_affected_cone",
    "unaffected_requirement_payload_is_really_transported",
    "transported_requirement_payload_is_observed_in_the_target",
    "incremental_and_complete_reference_verdicts_remain_equal",
    "closed_runtime_installs_exactly_the_checked_successor",
    "submitUpdate_rejected_cannot_install",
    "aligned_and_bypass_updates_remain_currently_equivalent",
    "finite_counterfactual_divergence_remains_constructed",
    "latent_bypass_detection_remains_constructed",
)

REQUIRED_PORTAL_GATES = (
    "check-neural-c1-c17-regression-floor.py",
    "check-neural-block-negative-fixtures.py",
    "check-neural-comparison-protocol-v4.py",
    "check-compiled-neural-checker-measurement.py",
    "check-independent-neural-artifact.py",
    "check-final-neural-campaign.py",
    "check-expected-failures",
)

REQUIRED_NEGATIVE_FIXTURES = (
    "ReindexedNodeCannotChangeStableKey.lean.fail",
    "AffectedNodeCannotBeReused.lean.fail",
    "PrivateCertifiedRuntimeConstructor.lean.fail",
    "CertifiedRuntimeCannotBeRecordUpdated.lean.fail",
    "BypassCannotReuseAlignedCertificate.lean.fail",
    "BypassCannotSatisfyCounterfactualContract.lean.fail",
)


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_C1_C17_REGRESSION_FLOOR_ERROR: {message}")


def require_all(text: str, required: tuple[str, ...], label: str) -> None:
    missing = [item for item in required if item not in text]
    if missing:
        fail(f"{label} missing: {', '.join(missing)}")


def main() -> None:
    lean_text = LEAN_FLOOR.read_text(encoding="utf-8")
    require_all(lean_text, REQUIRED_LEAN_NAMES, "named Lean floor")

    for portal in (SH_PORTAL, PS_PORTAL):
        require_all(
            portal.read_text(encoding="utf-8"),
            REQUIRED_PORTAL_GATES,
            portal.name,
        )

    registry_text = NEGATIVE_REGISTRY.read_text(encoding="utf-8")
    require_all(registry_text, REQUIRED_NEGATIVE_FIXTURES, "negative registry")

    print(
        "NEURAL_C1_C17_REGRESSION_FLOOR_OK "
        f"lean={len(REQUIRED_LEAN_NAMES)} "
        f"portals=2 negative={len(REQUIRED_NEGATIVE_FIXTURES)}"
    )


if __name__ == "__main__":
    main()
