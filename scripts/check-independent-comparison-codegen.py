#!/usr/bin/env python3
"""Check the transitive compiled boundary of the independent reference method."""

from __future__ import annotations

from pathlib import Path
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
SHARED = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_functions() -> dict[str, str]:
    functions: dict[str, str] = {}
    generated = list((ROOT / ".lake/build/ir").rglob("*.c"))
    require(bool(generated), "generated C is absent; run lake build first")
    for path in generated:
        source = path.read_text(encoding="utf-8")
        functions.update(SHARED["bodies"](source))
        SHARED["add_static_objects"](
            functions,
            SHARED["LITERALS"].sub(lambda match: " " * len(match.group()), source),
        )
    return functions


def require_reaches(functions: dict[str, str], start: str,
                    suffixes: tuple[str, ...], label: str) -> None:
    graph = SHARED["reachable"](functions, start)
    for suffix in suffixes:
        require(any(name.endswith(suffix) for name in graph),
                f"{label} execution does not reach {suffix}")


def validate_graph(functions: dict[str, str]) -> None:
    start = SHARED["select"](
        functions, "NeuralAgent_computeIndependentReferenceObservation")
    SHARED["absent"](
        functions,
        start,
        [
            "NeuralAgent_submitUpdate",
            "checkGenericIncrementalUpdate",
            "checkFullUpdate",
            "frozenFullRecheckDecision",
            "learnedAlignedRuntimeSubmissionDecision",
            "learnedBypassRuntimeSubmissionDecision",
            "runReferenceCombination",
            "frozenCompleteComparisonBundle",
            "learnedConstitutiveAlignmentClosure",
        ],
    )
    p2_incremental = SHARED["select"](
        functions, "NeuralAgent_observeLearnedP2Incremental")
    require_reaches(functions, p2_incremental, (
        "NeuralAgent_checkGenericIncrementalUpdate___redArg",
        "NeuralAgent_analyzeLearnedP2Incrementally",
        "NeuralAgent_checkLearnedP2Path",
        "NeuralAgent_learnedP2TargetAnalysisForAdmittedNamingFromDecision___redArg",
        "NeuralAgent_LearnedP2ConsumerFragment_action___redArg",
        "NeuralAgent_LearnedP2ConsumerFragment_effect___redArg",
        "NeuralAgent_learnedP2RecomputedCertificateFragments___redArg",
    ), "P2 incremental")
    p2_full = SHARED["select"](
        functions, "NeuralAgent_observeLearnedP2FullRecheck")
    require_reaches(functions, p2_full, (
        "NeuralAgent_checkFullUpdate___redArg",
        "NeuralAgent_recomputeLearnedP2FullRecheckExecution",
        "NeuralAgent_decodeLearnedP2Artifact",
        "NeuralAgent_checkLearnedP2Path",
        "NeuralAgent_LearnedP2DecodedArtifact_fragments___redArg",
        "NeuralAgent_LearnedP2ConsumerFragment_action___redArg",
        "NeuralAgent_LearnedP2ConsumerFragment_effect___redArg",
    ), "P2 full recheck")
    print("INDEPENDENT_COMPARISON_P2_CODEGEN_OK "
          "incremental-and-full-consumers=reachable")


def validate_emitter_source() -> None:
    source = (ROOT / "Tests/Executables/CompiledIndependentCompleteNeuralComparison.lean").read_text(
        encoding="utf-8")
    for forbidden in [
        "contracts_preserved\\\":true",
        "reuse_claimed\\\":true",
        "all_steps_checked\\\":true",
        "incremental_verdict_used_as_oracle\\\":false",
        "future_outcomes_different\\\":true",
    ]:
        require(forbidden not in source,
                f"proof consequence printed as a literal observation: {forbidden}")
    for required in [
        "observeRuntimeSubmission",
        "observeGenericIncremental",
        "observeIndependentFullRecheck",
        "observePostForgettingIncremental",
        "observePostForgettingFullRecheck",
        "observeLearnedP2Path",
        "recheckLearnedP2Path",
        "observeLearnedP2Incremental",
        "observeLearnedP2FullRecheck",
        "learnedP2AdmissibleDecoder",
        "learnedP2ModifiedDecoder",
        "learnedP3RejectedContractTransitionUpdate",
        "learnedPostForgettingExtendedRuntimeUpdate",
        "learnedP4IncorrectForgetting",
        "learnedOperationalFutureOutputs",
        "runLearnedP6SuccessiveComparison",
        "p6.incrementalDecision",
        "p6.fullRecheckDecision",
        "p6.transportedStructuralCount",
        "p6.recomputedStructuralCount",
        "observation.alignedDecision",
        "frozenFullRecheckDecision",
    ]:
        require(required in source, f"computed observation is absent: {required}")


def self_test() -> None:
    functions = {
        "l_reference": "{ l_indirect(); }",
        "l_indirect": "{ l_NeuralAgent_submitUpdate(); }",
        "l_NeuralAgent_submitUpdate": "{}",
    }
    try:
        SHARED["absent"](
            functions, "l_reference", ["NeuralAgent_submitUpdate"])
    except ValueError:
        pass
    else:
        raise ValueError("indirect-oracle mutation survived")
    incomplete_p2 = {
        "l_incremental": "{ l_check(); }",
        "l_check": "{}",
    }
    try:
        require_reaches(
            incomplete_p2, "l_incremental",
            ("check", "LearnedP2ConsumerFragment_action___redArg"),
            "mutated P2 incremental")
    except ValueError:
        pass
    else:
        raise ValueError("P2 installed-consumer mutation survived")
    print("INDEPENDENT_COMPARISON_CODEGEN_SELFTEST_OK mutations=2")


def main() -> None:
    self_test()
    validate_emitter_source()
    validate_graph(load_functions())
    print("INDEPENDENT_COMPARISON_CODEGEN_OK reference_oracle_closure=absent "
          "literal_scientific_verdicts=absent")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError) as error:
        raise SystemExit(f"INDEPENDENT_COMPARISON_CODEGEN_ERROR: {error}")
