#!/usr/bin/env python3
"""Validate the frozen pre-confirmatory neural capacity protocol v4."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v4"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
SCHEMA = EXPERIMENT / "comparison-result-schema.json"
README = EXPERIMENT / "README.md"
MANIFEST = EXPERIMENT / "manifest.json"
SH_PORTAL = ROOT / "scripts/verify.sh"
PS_PORTAL = ROOT / "scripts/verify.ps1"

BASELINES = {
    "extensional-current-behavior-verification",
    "fixed-network-interventional-causal-analysis",
    "pre-execution-action-shielding",
    "guaranteed-self-adaptive-system",
    "incremental-neural-verification-with-proof-reuse",
    "deployment-chain-certificate-propagation",
}

CAPABILITIES = {
    "neural-causal-provenance",
    "admission-distinct-from-certification",
    "exact-action-and-effect",
    "produced-succession",
    "exact-forgetting",
    "all-futures-preservation",
    "pre-effect-refusal",
    "local-certificate-reuse",
}

SOURCE_DECLARATIONS = {
    "RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean": (
        "learnedInitialCheckedAgent",
        "learnedInitialCertifiedRuntime",
        "LearnedAlignedOperationalContract",
        "submitUpdate_learned_aligned_exact",
        "submitUpdate_learned_bypass_rejected",
    ),
    "RelationalPerimeter/Agents/Neural/LearnedUpdateSeparation.lean": (
        "alignedUpdate",
        "bypassUpdate",
        "AdmittedIndependentLearnedIntent",
    ),
    "RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean": (
        "learnedRuntimeDeclaredCurrentDomain",
        "learnedOperationalCounterfactualRequests",
        "learnedOperationalFutureDivergence",
        "everyLearnedRuntimeCurrentVerifierAgrees",
    ),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_COMPARISON_PROTOCOL_V4_ERROR: {message}")


def validate_protocol(protocol: dict) -> None:
    if protocol.get("protocol_id") != "constitutive-neural-capability-comparison-v4":
        raise ValueError("wrong protocol id")
    if protocol.get("status") != "frozen-before-adapter-implementation":
        raise ValueError("protocol is not frozen before adapter implementation")
    if protocol.get("confirmatory_results_present") is not False:
        raise ValueError("the pre-confirmatory protocol contains a result claim")
    if protocol.get("confirmatory_run_permitted") is not False:
        raise ValueError("the protocol permits a run before adapter freeze")
    if {item["id"] for item in protocol.get("baselines", [])} != BASELINES:
        raise ValueError("the six baseline interfaces changed")
    if any(item.get("adapter_contract_status") != "frozen" or
           item.get("adapter_implementation_status") !=
           "required-before-confirmatory-run" or
           item.get("execution_status") != "not-run"
           for item in protocol["baselines"]):
        raise ValueError("a baseline claims implementation or execution before adapter freeze")
    if set(protocol.get("capabilities", [])) != CAPABILITIES:
        raise ValueError("the eight capability columns changed")
    if protocol["shared_material"].get("current_domain_cardinality") != 4:
        raise ValueError("the declared current domain is not the exact four-case domain")
    if protocol["shared_material"].get("future_request_cardinality") != 1:
        raise ValueError("the future discriminator is not the exact nonempty singleton")
    if protocol["release_gate"].get("required_adapter_count") != 6:
        raise ValueError("the release gate no longer requires all six adapters")


def self_test(protocol: dict) -> None:
    validate_protocol(protocol)
    mutations = []
    for name, mutate in (
        ("premature-result", lambda item: item.__setitem__(
            "confirmatory_results_present", True)),
        ("premature-run", lambda item: item.__setitem__(
            "confirmatory_run_permitted", True)),
        ("missing-baseline", lambda item: item["baselines"].pop()),
        ("wrong-current-domain", lambda item: item["shared_material"].__setitem__(
            "current_domain_cardinality", 8)),
        ("empty-future", lambda item: item["shared_material"].__setitem__(
            "future_request_cardinality", 0)),
    ):
        changed = copy.deepcopy(protocol)
        mutate(changed)
        mutations.append((name, changed))
    for name, changed in mutations:
        try:
            validate_protocol(changed)
        except ValueError:
            continue
        raise ValueError(f"negative self-test survived: {name}")
    print(f"NEURAL_COMPARISON_PROTOCOL_V4_SELFTEST_OK mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if arguments.self_test:
        self_test(protocol)
        return
    validate_protocol(protocol)

    forbidden_results = EXPERIMENT / "comparison-results.json"
    if forbidden_results.exists():
        fail("a result file exists before the adapter manifest and run")

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("manifest_id") != \
            "constitutive-neural-capability-comparison-manifest-v4":
        fail("wrong manifest id")
    if manifest.get("status") != "pre-confirmatory-inputs-frozen":
        fail("manifest does not describe frozen pre-confirmatory inputs")
    required_paths = [PROTOCOL, SCHEMA, README, Path(__file__).resolve()]
    required_paths += [ROOT / path for path in SOURCE_DECLARATIONS]
    required_paths += [
        ROOT / "experiments/constitutive-neural-alignment/v1/learned-artifact.json",
        ROOT / "experiments/constitutive-neural-alignment/v1/training-data.json",
    ]
    expected_names = {str(path.relative_to(ROOT)).replace("\\", "/")
                      for path in required_paths}
    if set(manifest.get("files", {})) != expected_names:
        fail("manifest file set differs from the frozen comparison inputs")
    for path in required_paths:
        relative = str(path.relative_to(ROOT)).replace("\\", "/")
        if manifest["files"][relative] != digest(path):
            fail(f"hash mismatch: {relative}")

    for relative, declarations in SOURCE_DECLARATIONS.items():
        source = (ROOT / relative).read_text(encoding="utf-8")
        missing = [name for name in declarations if name not in source]
        if missing:
            fail(f"{relative} lacks declarations: {', '.join(missing)}")

    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    if schema.get("$id") != "constitutive-neural-capability-comparison-result-v4":
        fail("wrong result schema id")
    row = schema["properties"]["rows"]
    if row.get("minItems") != 6 or row.get("maxItems") != 6:
        fail("result schema does not require exactly six rows")
    covered_baselines = {
        clause["contains"]["properties"]["baseline_id"]["const"]
        for clause in row.get("allOf", [])
        if clause.get("minContains") == 1 and clause.get("maxContains") == 1
    }
    if covered_baselines != BASELINES:
        fail("result schema does not require each baseline exactly once")
    row_properties = row["items"]["properties"]
    if set(row_properties["baseline_id"].get("enum", [])) != BASELINES:
        fail("result schema baseline ids differ from the protocol")
    capability_shape = row_properties["capabilities"]
    if set(capability_shape.get("required", [])) != CAPABILITIES:
        fail("result schema capability columns differ from the protocol")
    if capability_shape.get("additionalProperties") is not False:
        fail("result schema admits undeclared capability columns")

    gate = Path(__file__).name
    for portal in (SH_PORTAL, PS_PORTAL):
        if gate not in portal.read_text(encoding="utf-8"):
            fail(f"{portal.name} does not execute {gate}")

    print("NEURAL_COMPARISON_PROTOCOL_V4_OK baselines=6 capabilities=8 "
          "current=4 future=1 results=false")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        fail(str(error))
