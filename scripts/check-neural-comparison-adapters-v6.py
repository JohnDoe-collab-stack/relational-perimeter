#!/usr/bin/env python3
"""Validate the content-frozen, not-yet-run capability adapters v6."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v6"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
ADAPTER_MANIFEST = EXPERIMENT / "adapter-manifest.json"
SCHEMA = EXPERIMENT / "comparison-result-schema.json"
README = EXPERIMENT / "README.md"
MANIFEST = EXPERIMENT / "manifest.json"
ADAPTER_SOURCE = ROOT / "RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean"
ENTRYPOINT = ROOT / "Tests/Executables/CompiledNeuralComparisonAdapters.lean"
LAKEFILE = ROOT / "lakefile.toml"
SH_PORTAL = ROOT / "scripts/verify.sh"
PS_PORTAL = ROOT / "scripts/verify.ps1"

BASELINES = {
    "extensional-current-behavior-verification":
        "runExtensionalCurrentBehaviorAdapter",
    "fixed-network-interventional-causal-analysis":
        "runFixedNetworkInterventionalAdapter",
    "pre-execution-action-shielding":
        "runPreExecutionActionShieldAdapter",
    "guaranteed-self-adaptive-system":
        "runGuaranteedSelfAdaptiveAdapter",
    "incremental-neural-verification-with-proof-reuse":
        "runIncrementalProofReuseAdapter",
    "deployment-chain-certificate-propagation":
        "runDeploymentChainPropagationAdapter",
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

FROZEN_PATHS = (
    "experiments/constitutive-neural-alignment/v6/comparison-protocol.json",
    "experiments/constitutive-neural-alignment/v6/adapter-manifest.json",
    "experiments/constitutive-neural-alignment/v6/comparison-result-schema.json",
    "experiments/constitutive-neural-alignment/v6/README.md",
    "scripts/check-neural-comparison-adapters-v6.py",
    "RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean",
    "Tests/Executables/CompiledNeuralComparisonAdapters.lean",
    "RelationalPerimeter/Agents/Neural/LearnedRuntimeAdapter.lean",
    "RelationalPerimeter/Agents/Neural/LearnedUpdateSeparation.lean",
    "RelationalPerimeter/Agents/Neural/LearnedContractFutureDivergence.lean",
    "experiments/constitutive-neural-alignment/v1/learned-artifact.json",
    "experiments/constitutive-neural-alignment/v1/training-data.json",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_COMPARISON_ADAPTERS_V6_ERROR: {message}")


def validate_protocol(protocol: dict) -> None:
    if protocol.get("protocol_id") != "constitutive-neural-capability-comparison-v6":
        raise ValueError("wrong protocol id")
    if protocol.get("status") != "adapters-frozen-before-confirmatory-run":
        raise ValueError("protocol is not adapter-frozen")
    if protocol.get("confirmatory_results_present") is not False:
        raise ValueError("pre-confirmatory protocol contains a result claim")
    if protocol.get("confirmatory_run_permitted") is not False:
        raise ValueError("run is permitted before a stable commit is recorded")
    baselines = protocol.get("baselines", [])
    if {item.get("id") for item in baselines} != set(BASELINES):
        raise ValueError("the six baseline interfaces changed")
    for item in baselines:
        if item.get("adapter_contract_status") != "frozen":
            raise ValueError(f"unfrozen adapter contract: {item.get('id')}")
        if item.get("adapter_implementation_status") != "frozen":
            raise ValueError(f"unfrozen adapter implementation: {item.get('id')}")
        if item.get("execution_status") != "not-run":
            raise ValueError(f"premature adapter execution: {item.get('id')}")
        expected = "ConstitutiveSearch.NeuralAgent." + BASELINES[item["id"]]
        if item.get("adapter_declaration") != expected:
            raise ValueError(f"wrong declaration for {item['id']}")
    if set(protocol.get("capabilities", [])) != CAPABILITIES:
        raise ValueError("the eight capability columns changed")
    material = protocol.get("shared_material", {})
    if material.get("current_domain_cardinality") != 4:
        raise ValueError("wrong current-domain cardinality")
    if material.get("future_request_cardinality") != 1:
        raise ValueError("wrong future-request cardinality")
    if material.get("typed_material") != \
            "ConstitutiveSearch.NeuralAgent.frozenNeuralComparisonMaterial":
        raise ValueError("shared typed material changed")
    release = protocol.get("release_gate", {})
    if release.get("required_adapter_count") != 6:
        raise ValueError("release gate no longer requires six adapters")
    if release.get("raw_output_format") != "six-line-ndjson":
        raise ValueError("raw output format changed")


def self_test(protocol: dict) -> None:
    validate_protocol(protocol)
    mutations = []
    for name, mutate in (
        ("premature-result", lambda item: item.__setitem__(
            "confirmatory_results_present", True)),
        ("premature-run", lambda item: item.__setitem__(
            "confirmatory_run_permitted", True)),
        ("missing-adapter", lambda item: item["baselines"].pop()),
        ("adapter-not-frozen", lambda item: item["baselines"][0].__setitem__(
            "adapter_implementation_status", "required-before-run")),
        ("adapter-already-run", lambda item: item["baselines"][0].__setitem__(
            "execution_status", "completed")),
        ("wrong-domain", lambda item: item["shared_material"].__setitem__(
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
    print(f"NEURAL_COMPARISON_ADAPTERS_V6_SELFTEST_OK mutations={len(mutations)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    arguments = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if arguments.self_test:
        self_test(protocol)
        return
    validate_protocol(protocol)

    if (EXPERIMENT / "comparison-results.json").exists():
        fail("a result file exists before the permitted confirmatory run")

    adapters = json.loads(ADAPTER_MANIFEST.read_text(encoding="utf-8"))
    if adapters.get("adapter_manifest_id") != \
            "constitutive-neural-capability-adapters-v6":
        fail("wrong adapter manifest id")
    if adapters.get("status") != "content-frozen-not-run":
        fail("adapter manifest is not frozen and unexecuted")
    if adapters.get("confirmatory_execution") is not False:
        fail("adapter manifest claims a confirmatory execution")
    if adapters.get("command") != ["lake", "exe", "compiled_neural_comparison_adapters"]:
        fail("compiled adapter command changed")
    adapter_rows = adapters.get("adapters", [])
    if {item.get("id") for item in adapter_rows} != set(BASELINES):
        fail("adapter manifest does not contain the exact six interfaces")
    for item in adapter_rows:
        expected = "ConstitutiveSearch.NeuralAgent." + BASELINES[item["id"]]
        if item.get("declaration") != expected:
            fail(f"wrong adapter declaration: {item['id']}")

    source = ADAPTER_SOURCE.read_text(encoding="utf-8")
    runner = ENTRYPOINT.read_text(encoding="utf-8")
    for baseline, declaration in BASELINES.items():
        if f"def {declaration}" not in source:
            fail(f"missing Lean adapter declaration: {declaration}")
        if f'\\"adapter_id\\":\\"{baseline}\\"' not in runner:
            fail(f"compiled runner omits adapter id: {baseline}")
    if "FrozenNeuralComparisonAdapterBundle" not in source:
        fail("six adapters are not bundled over one typed material")
    if "noLearnedReuseClaim" not in source or "reuse_claimed\\\":false" not in runner:
        fail("learned adapter hides its zero-reuse boundary")
    if "compiled_neural_comparison_adapters" not in LAKEFILE.read_text(encoding="utf-8"):
        fail("compiled adapter executable is absent from lakefile.toml")

    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    if schema.get("$id") != "constitutive-neural-capability-comparison-result-v6":
        fail("wrong result schema id")
    if schema["properties"]["protocol_id"].get("const") != protocol["protocol_id"]:
        fail("result schema points to another protocol")
    rows = schema["properties"]["rows"]
    if rows.get("minItems") != 6 or rows.get("maxItems") != 6:
        fail("result schema does not require exactly six rows")
    if set(rows["items"]["properties"]["baseline_id"].get("enum", [])) != set(BASELINES):
        fail("result schema baseline ids differ")
    capability_shape = rows["items"]["properties"]["capabilities"]
    if set(capability_shape.get("required", [])) != CAPABILITIES:
        fail("result schema capability columns differ")

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("manifest_id") != \
            "constitutive-neural-capability-comparison-manifest-v6":
        fail("wrong frozen-input manifest id")
    if manifest.get("status") != "adapters-content-frozen-not-run":
        fail("frozen-input manifest has the wrong status")
    expected_paths = set(FROZEN_PATHS)
    if set(manifest.get("files", {})) != expected_paths:
        fail("frozen-input manifest file set differs")
    for relative in FROZEN_PATHS:
        if manifest["files"].get(relative) != digest(ROOT / relative):
            fail(f"hash mismatch: {relative}")

    adapter_files = adapters.get("files", {})
    expected_adapter_files = {
        "RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean",
        "Tests/Executables/CompiledNeuralComparisonAdapters.lean",
    }
    if set(adapter_files) != expected_adapter_files:
        fail("adapter source file set differs")
    for relative in expected_adapter_files:
        if adapter_files[relative] != digest(ROOT / relative):
            fail(f"adapter hash mismatch: {relative}")

    gate = Path(__file__).name
    for portal in (SH_PORTAL, PS_PORTAL):
        portal_text = portal.read_text(encoding="utf-8")
        if gate not in portal_text:
            fail(f"{portal.name} does not execute {gate}")

    historical = json.loads((ROOT /
        "experiments/constitutive-neural-alignment/v4/comparison-protocol.json"
    ).read_text(encoding="utf-8"))
    if historical.get("status") != "frozen-before-adapter-implementation":
        fail("historical v4 protocol was rewritten")

    print("NEURAL_COMPARISON_ADAPTERS_V6_OK adapters=6 capabilities=8 "
          "command=frozen results=false run=false")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        fail(str(error))
