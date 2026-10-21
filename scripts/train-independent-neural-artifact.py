#!/usr/bin/env python3
"""Deterministically learn and emit the independent neural artifact series."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def learn_neuron(rows: list[list[int]], targets: list[int]) -> dict[str, object]:
    count = 0
    for weights in itertools.product((-2, -1, 1, 2), repeat=len(rows[0])):
        for bias in range(-3, 4):
            for level in range(-3, 4):
                count += 1
                outputs = [int(level <= sum(v * w for v, w in zip(row, weights)) + bias)
                           for row in rows]
                if outputs == targets:
                    return {"weights": list(weights), "bias": bias,
                            "threshold": level, "candidate_count": count}
    raise RuntimeError("fixed search domain contains no exact neuron")


def serialized(sources: list[tuple[str, int]], learned: dict[str, object]) -> dict[str, object]:
    return {
        "inputs": [{"source": {"kind": kind, "index": index}, "weight": weight}
                   for (kind, index), weight in zip(sources, learned["weights"])],
        "bias": learned["bias"],
        "threshold": learned["threshold"],
    }


def outputs(rows: list[list[int]], learned: dict[str, object]) -> list[int]:
    return [int(learned["threshold"] <=
                sum(v * w for v, w in zip(row, learned["weights"])) + learned["bias"])
            for row in rows]


def train(data: dict[str, object]) -> dict[str, object]:
    samples = data["samples"]
    inputs = [sample["inputs"] for sample in samples]
    target_rows = [sample["targets"] for sample in samples]
    requirement = [row[0] for row in inputs]
    context = [row[1] for row in inputs]
    authorization_input = [row[2] for row in inputs]
    aligned = [row[0] for row in target_rows]
    authorization = [row[1] for row in target_rows]
    bypass = [row[2] for row in target_rows]
    stages: list[dict[str, object]] = []

    def add(name: str, sources: list[tuple[str, int]], rows: list[list[int]],
            targets: list[int]) -> list[int]:
        learned = learn_neuron(rows, targets)
        value = outputs(rows, learned)
        stages.append({"name": name, "serialized": serialized(sources, learned),
                       "candidate_count": learned["candidate_count"]})
        return value

    rc_rows = [[r, c] for r, c in zip(requirement, context)]
    left = add("requirement-and-not-context",
               [("receivedInput", 0), ("receivedInput", 1)], rc_rows,
               [int(r == 1 and c == 0) for r, c in zip(requirement, context)])
    right = add("not-requirement-and-context",
                [("receivedInput", 0), ("receivedInput", 1)], rc_rows,
                [int(r == 0 and c == 1) for r, c in zip(requirement, context)])
    xor_value = add("requirement-xor-context",
                    [("priorNeuron", 0), ("priorNeuron", 1)],
                    [[l, r] for l, r in zip(left, right)], bypass)
    auth_value = add("authorization-observation", [("receivedInput", 2)],
                     [[a] for a in authorization_input], authorization)
    aligned_value = add("authorized-proposal",
                        [("priorNeuron", 2), ("priorNeuron", 3)],
                        [[x, a] for x, a in zip(xor_value, auth_value)], aligned)
    bypass_value = add("authorization-bypass-observation",
                       [("priorNeuron", 0), ("priorNeuron", 1)],
                       [[l, r] for l, r in zip(left, right)], bypass)
    initial = [stage["serialized"] for stage in stages]
    first_value = add("first-successor-aligned-output",
                      [("priorNeuron", 4), ("priorNeuron", 3)],
                      [[v, a] for v, a in zip(aligned_value, auth_value)], aligned)
    first = [stage["serialized"] for stage in stages]
    second_value = add("second-successor-aligned-output",
                       [("priorNeuron", 6), ("priorNeuron", 5)],
                       [[v, b] for v, b in zip(first_value, bypass_value)], aligned)
    second = [stage["serialized"] for stage in stages]
    networks = [
        {"version": "learned-v0", "parent": None, "inputCount": 3,
         "neurons": initial, "outputs": [4, 3, 5]},
        {"version": "learned-v1", "parent": "learned-v0", "inputCount": 3,
         "neurons": first, "outputs": [6, 3, 5]},
        {"version": "learned-v2", "parent": "learned-v1", "inputCount": 3,
         "neurons": second, "outputs": [7, 3, 5]},
    ]
    return {
        "artifact_id": "independent-constitutive-neural-artifact-v1",
        "learning_method": "deterministic-exhaustive-integer-threshold-search",
        "randomness": "none",
        "manual_weight_edits": False,
        "networks": networks,
        "training": [{"name": stage["name"],
                      "candidate_count": stage["candidate_count"]} for stage in stages],
        "domain_outputs": [
            {"sample": sample["name"],
             "initial": [aligned_value[i], auth_value[i], bypass_value[i]],
             "revision_one": [first_value[i], auth_value[i], bypass_value[i]],
             "revision_two": [second_value[i], auth_value[i], bypass_value[i]]}
            for i, sample in enumerate(samples)
        ],
    }


def lint(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lsource(source: dict[str, object]) -> str:
    constructor = "receivedInput" if source["kind"] == "receivedInput" else "priorNeuron"
    return f".{constructor} {source['index']}"


def lneuron(neuron: dict[str, object], typed: bool, indent: str = "      ") -> str:
    edges = [f"{{ source := {lsource(edge['source'])}, weight := {lint(edge['weight'])} }}"
             for edge in neuron["inputs"]]
    threshold = lint(neuron["threshold"])
    if typed:
        threshold = f"⟨{threshold}⟩"
    constructor = "NeuronSpec.mk" if typed else "SerializedNeuron.mk"
    return (constructor + "\n" + indent + "  [" +
            (",\n" + indent + "  ").join(edges) + "]\n" + indent +
            f"  {lint(neuron['bias'])} {threshold}")


def emit_lean(artifact: dict[str, object], hashes: dict[str, str]) -> bytes:
    lines = [
        "import RelationalPerimeter.Agents.Neural.SerializedNativeSystem", "", "/-!",
        "# Independently learned serialized neural artifact", "",
        "This file is generated byte-for-byte by the frozen external learner.",
        "The repository verifier regenerates it and rejects manual edits.", "-/",
        "set_option genInjectivity false", "namespace ConstitutiveSearch.NeuralAgent",
        "open NativeMechanism", "",
        f'def independentLearningProtocolSha256 : String := "{hashes["protocol"]}"',
        f'def independentLearningDataSha256 : String := "{hashes["data"]}"',
        f'def independentLearningGeneratorSha256 : String := "{hashes["generator"]}"',
        f'def independentLearnedArtifactSha256 : String := "{hashes["artifact"]}"', "",
    ]
    names = ["Initial", "FirstSuccessor", "SecondSuccessor"]
    for name, network in zip(names, artifact["networks"]):
        out = ", ".join(str(v) for v in network["outputs"])
        lines += [f"def independentLearned{name}Network : SerializedNetwork :=",
                  f"  {{ inputCount := {network['inputCount']}", "    neurons :=",
                  "      [" + (",\n       ".join(lneuron(n, False) for n in network["neurons"])) + "]",
                  f"    outputs := [{out}] }}", "",
                  f"def independentLearned{name}NetworkAccepted : Bool :=",
                  f"  match decodeArtifact PublicReconfiguredOperationalContract independentLearned{name}Network with",
                  "  | .ok _ => true", "  | .error _ => false", "",
                  f"theorem independentLearned{name}Network_decodes :",
                  f"    independentLearned{name}NetworkAccepted = true := by", "  rfl", "",
                  f"theorem independentLearned{name}NeuronCount :",
                  f"    independentLearned{name}Network.neurons.length = {len(network['neurons'])} := by",
                  "  rfl", ""]
    lines += ["end ConstitutiveSearch.NeuralAgent", "/- AXIOM_AUDIT_BEGIN -/",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearningProtocolSha256",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedInitialNetwork",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedInitialNetwork_decodes",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFirstSuccessorNetwork",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedFirstSuccessorNetwork_decodes",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedSecondSuccessorNetwork",
              "#print axioms ConstitutiveSearch.NeuralAgent.independentLearnedSecondSuccessorNetwork_decodes",
              "/- AXIOM_AUDIT_END -/", ""]
    return "\n".join(lines).encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    for name in ("protocol", "data", "artifact", "lean", "manifest"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    protocol = json.loads(args.protocol.read_text(encoding="utf-8"))
    data = json.loads(args.data.read_text(encoding="utf-8"))
    if protocol["confirmatory_results_present"] is not False:
        raise RuntimeError("the frozen pre-confirmatory protocol cannot contain results")
    artifact = train(data)
    artifact_bytes = canonical_json(artifact)
    args.artifact.parent.mkdir(parents=True, exist_ok=True)
    args.artifact.write_bytes(artifact_bytes)
    hashes = {"protocol": sha256(args.protocol), "data": sha256(args.data),
              "generator": sha256(Path(__file__)),
              "artifact": hashlib.sha256(artifact_bytes).hexdigest()}
    lean_bytes = emit_lean(artifact, hashes)
    args.lean.parent.mkdir(parents=True, exist_ok=True)
    args.lean.write_bytes(lean_bytes)
    manifest = {
        "manifest_id": "independent-constitutive-neural-artifact-manifest-v1",
        "hash_algorithm": "sha256",
        "exact_command": ["python3", "scripts/train-independent-neural-artifact.py",
            "--protocol", "experiments/constitutive-neural-alignment/v1/comparison-protocol.json",
            "--data", "experiments/constitutive-neural-alignment/v1/training-data.json",
            "--artifact", "experiments/constitutive-neural-alignment/v1/learned-artifact.json",
            "--lean", "RelationalPerimeter/Agents/Neural/IndependentLearnedArtifact.lean",
            "--manifest", "experiments/constitutive-neural-alignment/v1/manifest.json"],
        "parameters": {"weight_values": [-2, -1, 1, 2],
                       "bias_range_inclusive": [-3, 3],
                       "threshold_range_inclusive": [-3, 3], "randomness": "none"},
        "provenance": {"data_origin": "locally-defined-synthetic-complete-domain",
                       "external_material": False, "manual_weight_edits": False,
                       "reuse_conditions": "repository-license"},
        "files": {"comparison-protocol.json": hashes["protocol"],
                  "training-data.json": hashes["data"],
                  "scripts/train-independent-neural-artifact.py": hashes["generator"],
                  "learned-artifact.json": hashes["artifact"],
                  "RelationalPerimeter/Agents/Neural/IndependentLearnedArtifact.lean":
                      hashlib.sha256(lean_bytes).hexdigest()}}
    args.manifest.write_bytes(canonical_json(manifest))


if __name__ == "__main__":
    main()
