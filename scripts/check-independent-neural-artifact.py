#!/usr/bin/env python3
"""Reproduce the frozen learner and reject protocol or artifact drift."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments" / "constitutive-neural-alignment" / "v1"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
DATA = EXPERIMENT / "training-data.json"
ARTIFACT = EXPERIMENT / "learned-artifact.json"
MANIFEST = EXPERIMENT / "manifest.json"
LEAN = ROOT / "RelationalPerimeter" / "Agents" / "Neural" / "IndependentLearnedArtifact.lean"
GENERATOR = ROOT / "scripts" / "train-independent-neural-artifact.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"INDEPENDENT_ARTIFACT_ERROR: {message}")


def main() -> None:
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if protocol.get("status") != "frozen-before-confirmatory-experiment":
        fail("protocol is not frozen in its pre-confirmatory state")
    if protocol.get("confirmatory_results_present") is not False:
        fail("pre-confirmatory protocol contains a result claim")
    expected_baselines = {
        "extensional-current-behavior-verification",
        "fixed-network-interventional-causal-analysis",
        "pre-execution-action-shielding",
        "guaranteed-self-adaptive-system",
        "incremental-neural-verification-with-proof-reuse",
        "deployment-chain-certificate-propagation",
    }
    observed_baselines = {item["id"] for item in protocol.get("baselines", [])}
    if observed_baselines != expected_baselines:
        fail("baseline matrix differs from the frozen six-class protocol")

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    paths = {
        "comparison-protocol.json": PROTOCOL,
        "training-data.json": DATA,
        "scripts/train-independent-neural-artifact.py": GENERATOR,
        "learned-artifact.json": ARTIFACT,
        "RelationalPerimeter/Agents/Neural/IndependentLearnedArtifact.lean": LEAN,
    }
    for name, path in paths.items():
        if manifest["files"].get(name) != digest(path):
            fail(f"hash mismatch for {name}")

    with tempfile.TemporaryDirectory(prefix="relational-perimeter-learned-") as temporary:
        temporary = Path(temporary)
        reproduced_artifact = temporary / "learned-artifact.json"
        reproduced_lean = temporary / "IndependentLearnedArtifact.lean"
        reproduced_manifest = temporary / "manifest.json"
        command = [
            sys.executable, str(GENERATOR),
            "--protocol", str(PROTOCOL),
            "--data", str(DATA),
            "--artifact", str(reproduced_artifact),
            "--lean", str(reproduced_lean),
            "--manifest", str(reproduced_manifest),
        ]
        subprocess.run(command, cwd=ROOT, check=True)
        for expected, reproduced in [
            (ARTIFACT, reproduced_artifact),
            (LEAN, reproduced_lean),
            (MANIFEST, reproduced_manifest),
        ]:
            if expected.read_bytes() != reproduced.read_bytes():
                fail(f"reproduction differs for {expected.name}")

    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    if len(artifact.get("networks", [])) != 3:
        fail("artifact series does not contain two successive transformations")
    if artifact.get("manual_weight_edits") is not False:
        fail("artifact reports manual weight editing")
    if any(len(network["outputs"]) < 3 for network in artifact["networks"]):
        fail("artifact lacks the three frozen observations")
    data = json.loads(DATA.read_text(encoding="utf-8"))
    expected = [sample["targets"] for sample in data["samples"]]
    for revision in ("initial", "revision_one", "revision_two"):
        observed = [row[revision] for row in artifact["domain_outputs"]]
        if observed != expected:
            fail(f"learned {revision} readout differs from the complete declared domain")
    if [len(network["neurons"]) for network in artifact["networks"]] != [6, 7, 8]:
        fail("successive transformations do not extend the learned causal graph")
    if not any(row["initial"][0] != row["initial"][2]
               for row in artifact["domain_outputs"]):
        fail("authorization-sensitive and bypass observations never separate")
    print("INDEPENDENT_ARTIFACT_OK baselines=6 networks=3 samples=8 confirmatory=false")


if __name__ == "__main__":
    main()
