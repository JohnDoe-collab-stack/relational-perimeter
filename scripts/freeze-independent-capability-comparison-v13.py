#!/usr/bin/env python3
"""Freeze v13 after an authorized stable source commit and before its run."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PROTOCOL = ROOT / "experiments/constitutive-neural-alignment/v13/comparison-protocol.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*arguments: str) -> str:
    result = subprocess.run(["git", *arguments], cwd=ROOT, capture_output=True,
                            text=True, encoding="utf-8", check=False)
    if result.returncode != 0:
        raise SystemExit("INDEPENDENT_CAPABILITY_COMPARISON_V13_FREEZE_ERROR: git failed")
    return result.stdout.strip()


def main() -> None:
    if git("status", "--porcelain"):
        raise SystemExit("INDEPENDENT_CAPABILITY_COMPARISON_V13_FREEZE_ERROR: working tree is not clean")
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if protocol.get("status") != "draft-awaiting-stable-source-commit":
        raise SystemExit("INDEPENDENT_CAPABILITY_COMPARISON_V13_FREEZE_ERROR: protocol is not a draft")
    sources = [
        "RelationalPerimeter/Agents/Neural/CapabilityComparisonAdapters.lean",
        "RelationalPerimeter/Agents/Neural/CompleteCapabilityComparison.lean",
        "RelationalPerimeter/Agents/Neural/IndependentCapabilityComparison.lean",
        "Tests/Executables/CompiledIndependentCompleteNeuralComparison.lean",
        "Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean",
        "scripts/check-independent-comparison-codegen.py",
        "scripts/check-independent-capability-comparison-v13.py",
        "scripts/run-independent-capability-comparison-v13.py",
        "scripts/expected-failures.tsv",
        "scripts/stratification.tsv",
        "experiments/constitutive-neural-alignment/v13/evidence-ledger.json",
        "experiments/constitutive-neural-alignment/v13/capability-matrix.json",
        "experiments/constitutive-neural-alignment/v13/success-criteria.json",
        "experiments/constitutive-neural-alignment/v13/result-schema.json",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain"
    ]
    protocol["status"] = "frozen-before-confirmatory-run"
    protocol["frozen_source_commit"] = git("rev-parse", "HEAD")
    protocol["frozen_source_git_tree"] = git("rev-parse", "HEAD^{tree}")
    protocol["source_sha256"] = {
        relative: digest(ROOT / relative) for relative in sources
    }
    PROTOCOL.write_text(json.dumps(protocol, indent=2) + "\n", encoding="utf-8")
    print("INDEPENDENT_CAPABILITY_COMPARISON_V13_FROZEN "
          f"source={protocol['frozen_source_commit']}")


if __name__ == "__main__":
    main()
