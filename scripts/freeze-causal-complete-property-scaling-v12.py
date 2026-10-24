#!/usr/bin/env python3
"""Freeze v12 after an authorized stable commit and before any confirmatory run."""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
PROTOCOL = ROOT / "experiments/constitutive-neural-alignment/v12/scaling-protocol.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*arguments: str) -> str:
    result = subprocess.run(["git", *arguments], cwd=ROOT, text=True,
                            encoding="utf-8", capture_output=True, check=False)
    if result.returncode != 0:
        raise SystemExit("CAUSAL_COMPLETE_PROPERTY_SCALING_V12_FREEZE_ERROR: git failed")
    return result.stdout.strip()


def tree_files() -> list[Path]:
    files = sorted((ROOT / "RelationalPerimeter").rglob("*.lean"))
    files.extend(sorted((ROOT / "Tests").rglob("*.lean")))
    files.extend((ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                  ROOT / "lean-toolchain"))
    return files


def tree_digest(files: list[Path]) -> str:
    state = hashlib.sha256()
    for path in sorted(files):
        relative = path.relative_to(ROOT).as_posix().encode("utf-8")
        payload = path.read_bytes()
        state.update(len(relative).to_bytes(8, "big"))
        state.update(relative)
        state.update(len(payload).to_bytes(8, "big"))
        state.update(payload)
    return state.hexdigest()


def main() -> None:
    if git("status", "--porcelain"):
        raise SystemExit(
            "CAUSAL_COMPLETE_PROPERTY_SCALING_V12_FREEZE_ERROR: working tree is not clean")
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if protocol.get("status") != "draft-awaiting-stable-source-commit":
        raise SystemExit(
            "CAUSAL_COMPLETE_PROPERTY_SCALING_V12_FREEZE_ERROR: protocol is not a draft")
    sources = (
        ROOT / "scripts/run-compiled-causal-complete-property-scaling-v12.py",
        ROOT / "scripts/check-causal-complete-property-scaling-v12.py",
        ROOT / "scripts/check-agent-codegen.py",
        Path(__file__).resolve(),
        ROOT / "scripts/run-compiled-complete-property-scaling-v11.py",
        ROOT / "scripts/check-complete-property-scaling-v11.py",
        ROOT / "RelationalPerimeter/Agents/Neural/CausalParameterizedCompiledCheckerFamily.lean",
        ROOT / "RelationalPerimeter/Agents/Neural/CausalCompletePropertyScalingMeasurement.lean",
        ROOT / "Tests/Executables/CompiledCausalCompletePropertyNeuralScaling.lean",
        ROOT / "Tests/Mechanisms/NeuralCausalCompletePropertyScalingRegression.lean",
        ROOT / "Tests/ExpectedFailure/CausalScalingProductionCannotMoveToForeignSource.lean.fail",
        ROOT / "Tests/ExpectedFailure/CausalScalingProductionCannotChangeCommand.lean.fail",
        ROOT / "Tests/ExpectedFailure/CausalScalingActionCannotReplaceProposalRequest.lean.fail",
        ROOT / "scripts/expected-failures.tsv", ROOT / "scripts/stratification.tsv",
        ROOT / "lakefile.toml", ROOT / "lake-manifest.json", ROOT / "lean-toolchain",
    )
    files = tree_files()
    protocol["status"] = "frozen-before-confirmatory-run"
    protocol["frozen_source_commit"] = git("rev-parse", "HEAD")
    protocol["frozen_source_git_tree"] = git("rev-parse", "HEAD^{tree}")
    protocol["source_tree_file_count"] = len(files)
    protocol["source_tree_sha256"] = tree_digest(files)
    protocol["runner_sha256"] = digest(sources[0])
    protocol["source_sha256"] = {
        path.relative_to(ROOT).as_posix(): digest(path) for path in sources
    }
    PROTOCOL.write_text(json.dumps(protocol, indent=2) + "\n", encoding="utf-8")
    print("CAUSAL_COMPLETE_PROPERTY_SCALING_V12_FROZEN "
          f"source={protocol['frozen_source_commit']}")


if __name__ == "__main__":
    main()
