#!/usr/bin/env python3
"""Validate the frozen final mutation campaign and scaling evidence."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CAMPAIGN = ROOT / "experiments/constitutive-neural-alignment/v2/final-negative-mutations.json"
PROTOCOL = ROOT / "experiments/constitutive-neural-alignment/v2/scaling-protocol.json"
RESULTS = ROOT / "experiments/constitutive-neural-alignment/v2/scaling-results.json"
RUNNER = ROOT / "scripts/run-neural-update-scaling.py"
MANIFEST = ROOT / "experiments/constitutive-neural-alignment/v2/manifest.json"
V3_PROTOCOL = ROOT / "experiments/constitutive-neural-alignment/v3/scaling-protocol.json"
V3_RESULTS = ROOT / "experiments/constitutive-neural-alignment/v3/scaling-results.json"
V3_RUNNER = ROOT / "scripts/run-neural-update-scaling-v3.py"
V3_MANIFEST = ROOT / "experiments/constitutive-neural-alignment/v3/manifest.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def deterministic(row: dict) -> dict:
    return {key: value for key, value in row.items() if not key.endswith("_time_ns_median")}


def verify_scaling(protocol_path: Path, results_path: Path,
                   runner_path: Path, manifest_path: Path,
                   require_local_work: bool) -> list[dict]:
    protocol = json.loads(protocol_path.read_text(encoding="utf-8"))
    results = json.loads(results_path.read_text(encoding="utf-8"))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    for relative, expected in manifest["files"].items():
        if sha256(ROOT / relative) != expected:
            raise ValueError(f"manifest hash mismatch: {relative}")
    if protocol["script_sha256"] != sha256(runner_path):
        raise ValueError("scaling runner differs from frozen protocol")
    if results["protocol_sha256"] != sha256(protocol_path):
        raise ValueError("results are not tied to the frozen protocol")
    if results["script_sha256"] != sha256(runner_path):
        raise ValueError("results are not tied to the frozen runner")
    if results["command"] != manifest["confirmatory_command"]:
        raise ValueError("recorded command differs from the manifest")
    if [row["network_size"] for row in results["rows"]] != protocol["sizes"]:
        raise ValueError("result sizes differ from frozen sizes")
    for row in results["rows"]:
        if not row["verdicts_equal"] or not row["target_well_formed"]:
            raise ValueError("incremental and complete verification disagree")
        if row["same_property"] != "serialized-native-system-well-formed":
            raise ValueError("the compared property changed")
        if row["affected_cone_size"] != protocol["affected_cone_size"]:
            raise ValueError("the affected cone changed")
        if row["reused_fragments"] + row["recomputed_fragments"] != row["network_size"]:
            raise ValueError("fragment accounting is incomplete")
        if row["incremental_checked_units"] >= row["complete_checked_units"]:
            raise ValueError("incremental deterministic work was not reduced")
        if require_local_work and row["incremental_checked_units"] > 3 * row["affected_cone_size"]:
            raise ValueError("incremental work is not bounded by the local cone")
    return results["rows"]


def main() -> None:
    campaign = json.loads(CAMPAIGN.read_text(encoding="utf-8"))
    if [case["id"] for case in campaign["mutations"]] != [
        "remove-authorization-edge", "substitute-context",
        "substitute-requirement", "short-circuit-prior-system",
        "post-hoc-constant-transformer", "zero-weight-edge",
        "pre-erase-history", "independent-successor-reconstruction"]:
        raise ValueError("final mutation campaign does not cover the frozen eight obligations")
    inventory_rows = {}
    for row in (ROOT / "scripts/expected-failures.tsv").read_text(encoding="utf-8").splitlines():
        if row.strip() and not row.startswith("#"):
            fields = row.split("\t")
            if len(fields) == 6:
                inventory_rows[fields[0]] = fields
    for case in campaign["mutations"]:
        fixture = case["fixture"]
        if not (ROOT / fixture).is_file() or fixture not in inventory_rows:
            raise ValueError(f"mutation fixture is not enforced: {fixture}")
        if not case["scientific_role"].strip() or not case["expected_diagnostic"].strip():
            raise ValueError(f"mutation metadata is incomplete: {case['id']}")
        if inventory_rows[fixture][4] != case["expected_diagnostic"]:
            raise ValueError(f"mutation diagnostic differs from exact gate: {fixture}")
    verify_scaling(PROTOCOL, RESULTS, RUNNER, MANIFEST, False)
    final_rows = verify_scaling(V3_PROTOCOL, V3_RESULTS, V3_RUNNER, V3_MANIFEST, True)
    print(f"FINAL_NEURAL_CAMPAIGN_OK mutations={len(campaign['mutations'])} "
          f"sizes={len(final_rows)} property=serialized-native-system-well-formed "
          "local_reuse=v3")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        raise SystemExit(f"FINAL_NEURAL_CAMPAIGN_FAILED: {error}")
