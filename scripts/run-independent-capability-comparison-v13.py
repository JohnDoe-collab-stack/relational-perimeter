#!/usr/bin/env python3
"""Execute the frozen v13 comparison and semantic controls exactly once."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

from independent_capability_snapshot_v13 import validate_snapshot


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v13"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
RAW = EXPERIMENT / "comparison-results.ndjson"
RECORD = EXPERIMENT / "result-record.json"
ABLATION_RESULTS = EXPERIMENT / "ablation-results.json"
SNAPSHOT = EXPERIMENT / "frozen-snapshot.json"
CHECKER = ROOT / "scripts/check-independent-capability-comparison-v13.py"
CODEGEN = ROOT / "scripts/check-independent-comparison-codegen.py"
ABLATIONS = ROOT / "scripts/run-independent-capability-ablations-v13.py"
LEDGER = EXPERIMENT / "evidence-ledger.json"
COMMAND = ["lake", "-K", 'moreLeanArgs=["-M=8192"]', "exe",
           "compiled_independent_complete_neural_comparison"]
BUILD = ["lake", "-K", 'moreLeanArgs=["-M=8192"]', "build",
         "compiled_independent_complete_neural_comparison"]
REFERENCE_AUDIT = ["lake", "env", "lean", "-M", "8192",
                   "Tests/Mechanisms/NeuralIndependentCapabilityComparisonRegression.lean"]


def fail(message: str) -> None:
    raise SystemExit(f"INDEPENDENT_CAPABILITY_COMPARISON_V13_RUN_ERROR: {message}")


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            encoding="utf-8", check=False)
    if result.returncode != 0:
        fail(result.stderr.strip() or result.stdout.strip() or
             f"command failed: {' '.join(command)}")
    return result


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def exclusive(path: Path, data: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(data)


def main() -> None:
    if RAW.exists() or RECORD.exists() or ABLATION_RESULTS.exists():
        fail("reserved outputs already exist and are immutable")
    if run(["git", "status", "--porcelain"]).stdout:
        fail("working tree is not clean")
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if (protocol.get("status") != "frozen-before-confirmatory-run" or
            protocol.get("confirmatory_run_permitted") is not True):
        fail("protocol is not frozen and permitted")
    run([sys.executable, str(CHECKER)])
    snapshot = json.loads(SNAPSHOT.read_text(encoding="utf-8"))
    validate_snapshot(snapshot, check_worktree=True)
    execution_commit = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    run(["git", "merge-base", "--is-ancestor", execution_commit,
         snapshot["remote_ref"]])

    lake = shutil.which("lake")
    if lake is None:
        suffix = "lake.exe" if sys.platform == "win32" else "lake"
        candidate = Path.home() / ".elan/bin" / suffix
        if not candidate.is_file():
            fail("lake is unavailable")
        lake = str(candidate)

    build = [lake, *BUILD[1:]]
    built = run(build)
    build_output = built.stdout + built.stderr
    if ("warning:" in build_output or "depends on axioms:" in build_output or
            "sorryAx" in build_output):
        fail("memory-bounded build contains a warning or axiom-audit failure")
    reference_audit = [lake, *REFERENCE_AUDIT[1:]]
    audited = run(reference_audit)
    audit_output = audited.stdout + audited.stderr
    if ("warning:" in audit_output or "depends on axioms:" in audit_output or
            "sorryAx" in audit_output):
        fail("reference audit contains a warning or axiom-audit failure")
    run([sys.executable, str(CODEGEN)])

    with tempfile.TemporaryDirectory(prefix="independent-capability-v13-") as temporary:
        temporary_root = Path(temporary)
        temporary_ablations = temporary_root / "ablation-results.json"
        run([sys.executable, str(ABLATIONS), "--lake", lake,
             "--output", str(temporary_ablations)])
        ablation_document = json.loads(
            temporary_ablations.read_text(encoding="utf-8"))
        ablation_document["results"].append({
            "probe": "P7",
            "mutation": "transitive audited-verdict injection",
            "gate": "scripts/check-independent-comparison-codegen.py",
            "outcome": "rejected",
        })
        ablation_bytes = (json.dumps(ablation_document, indent=2) + "\n").encode("utf-8")

    produced = run([lake, *COMMAND[1:]])
    lines = produced.stdout.splitlines()
    if len(lines) != 9 or any(not line.strip() for line in lines):
        fail("executable did not emit exactly nine rows")
    rows = [json.loads(line) for line in lines]
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    emitted_fields = ledger["emitted_fields"]
    for index, (row, method, translations) in enumerate(zip(
            rows, protocol["methods"], protocol["translation_counts"],
            strict=True)):
        if row.get("method_id") != method:
            fail(f"wrong method at emitted row {index + 1}")
        if row.get("translation_count") != translations:
            fail(f"wrong translation count at emitted row {index + 1}")
        expected = {"method_id", "translation_count"} | set(
            emitted_fields[method])
        if set(row) != expected:
            fail(f"unmapped or missing field at emitted row {index + 1}")
    raw_bytes = ("\n".join(json.dumps(row, separators=(",", ":"))
                            for row in rows) + "\n").encode("utf-8")
    validate_snapshot(snapshot, check_worktree=True)
    current = execution_commit
    record = {
        "protocol_id": protocol["protocol_id"],
        "repository_commit": current,
        "frozen_source_commit": protocol["frozen_source_commit"],
        "frozen_source_tree": protocol["frozen_source_git_tree"],
        "snapshot_sha256": protocol["frozen_snapshot_sha256"],
        "protocol_sha256": protocol["protocol_sha256"],
        "environment": {
            "platform": platform.platform(),
            "python": platform.python_version(),
            "lean": run([lake, "env", "lean", "--version"]).stdout.strip(),
        },
        "command": COMMAND,
        "build_command": BUILD,
        "reference_audit_command": REFERENCE_AUDIT,
        "rows": rows,
        "raw_output_sha256": digest(raw_bytes),
        "ablation_results": ablation_document["results"],
        "ablation_output_sha256": digest(ablation_bytes),
    }
    record_bytes = (json.dumps(record, indent=2) + "\n").encode("utf-8")
    exclusive(RAW, raw_bytes)
    exclusive(ABLATION_RESULTS, ablation_bytes)
    exclusive(RECORD, record_bytes)
    print("INDEPENDENT_CAPABILITY_COMPARISON_V13_COMPLETE "
          f"evidence_commit={current} source={protocol['frozen_source_commit']} "
          f"rows=9 ablations={len(ablation_document['results'])}")


if __name__ == "__main__":
    main()
