#!/usr/bin/env python3
"""Run the single frozen v9 comparison without selecting or overwriting rows."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from typing import Any, Dict, List


ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v9"
RAW_OUTPUT = EXPERIMENT / "comparison-results.ndjson"
RESULT_RECORD = EXPERIMENT / "result-record.json"
CHECKER = ROOT / "scripts/check-neural-joint-protocol-v9.py"
PROTOCOL_ID = "constitutive-neural-joint-capability-comparison-v9"
ADAPTER_COMMAND = ["lake", "exe", "compiled_neural_comparison_adapters"]
EXPECTED_ADAPTERS = [
    "extensional-current-behavior-verification",
    "fixed-network-interventional-causal-analysis",
    "pre-execution-action-shielding",
    "guaranteed-self-adaptive-system",
    "incremental-neural-verification-with-proof-reuse",
    "deployment-chain-certificate-propagation",
]
REQUIRED_FIELDS = {
    EXPECTED_ADAPTERS[0]: {"current_cases", "tables_equal"},
    EXPECTED_ADAPTERS[1]: {
        "aligned_authorization_dependency", "bypass_authorization_dependency"
    },
    EXPECTED_ADAPTERS[2]: {"aligned_decision", "bypass_decision"},
    EXPECTED_ADAPTERS[3]: {
        "aligned_submission", "bypass_submission", "contracts_preserved"
    },
    EXPECTED_ADAPTERS[4]: {
        "aligned_submission", "bypass_submission",
        "transported_structural_fragments", "recomputed_structural_fragments",
        "reuse_claimed"
    },
    EXPECTED_ADAPTERS[5]: {
        "accepted_transitions", "all_steps_checked", "contracts_preserved",
        "bypass_rejected_at_source"
    },
}


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_JOINT_CONFIRMATORY_V9_ERROR: {message}")


def run_checked(command: List[str]) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            check=False)
    if result.returncode != 0:
        details = result.stderr.strip() or result.stdout.strip()
        fail(f"command failed ({' '.join(command)}): {details}")
    return result


def resolve_lake() -> str:
    found = shutil.which("lake")
    if found:
        return found
    suffix = "lake.exe" if sys.platform == "win32" else "lake"
    fallback = Path.home() / ".elan" / "bin" / suffix
    if fallback.is_file():
        return str(fallback)
    fail("lake is unavailable")


def parse_rows(raw: str) -> List[Dict[str, Any]]:
    lines = raw.splitlines()
    if len(lines) != 6 or any(not line.strip() for line in lines):
        fail(f"expected exactly six nonempty NDJSON rows, found {len(lines)}")
    rows: List[Dict[str, Any]] = []
    for index, line in enumerate(lines):
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            fail(f"row {index + 1} is not JSON: {error}")
        if not isinstance(row, dict):
            fail(f"row {index + 1} is not an object")
        adapter = row.get("adapter_id")
        if adapter != EXPECTED_ADAPTERS[index]:
            fail(f"row {index + 1} has wrong adapter: {adapter}")
        missing = REQUIRED_FIELDS[adapter] - set(row)
        if missing:
            fail(f"row {index + 1} lacks fields: {sorted(missing)}")
        rows.append(row)
    return rows


def main() -> None:
    if RAW_OUTPUT.exists() or RESULT_RECORD.exists():
        fail("a reserved v9 result already exists; outputs are immutable")

    status = run_checked(["git", "status", "--porcelain"]).stdout
    if status:
        fail("repository working tree is not clean")
    commit = run_checked(["git", "rev-parse", "HEAD"]).stdout.strip()
    if len(commit) != 40 or any(char not in "0123456789abcdef" for char in commit):
        fail("repository HEAD is not a full lowercase commit SHA")

    run_checked([sys.executable, str(CHECKER)])
    lake = resolve_lake()
    actual_command = [lake, *ADAPTER_COMMAND[1:]]
    produced = run_checked(actual_command)
    rows = parse_rows(produced.stdout)

    raw_bytes = ("\n".join(
        json.dumps(row, separators=(",", ":"), sort_keys=False)
        for row in rows
    ) + "\n").encode("utf-8")
    raw_digest = hashlib.sha256(raw_bytes).hexdigest()
    lean_version = run_checked([lake, "env", "lean", "--version"]).stdout.strip()
    record = {
        "protocol_id": PROTOCOL_ID,
        "repository_commit": commit,
        "environment": {
            "platform": platform.platform(),
            "python": platform.python_version(),
            "lean": lean_version,
        },
        "command": ADAPTER_COMMAND,
        "raw_output_path": RAW_OUTPUT.relative_to(ROOT).as_posix(),
        "rows": rows,
        "raw_output_sha256": raw_digest,
    }

    # Write only after all six rows and the environment have validated.  The
    # exclusive modes make reruns and post-observation replacement impossible.
    with RAW_OUTPUT.open("xb") as stream:
        stream.write(raw_bytes)
    with RESULT_RECORD.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(record, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    print(f"NEURAL_JOINT_CONFIRMATORY_V9_COMPLETE commit={commit} "
          f"rows=6 raw_sha256={raw_digest}")


if __name__ == "__main__":
    main()
