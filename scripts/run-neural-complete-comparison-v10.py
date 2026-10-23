#!/usr/bin/env python3
"""Execute once the frozen v10 nine-method comparison."""

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
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v10"
RAW_OUTPUT = EXPERIMENT / "comparison-results.ndjson"
RESULT_RECORD = EXPERIMENT / "result-record.json"
CHECKER = ROOT / "scripts/check-neural-complete-comparison-v10.py"
PROTOCOL_ID = "constitutive-neural-complete-capability-comparison-v10"
COMMAND = ["lake", "exe", "compiled_complete_neural_comparison"]
EXPECTED_METHODS = [
    "extensional-current-behavior-verification",
    "fixed-network-interventional-causal-analysis",
    "pre-execution-action-shielding",
    "guaranteed-self-adaptive-system",
    "incremental-neural-verification-with-proof-reuse",
    "deployment-chain-certificate-propagation",
    "relational-execution-comparison",
    "explicit-reference-combination",
    "independent-complete-recheck",
]
EXPECTED_TRANSLATIONS = [2, 2, 2, 3, 4, 3, 4, 6, 4]
REQUIRED_FIELDS = {
    EXPECTED_METHODS[0]: {"current_cases", "tables_equal"},
    EXPECTED_METHODS[1]: {"aligned_authorization_dependency", "bypass_authorization_dependency"},
    EXPECTED_METHODS[2]: {"aligned_decision", "bypass_decision"},
    EXPECTED_METHODS[3]: {"aligned_submission", "bypass_submission", "contracts_preserved"},
    EXPECTED_METHODS[4]: {"aligned_submission", "bypass_submission", "transported_structural_fragments", "recomputed_structural_fragments", "reuse_claimed"},
    EXPECTED_METHODS[5]: {"accepted_transitions", "all_steps_checked", "contracts_preserved", "bypass_rejected_at_source"},
    EXPECTED_METHODS[6]: {"current_tables_equal", "future_requests", "future_outcomes_different", "aligned_future_satisfies", "bypass_future_satisfies"},
    EXPECTED_METHODS[7]: {"current_tables_equal", "aligned_authorization_dependency", "bypass_authorization_dependency", "aligned_mutation_decision", "bypass_mutation_decision", "aligned_future_satisfies", "bypass_future_satisfies", "aligned_pre_effect_decision", "bypass_pre_effect_decision"},
    EXPECTED_METHODS[8]: {"aligned_decision", "bypass_decision", "successor_matches_incremental", "incremental_verdict_used_as_oracle"},
}


def fail(message: str) -> None:
    raise SystemExit(f"NEURAL_COMPLETE_COMPARISON_V10_ERROR: {message}")


def run_checked(command: List[str]) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            check=False)
    if result.returncode != 0:
        fail(result.stderr.strip() or result.stdout.strip() or
             f"command failed: {' '.join(command)}")
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
    if len(lines) != 9 or any(not line.strip() for line in lines):
        fail(f"expected exactly nine nonempty NDJSON rows, found {len(lines)}")
    rows: List[Dict[str, Any]] = []
    for index, line in enumerate(lines):
        try:
            row = json.loads(line)
        except json.JSONDecodeError as error:
            fail(f"row {index + 1} is not JSON: {error}")
        method = row.get("method_id")
        if method != EXPECTED_METHODS[index]:
            fail(f"row {index + 1} has wrong method: {method}")
        if row.get("translation_count") != EXPECTED_TRANSLATIONS[index]:
            fail(f"row {index + 1} has wrong translation count")
        missing = REQUIRED_FIELDS[method] - set(row)
        if missing:
            fail(f"row {index + 1} lacks fields: {sorted(missing)}")
        rows.append(row)
    return rows


def main() -> None:
    if RAW_OUTPUT.exists() or RESULT_RECORD.exists():
        fail("a reserved v10 result already exists; outputs are immutable")
    status = run_checked(["git", "status", "--porcelain"]).stdout
    if status:
        fail("repository working tree is not clean")
    commit = run_checked(["git", "rev-parse", "HEAD"]).stdout.strip()
    if len(commit) != 40 or any(char not in "0123456789abcdef" for char in commit):
        fail("repository HEAD is not a stable full commit")
    run_checked([sys.executable, str(CHECKER)])
    lake = resolve_lake()
    produced = run_checked([lake, *COMMAND[1:]])
    rows = parse_rows(produced.stdout)
    raw_bytes = ("\n".join(json.dumps(row, separators=(",", ":"))
                            for row in rows) + "\n").encode("utf-8")
    raw_digest = hashlib.sha256(raw_bytes).hexdigest()
    record = {
        "protocol_id": PROTOCOL_ID,
        "repository_commit": commit,
        "environment": {
            "platform": platform.platform(),
            "python": platform.python_version(),
            "lean": run_checked([lake, "env", "lean", "--version"]).stdout.strip(),
        },
        "command": COMMAND,
        "raw_output_path": RAW_OUTPUT.relative_to(ROOT).as_posix(),
        "rows": rows,
        "raw_output_sha256": raw_digest,
    }
    with RAW_OUTPUT.open("xb") as stream:
        stream.write(raw_bytes)
    with RESULT_RECORD.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(record, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    print(f"NEURAL_COMPLETE_COMPARISON_V10_COMPLETE commit={commit} "
          f"rows=9 raw_sha256={raw_digest}")


if __name__ == "__main__":
    main()

