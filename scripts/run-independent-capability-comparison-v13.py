#!/usr/bin/env python3
"""Execute once the frozen v13 oracle-independent comparison."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v13"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
RAW = EXPERIMENT / "comparison-results.ndjson"
RECORD = EXPERIMENT / "result-record.json"
CHECKER = ROOT / "scripts/check-independent-capability-comparison-v13.py"
COMMAND = ["lake", "exe", "compiled_independent_complete_neural_comparison"]


def fail(message: str) -> None:
    raise SystemExit(f"INDEPENDENT_CAPABILITY_COMPARISON_V13_RUN_ERROR: {message}")


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            encoding="utf-8", check=False)
    if result.returncode != 0:
        fail(result.stderr.strip() or result.stdout.strip() or "command failed")
    return result


def main() -> None:
    if RAW.exists() or RECORD.exists():
        fail("reserved outputs already exist and are immutable")
    if run(["git", "status", "--porcelain"]).stdout:
        fail("working tree is not clean")
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    if protocol.get("status") != "frozen-before-confirmatory-run":
        fail("protocol is not frozen")
    run([sys.executable, str(CHECKER)])
    lake = shutil.which("lake")
    if lake is None:
        suffix = "lake.exe" if sys.platform == "win32" else "lake"
        candidate = Path.home() / ".elan/bin" / suffix
        if not candidate.is_file():
            fail("lake is unavailable")
        lake = str(candidate)
    produced = run([lake, *COMMAND[1:]])
    lines = produced.stdout.splitlines()
    if len(lines) != 9 or any(not line.strip() for line in lines):
        fail("executable did not emit exactly nine rows")
    rows = [json.loads(line) for line in lines]
    raw_bytes = ("\n".join(json.dumps(row, separators=(",", ":"))
                            for row in rows) + "\n").encode("utf-8")
    raw_hash = hashlib.sha256(raw_bytes).hexdigest()
    current = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    record = {
        "protocol_id": protocol["protocol_id"],
        "repository_commit": current,
        "frozen_source_commit": protocol["frozen_source_commit"],
        "environment": {
            "platform": platform.platform(),
            "python": platform.python_version(),
            "lean": run([lake, "env", "lean", "--version"]).stdout.strip()
        },
        "command": COMMAND,
        "rows": rows,
        "raw_output_sha256": raw_hash
    }
    with RAW.open("xb") as stream:
        stream.write(raw_bytes)
    with RECORD.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(record, stream, indent=2)
        stream.write("\n")
    print("INDEPENDENT_CAPABILITY_COMPARISON_V13_COMPLETE "
          f"commit={current} rows=9 raw_sha256={raw_hash}")


if __name__ == "__main__":
    main()
