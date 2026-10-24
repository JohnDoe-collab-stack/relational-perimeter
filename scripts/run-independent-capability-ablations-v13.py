#!/usr/bin/env python3
"""Run the exact semantic negative controls authorized for comparison v13."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent.parent
ABLATIONS = ROOT / "experiments/constitutive-neural-alignment/v13/authorized-ablations.json"
REGISTRY = ROOT / "scripts/expected-failures.tsv"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def registry() -> dict[str, tuple[int, int, str, str]]:
    rows: dict[str, tuple[int, int, str, str]] = {}
    for line in REGISTRY.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        require(len(fields) == 6, "invalid expected-failure registry")
        path, _category, line_number, column, needle, obligation = fields
        rows[path] = (int(line_number), int(column), needle, obligation)
    return rows


def diagnostics(output: str) -> list[dict]:
    records: list[dict] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        require(record.get("severity") != "warning", "unexpected Lean warning")
        if record.get("severity") == "error":
            records.append(record)
    return records


def run_fixture(lake: str, fixture: str,
                expected: tuple[int, int, str, str]) -> dict:
    line, column, needle, obligation = expected
    result = subprocess.run(
        [lake, "env", "lean", "-M", "8192", "--json", fixture], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8", timeout=90,
        check=False)
    require(result.returncode == 1, f"fixture did not fail normally: {fixture}")
    errors = diagnostics(result.stdout + result.stderr)
    require(len(errors) == 1, f"fixture has non-exact error count: {fixture}")
    error = errors[0]
    path = str(error.get("fileName", "")).replace("\\", "/")
    if Path(path).is_absolute():
        path = Path(path).resolve().relative_to(ROOT.resolve()).as_posix()
    require(path.removeprefix("./") == fixture,
            f"fixture failed in another file: {fixture}")
    require(error.get("pos") == {"line": line, "column": column},
            f"fixture failed at another site: {fixture}")
    require(needle in error.get("data", ""),
            f"fixture failed for another reason: {fixture}")
    return {"fixture": fixture, "obligation": obligation, "outcome": "rejected"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output")
    arguments = parser.parse_args()
    specification = json.loads(ABLATIONS.read_text(encoding="utf-8"))
    registered = registry()
    results = []
    for row in specification["ablations"]:
        fixture = row.get("fixture")
        if fixture is None:
            continue
        require(fixture in registered, f"fixture is not registered: {fixture}")
        result = run_fixture(arguments.lake, fixture, registered[fixture])
        result["probe"] = row["probe"]
        result["mutation"] = row["mutation"]
        results.append(result)
    output = {"campaign_id": specification["campaign_id"], "results": results}
    if arguments.output:
        path = Path(arguments.output)
        require(not path.exists(), "ablation output already exists")
        path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError,
            json.JSONDecodeError, subprocess.TimeoutExpired) as error:
        raise SystemExit(f"INDEPENDENT_CAPABILITY_ABLATION_V13_ERROR: {error}")
