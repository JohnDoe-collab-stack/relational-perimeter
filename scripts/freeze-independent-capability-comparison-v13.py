#!/usr/bin/env python3
"""Freeze v13 at a clean, pushed source commit before confirmation."""

from __future__ import annotations

import json
from pathlib import Path

from independent_capability_snapshot_v13 import (
    ROOT, build_snapshot, canonical_digest, digest, git, require,
)


EXPERIMENT = ROOT / "experiments/constitutive-neural-alignment/v13"
PROTOCOL = EXPERIMENT / "comparison-protocol.json"
SNAPSHOT = EXPERIMENT / "frozen-snapshot.json"


def main() -> None:
    require(not git("status", "--porcelain"), "working tree is not clean")
    require(not SNAPSHOT.exists(), "frozen snapshot already exists")
    protocol = json.loads(PROTOCOL.read_text(encoding="utf-8"))
    require(protocol.get("status") == "draft-awaiting-stable-source-commit",
            "protocol is not a draft")
    commit = git("rev-parse", "HEAD")
    upstream = git("rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}")
    require(commit == git("rev-parse", upstream),
            "source commit is not the exact pushed upstream revision")
    remote_name = upstream.split("/", 1)[0]
    remote_url = git("remote", "get-url", remote_name)
    snapshot = build_snapshot(commit, remote_url, upstream)
    SNAPSHOT.write_text(json.dumps(snapshot, indent=2) + "\n", encoding="utf-8")

    protocol["status"] = "frozen-before-confirmatory-run"
    protocol["confirmatory_run_permitted"] = True
    protocol["frozen_source_commit"] = commit
    protocol["frozen_source_git_tree"] = snapshot["source_tree"]
    protocol["frozen_source_remote_url"] = remote_url
    protocol["frozen_source_remote_ref"] = upstream
    protocol["frozen_snapshot"] = SNAPSHOT.relative_to(ROOT).as_posix()
    protocol["frozen_snapshot_sha256"] = digest(SNAPSHOT.read_bytes())
    protocol["protocol_sha256"] = canonical_digest(protocol, "protocol_sha256")
    PROTOCOL.write_text(json.dumps(protocol, indent=2) + "\n", encoding="utf-8")
    print("INDEPENDENT_CAPABILITY_COMPARISON_V13_FROZEN "
          f"source={commit} material={len(snapshot['material_sha256'])} "
          f"lean_closure={len(snapshot['lean_import_closure'])}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError,
            json.JSONDecodeError) as error:
        raise SystemExit(
            f"INDEPENDENT_CAPABILITY_COMPARISON_V13_FREEZE_ERROR: {error}")
