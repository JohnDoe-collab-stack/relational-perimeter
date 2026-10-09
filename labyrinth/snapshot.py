"""Record the source boundary of the foundational map; never alter source files."""
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HASH_MODE = "sha256-lf-normalized"
REVISION_MODE = "frozen-sources-base-ancestor"
FILES = [
    "SegmentedResidualRole.lean", "AbstractSegmentedTurning.lean",
    "ExactTypeTransport.lean", "StrongPerimetralTurning.lean",
    "RelationalPerimeter.lean", "docs/relations-primitives-constitution-perimetre.fr.md",
    "docs/primitive-relations-and-perimeter-constitution.en.md",
    "docs/positionnement-et-portee.fr.md", "docs/positioning-and-scope.en.md",
    "docs/plan-reconstruction-fondations-relationnelles.fr.md",
    "lean-toolchain", "lakefile.toml",
    "README.md", "Tests/PublicRootImport.lean",
    "RelationalPerimeter/Constitution.lean",
    "RelationalPerimeter/Constitution/Primitives.lean",
    "RelationalPerimeter/Constitution/PositivePresentation.lean",
    "RelationalPerimeter/Constitution/CircularPresentationBridge.lean",
    "RelationalPerimeter/Constitution/BoundaryTransport.lean",
    "RelationalPerimeter/Constitution/Examples.lean",
    "docs/circularite-positive-et-transports-frontiere.fr.md",
    "docs/positive-circularity-and-boundary-transports.en.md",
    "RelationalPerimeter/Constitution/ClosingBoundary.lean",
    "RelationalPerimeter/Constitution/ClosingBoundaryExamples.lean",
    "docs/frontiere-sans-jonction-choisie.fr.md",
    "docs/plan-suite-fondations-positives.fr.md",
    "RelationalPerimeter/Constitution/PositiveGeneration.lean",
    "RelationalPerimeter/Constitution/PositiveGenerationBridge.lean",
    "RelationalPerimeter/Constitution/PositiveGenerationExamples.lean",
    "docs/formation-et-generation-positives.fr.md",
    "RelationalPerimeter/Constitution/SignatureTransport.lean",
    "RelationalPerimeter/Constitution/SpineTransport.lean",
    "RelationalPerimeter/Constitution/FormationTransport.lean",
    "RelationalPerimeter/Constitution/ClosingTransport.lean",
    "RelationalPerimeter/Constitution/SignatureTransportExamples.lean",
    "RelationalPerimeter/Constitution/FormationTransportExamples.lean",
    "RelationalPerimeter/Constitution/ClosingTransportExamples.lean",
    "docs/transports-signature-et-formation.fr.md",
    "RelationalPerimeter/Constitution/CircularRoles.lean",
    "RelationalPerimeter/Constitution/HistoricalRoleBridge.lean",
    "RelationalPerimeter/Constitution/CircularRoleTransport.lean",
    "RelationalPerimeter/Constitution/CircularRolesExamples.lean",
    "RelationalPerimeter/Constitution/CircularRoleTransportExamples.lean",
    "docs/classification-roles-equipes.fr.md",
    "labyrinth/snapshot.py", "labyrinth/check_foundations.py", "labyrinth/rebuild.ps1",
]

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()

def source_hash(raw):
    # Git may normalize CRLF on commit/checkout. All other bytes remain covered.
    return hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest()

def validate_revision(baseline, current):
    if baseline["branch"] != current["branch"]:
        raise ValueError("Branch changed: obtain a new source review.")
    if baseline.get("hash_mode") != current.get("hash_mode"):
        raise ValueError("Hash format changed: obtain a new source snapshot/review.")
    if baseline["commit"] == current["commit"]:
        return
    if baseline.get("revision_mode") != REVISION_MODE:
        raise ValueError("Revision changed without frozen-source publication mode.")
    ancestry = subprocess.run(["git", "merge-base", "--is-ancestor",
                               baseline["commit"], current["commit"]], cwd=ROOT)
    if ancestry.returncode != 0:
        raise ValueError("Current revision is not a descendant of the reviewed base.")
    # The caller must still compare every frozen source hash. Ancestry alone is
    # insufficient and does not extend the mathematical review to changed code.

def verify_tree(baseline, revision):
    commit = git("rev-parse", "--verify", revision + "^{commit}")
    current = {"branch": git("branch", "--show-current"), "commit": commit,
               "hash_mode": HASH_MODE}
    validate_revision(baseline, current)
    for record in baseline["files"]:
        raw = subprocess.check_output(["git", "show", commit + ":" + record["path"]], cwd=ROOT)
        if source_hash(raw) != record["sha256"]:
            raise ValueError("Committed source differs: " + record["path"])
    print(f'Committed tree verified: {len(baseline["files"])} frozen sources at {commit}.')

def snapshot():
    records = []
    for name in FILES:
        path = ROOT / name
        raw = path.read_bytes()
        tracked = subprocess.run(["git", "ls-files", "--error-unmatch", name],
                                 cwd=ROOT, capture_output=True).returncode == 0
        record = {"path": name, "sha256": source_hash(raw),
                  "tracked": tracked, "bytes": len(raw)}
        if name.endswith(".lean"):
            record["audit_declarations"] = re.findall(
                r"^#print axioms (\S+)", raw.decode("utf-8-sig"), re.M)
        records.append(record)
    return {"recorded_at": datetime.now(timezone.utc).isoformat(),
            "branch": git("branch", "--show-current"), "commit": git("rev-parse", "HEAD"),
            "working_tree": True,
            "hash_mode": HASH_MODE, "revision_mode": REVISION_MODE,
            "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "files": records}

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--verify-tree", metavar="REVISION")
    args = parser.parse_args()
    target = ROOT / "labyrinth/evidence/roles-source-snapshot.json"
    current = snapshot()
    if args.verify_tree:
        verify_tree(json.loads(target.read_text(encoding="utf-8")), args.verify_tree)
        raise SystemExit(0)
    if args.verify:
        old = json.loads(target.read_text(encoding="utf-8"))
        validate_revision(old, current)
        old_files = {f["path"]: f["sha256"] for f in old["files"]}
        new_files = {f["path"]: f["sha256"] for f in current["files"]}
        differences = [path for path in sorted(old_files.keys() | new_files.keys())
                       if old_files.get(path) != new_files.get(path)]
        if differences:
            raise SystemExit("Sources changed: " + ", ".join(differences))
        print(f"Source snapshot verified: {len(current['files'])} unchanged files.")
    else:
        if target.exists():
            raise SystemExit("Snapshot exists; use --verify or archive it before a new iteration.")
        target.write_text(json.dumps(current, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"Recorded {len(current['files'])} files at {current['commit']}.")
