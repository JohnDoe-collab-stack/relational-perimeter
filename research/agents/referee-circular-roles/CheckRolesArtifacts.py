"""Independent exact anchor/hash check; not a proof checker or Lean build."""
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[3]
snapshot_path = root / "labyrinth/evidence/roles-source-snapshot.json"
assert snapshot_path.is_file(), "Roles snapshot explicitly must exist"
snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
assert len(snapshot["files"]) == 47, "Expected 47 frozen paths"
assert snapshot["branch"] == "codex/positive-circular-foundations"
assert snapshot["commit"] == "8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685"
assert snapshot["working_tree"] is True
assert snapshot["hash_mode"] == "sha256-lf-normalized"
assert snapshot["revision_mode"] == "frozen-sources-base-ancestor"
paths = [entry["path"] for entry in snapshot["files"]]
assert len(paths) == len(set(paths)), "Duplicate frozen source paths"
for entry in snapshot["files"]:
    source = root / entry["path"]
    assert source.is_file(), entry["path"]
    actual = hashlib.sha256(source.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
    assert actual == entry["sha256"], f"Changed frozen source: {entry['path']}"
print("47 explicitly existing frozen sources match all current CRLF-only-normalized SHA256 fingerprints.")
role_pattern = re.compile(r"/(CircularRoles|HistoricalRoleBridge|CircularRoleTransport)[^/]*\.lean$")
modules = [entry for entry in snapshot["files"] if role_pattern.search(entry["path"])]
assert len(modules) == 5
assert sum(len(entry["audit_declarations"]) for entry in modules) == 109
print("Five canonical role modules contain 109 frozen audit declarations.")

knowledge = json.loads((root / "labyrinth/knowledge.json").read_text(encoding="utf-8"))
sota = json.loads((root / "labyrinth/sota.json").read_text(encoding="utf-8"))
rows = {row["id"]: row for row in sota["entries"]}
ids = {node["id"] for node in knowledge["nodes"]}
nodes = [node for node in knowledge["nodes"] if node["kind"] == "theorem" and
         any(role_pattern.search(ref["file"]) for ref in node.get("lean_refs", []))]
assert nodes, "No role theorem nodes; map is not ready"
anchor_count = 0
for node in nodes:
    assert node["tier"] == "T2" and node["review"]["state"] == "refereed", node["id"]
    assert rows[node["id"]]["result"] == node["statement"], node["id"]
    for ref in node["lean_refs"]:
        text = (root / ref["file"]).read_text(encoding="utf-8-sig")
        assert text.splitlines()[ref["line"] - 1].strip() == ref["anchor"].strip(), ref
        assert ref["declaration"] in re.findall(r"^#print axioms (\S+)", text, re.M), ref
        anchor_count += 1
    for path in node.get("evidence", []):
        assert path.startswith(("http:", "https:")) or (root / path).exists(), path
    for link in node.get("links", []):
        assert link["to"] in ids, link
    print(f"{node['id']}: exact audited anchors, T2 review, evidence, link targets and SOTA text agree.")
print(f"{len(nodes)} role T2 nodes / {anchor_count} exact audited anchors checked; semantic review is separate.")
question = next(node for node in knowledge["nodes"] if node["id"] == "q.equipped-final-role")
assert rows[question["id"]]["result"] == question["statement"]
print("Equipped-final-role question and SOTA statement agree; scope reviewed manually.")
