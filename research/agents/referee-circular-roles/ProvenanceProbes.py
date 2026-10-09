"""Independent small provenance diagnostics; no repository or Git mutation."""
import hashlib
import importlib.util
import ast
import json
import sys
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("reviewed_snapshot", root / "labyrinth/snapshot.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

count = 0

def check(condition, label):
    global count
    assert condition, label
    count += 1
    print("PASS:", label)

def rejected(action, label):
    try:
        action()
    except ValueError:
        check(True, label)
    else:
        raise AssertionError(label)

check(module.source_hash(b"a\r\nb\r\n") == module.source_hash(b"a\nb\n"),
      "CRLF and LF give the same explicitly normalized fingerprint")
check(module.source_hash(b"a\rb\n") != module.source_hash(b"a\nb\n"),
      "standalone CR is covered, not silently normalized")
check(module.source_hash(b"a \nb\n") != module.source_hash(b"a\nb\n"),
      "whitespace changes other than CRLF are detected")
check(module.source_hash(b"a\nb\n") != module.source_hash(b"a\nc\n"),
      "changed source token is detected")
check(module.source_hash(b"\xef\xbb\xbfa\n") != module.source_hash(b"a\n"),
      "UTF-8 BOM is covered")
check(module.source_hash(b"a\r\n") == hashlib.sha256(b"a\n").hexdigest(),
      "hash algorithm is SHA256 of exactly CRLF-replaced bytes")

base = {"branch": "codex/positive-circular-foundations", "commit": "old",
        "hash_mode": module.HASH_MODE, "revision_mode": module.REVISION_MODE}
current = {"branch": base["branch"], "commit": "new", "hash_mode": module.HASH_MODE}
rejected(lambda: module.validate_revision(base, {**current, "branch": "another"}),
         "branch change rejected")
rejected(lambda: module.validate_revision(base, {**current, "hash_mode": "raw"}),
         "hash mode change rejected")
rejected(lambda: module.validate_revision({k: v for k, v in base.items() if k != "revision_mode"}, current),
         "different commit without explicit frozen-source mode rejected")
with patch.object(module.subprocess, "run", return_value=SimpleNamespace(returncode=1)):
    rejected(lambda: module.validate_revision(base, current), "non-descendant revision rejected")
with patch.object(module.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as ancestry:
    module.validate_revision(base, current)
    check(ancestry.call_args.args[0][-2:] == ["old", "new"],
          "descendant mode checks the reviewed base against current full commit")
with patch.object(module.subprocess, "run", side_effect=AssertionError("unexpected ancestry call")):
    module.validate_revision(base, {**current, "commit": "old"})
    check(True, "unchanged base still requires matching branch and hash mode")

tree_base = {**base, "files": [{"path": "source.lean", "sha256": module.source_hash(b"token\n")}]}
def fake_git(*args):
    return "new" if args[0] == "rev-parse" else base["branch"]

with patch.object(module, "git", side_effect=fake_git), \
     patch.object(module.subprocess, "run", return_value=SimpleNamespace(returncode=0)), \
     patch.object(module.subprocess, "check_output", return_value=b"token\r\n") as read_tree:
    with redirect_stdout(StringIO()):
        module.verify_tree(tree_base, "HEAD")
    check(read_tree.call_args.args[0] == ["git", "show", "new:source.lean"],
          "tree verification reads the resolved committed blob and accepts only newline normalization")

with patch.object(module, "git", side_effect=fake_git), \
     patch.object(module.subprocess, "run", return_value=SimpleNamespace(returncode=0)), \
     patch.object(module.subprocess, "check_output", return_value=b"changed-token\n"):
    rejected(lambda: module.verify_tree(tree_base, "HEAD"),
             "ancestor and same branch do not bypass changed committed source hash")

# Execute the actual CLI guard with synthetic snapshots and a mocked read.
# This checks that the frozen source boundary cannot silently shrink or grow.
parsed = ast.parse((root / "labyrinth/snapshot.py").read_text(encoding="utf-8"))
main_guard = next(node for node in parsed.body if isinstance(node, ast.If))
cli_code = compile(ast.Module(body=[main_guard], type_ignores=[]), "reviewed-snapshot-cli", "exec")

def run_verify_cli(baseline_files, current_files):
    baseline = {**base, "files": baseline_files}
    current_snapshot = {**base, "files": current_files}
    namespace = {**module.__dict__, "__name__": "__main__", "snapshot": lambda: current_snapshot}
    with patch.object(sys, "argv", ["snapshot.py", "--verify"]), \
         patch.object(Path, "read_text", return_value=json.dumps(baseline)), \
         redirect_stdout(StringIO()):
        try:
            exec(cli_code, namespace)
        except SystemExit as error:
            return str(error)
    return None

record_a = {"path": "a.lean", "sha256": "hash-a"}
record_b = {"path": "b.lean", "sha256": "hash-b"}
check(run_verify_cli([record_a, record_b], [record_a]) == "Sources changed: b.lean",
      "CLI rejects a frozen baseline file removed from current FILES")
check(run_verify_cli([record_a], [record_a, record_b]) == "Sources changed: b.lean",
      "CLI rejects an added file outside the frozen baseline")
check(run_verify_cli([record_a], [record_a]) is None,
      "CLI accepts exactly the same full frozen path/hash dictionary")

print(f"{count} independent provenance diagnostics passed; ancestry and tree content were simulated without Git mutation.")
