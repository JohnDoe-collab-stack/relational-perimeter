#!/usr/bin/env python3
"""Transitive local import boundaries using the shared Lean header reader."""
import argparse
from collections import deque
from contextlib import redirect_stdout
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from lean_imports import ImportSyntaxError, imports

ROOT = Path(__file__).resolve().parent.parent


class BoundaryViolation(ValueError):
    pass


def check_graph(source_root, manifest, files):
    root_module, forbidden = None, set()
    for line_number, raw in enumerate(manifest.read_text(encoding="utf-8-sig").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2 or parts[0] not in ("root", "forbidden"):
            raise BoundaryViolation(f"{manifest}:{line_number}: malformed boundary entry")
        if parts[0] == "root":
            if root_module is not None:
                raise BoundaryViolation(f"{manifest}: duplicate root")
            root_module = parts[1]
        else:
            forbidden.add(parts[1])
    if not root_module:
        raise BoundaryViolation(f"{manifest}: missing root entry")
    graph = {}
    for file in files:
        module = file.relative_to(source_root).with_suffix("").as_posix().replace("/", ".")
        graph[module] = imports(file.read_bytes().decode("utf-8-sig"))
    if root_module not in graph:
        raise BoundaryViolation(f"{manifest}: root module '{root_module}' has no local source")
    queue, paths = deque([root_module]), {root_module: [root_module]}
    while queue:
        current = queue.popleft()
        for dependency in graph[current]:
            if dependency in forbidden:
                raise BoundaryViolation("forbidden import path: " + " -> ".join(paths[current] + [dependency]))
            if dependency in graph and dependency not in paths:
                paths[dependency] = paths[current] + [dependency]
                queue.append(dependency)
    print(f"IMPORT_BOUNDARY_OK {root_module}: {len(paths)} reachable local modules")


class SelfTests(unittest.TestCase):
    def test_cli_line_endings(self):
        parsed = subprocess.run([sys.executable, str(ROOT / "scripts/lean_imports.py"), "--stdin"],
                                input=b"import\n A.B\r\nimport C.D\n", capture_output=True, check=False)
        self.assertEqual(parsed.returncode, 0, parsed.stderr)
        self.assertEqual(parsed.stdout, b"A.B\nC.D\n")

    def test_headers(self):
        cases = [
            ("import A.B\n", ["A.B"]),
            ("import\n  A.B\n", ["A.B"]),
            ("/- prefix -/ import A.B\n", ["A.B"]),
            ("import /- nested /- c -/ -/\n A.B\n", ["A.B"]),
            ("-- import Bad\n/- import Bad /- import Worse -/ -/\nimport A\n", ["A"]),
            ("import A import B\n", ["A", "B"]),
            ("import A\ndef text := \"import Bad\"\n", ["A"]),
            ("module\nprelude\npublic import A\nmeta import B\nimport all C\n", ["A", "B", "C"]),
            ("import\r\n  A.B\r\n", ["A.B"]),
        ]
        for source, expected in cases:
            with self.subTest(source=source):
                self.assertEqual(imports(source), expected)
        for source in ("import", "import /- missing", "import «quoted»", "import A.",
                       "import Allowedβ\nimport Forbidden\n", "import Allowed.β\nimport Forbidden\n"):
            with self.assertRaises(ImportSyntaxError):
                imports(source)

    def test_boundaries(self):
        with tempfile.TemporaryDirectory(prefix="rp-import-boundary-") as directory:
            root = Path(directory)
            files = [root / (name + ".lean") for name in ("Root", "Middle", "Forbidden", "Allowed")]
            manifest = root / "boundaries.txt"
            manifest.write_text("root Root\nforbidden Forbidden\n", encoding="utf-8")
            for file in files:
                file.write_text("", encoding="utf-8")
            forms = ("import Forbidden\n", "import\n  Forbidden\n",
                     "/- prefix -/ import Forbidden\n", "import /- between -/ Forbidden\n",
                     "import Allowed import Forbidden\n")
            for form in forms:
                for indirect in (False, True):
                    with self.subTest(form=form, indirect=indirect):
                        files[0].write_text("import Middle\n" if indirect else form, encoding="utf-8")
                        files[1].write_text(form if indirect else "", encoding="utf-8")
                        expected = "Root -> Middle -> Forbidden" if indirect else "Root -> Forbidden"
                        with self.assertRaisesRegex(BoundaryViolation, "^forbidden import path: " + expected + "$"):
                            check_graph(root, manifest, files)
            files[0].write_text("/- import Forbidden -/\nimport Allowed\n", encoding="utf-8")
            files[1].write_text("", encoding="utf-8")
            with redirect_stdout(io.StringIO()):
                check_graph(root, manifest, files)

    def test_unrelated_failures(self):
        with tempfile.TemporaryDirectory(prefix="rp-import-boundary-") as directory:
            root = Path(directory)
            manifest = root / "boundaries.txt"
            manifest.write_text("forbidden Forbidden\n", encoding="utf-8")
            with self.assertRaisesRegex(BoundaryViolation, "missing root"):
                check_graph(root, manifest, [])
            manifest.write_text("root Missing\n", encoding="utf-8")
            with self.assertRaisesRegex(BoundaryViolation, "has no local source"):
                check_graph(root, manifest, [])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="?", default="scripts/import-boundaries.txt")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests))
        if not result.wasSuccessful():
            raise BoundaryViolation("IMPORT_BOUNDARY_SELFTEST_FAILED")
        print("IMPORT_BOUNDARY_SELFTEST_OK: split/commented headers, direct and transitive edges")
        return
    listed = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
                            cwd=ROOT, capture_output=True, encoding="utf-8", check=True)
    files = sorted({ROOT / relative for relative in listed.stdout.splitlines() if (ROOT / relative).is_file()})
    manifest = Path(args.manifest)
    check_graph(ROOT, manifest if manifest.is_absolute() else ROOT / manifest, files)


if __name__ == "__main__":
    try:
        main()
    except (BoundaryViolation, ImportSyntaxError, OSError, UnicodeError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
