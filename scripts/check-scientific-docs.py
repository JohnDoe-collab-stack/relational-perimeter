#!/usr/bin/env python3
"""Read-only claim/proof freshness checks; never a semantic or novelty verdict.

Only stdlib. Source fingerprints cover local import closures, not minimal term
dependencies. Lean clients resolve cited declarations after the existing build.
"""
import argparse
from contextlib import redirect_stdout
from functools import lru_cache
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import unquote, urlsplit

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
REGISTRY = "docs/scientific-claims.json"
CONFIG = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
SHA = re.compile(r"[0-9a-f]{64}")
REV = re.compile(r"[0-9a-f]{40}")


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def fields(value, keys, context):
    require(isinstance(value, dict) and set(value) == set(keys),
            f"SCHEMA: {context}: expected fields {sorted(keys)}")


def prose(value, context):
    require(isinstance(value, str) and bool(value.strip()), f"SCHEMA: empty {context}")


def digest(text):
    return hashlib.sha256(text.replace("\r\n", "\n").encode("utf-8")).hexdigest()


def safe_path(root, relative):
    require(isinstance(relative, str) and bool(relative) and "\\" not in relative,
            f"PATH: invalid relative path {relative!r}")
    path = PurePosixPath(relative)
    require(not path.is_absolute() and not re.match(r"^[A-Za-z]:", relative)
            and not any(part in ("..", ".") for part in relative.split("/"))
            and not any(part == "" for part in relative.split("/")),
            f"PATH: forbidden path {relative!r}")
    resolved = (root / relative).resolve()
    require(resolved.is_relative_to(root.resolve()), f"PATH: escapes root {relative!r}")
    return resolved


def read_current(root, path):
    target = safe_path(root, path)
    require(target.is_file(), f"MISSING: {path}")
    return target.read_bytes().decode("utf-8").replace("\r\n", "\n")


def git_text(root, revision, path):
    safe_path(root, path)
    result = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=root,
                            capture_output=True, check=False)
    require(result.returncode == 0, f"SNAPSHOT: missing {path} at {revision}")
    return result.stdout.decode("utf-8").replace("\r\n", "\n")


def outside_fences(text):
    result, fence = [], None
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence):
                fence = None
            result.append("\n")
        elif marker:
            fence = marker[1]
            result.append("\n")
        else:
            result.append(line)
    return "".join(result)


def headings(text):
    # Offsets stay aligned even though fenced lines are blanked for recognition.
    result, offset, fence = [], 0, None
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence):
                fence = None
        elif marker:
            fence = marker[1]
        else:
            match = re.match(r"^ {0,3}(#{1,6})\s+(.+?)\s*#*\s*$", line.rstrip("\n"))
            if match:
                result.append((match[2], offset, offset + len(line)))
        offset += len(line)
    return result


def passage(text, anchor):
    entries = headings(text)
    matches = [i for i, entry in enumerate(entries) if entry[0] == anchor["heading"]]
    require(len(matches) == 1, f"ANCHOR: missing or ambiguous heading {anchor['heading']!r}")
    index = matches[0]
    end = entries[index + 1][1] if index + 1 < len(entries) else len(text)
    body = text[entries[index][2]:end].strip("\n")
    paragraph = anchor["paragraph"]
    if paragraph is not None:
        parts = re.split(r"\n[ \t]*\n", body)
        require(1 <= paragraph <= len(parts), f"ANCHOR: paragraph {paragraph} missing")
        body = parts[paragraph - 1]
    require(bool(body.strip()), f"ANCHOR: empty passage {anchor['heading']!r}")
    return body


def validate_anchor(root, anchor, reader):
    fields(anchor, ("path", "heading", "paragraph", "sha256"), "anchor")
    safe_path(root, anchor["path"])
    require(anchor["path"].endswith(".md"), "SCHEMA: anchor must be Markdown")
    prose(anchor["heading"], "heading")
    require(anchor["paragraph"] is None or
            (type(anchor["paragraph"]) is int and anchor["paragraph"] > 0), "SCHEMA: paragraph")
    require(isinstance(anchor["sha256"], str) and SHA.fullmatch(anchor["sha256"]), "SCHEMA: anchor hash")
    content = reader(anchor["path"])
    require(digest(passage(content, anchor)) == anchor["sha256"],
            f"STALE_TEXT: {anchor['path']} / {anchor['heading']} / {anchor['paragraph']}")


def lean_code(text):
    """Remove nested comments and strings before reading the import header."""
    output, index, depth = [], 0, 0
    quoted = False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif quoted:
            if char == "\\":
                output.extend("  ")
                index += 2
            else:
                quoted = char != '"'
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            output.extend(" " * (end - index))
            index = end
        elif char == '"':
            quoted = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    require(depth == 0 and not quoted, "IMPORT_PARSE: unclosed comment/string")
    return "".join(output)


@lru_cache(maxsize=None)
def imports(text):
    tokens = re.findall(NAME.pattern + r"|[^\s]", lean_code(text))
    result, index = [], 0
    stops = {"import", "module", "prelude", "public", "private", "meta", "namespace",
             "section", "end", "open", "set_option", "def", "theorem", "abbrev", "instance",
             "structure", "inductive", "opaque", "example", "attribute", "export", "deriving",
             "universe", "variable", "noncomputable", "macro", "syntax", "elab", "initialize"}
    while index < len(tokens):
        if tokens[index] in ("module", "prelude"):
            index += 1
            continue
        start = index
        while index < len(tokens) and tokens[index] in ("public", "private", "meta"):
            index += 1
        if index >= len(tokens) or tokens[index] != "import":
            break
        index += 1
        first = index
        while index < len(tokens) and tokens[index] not in stops and NAME.fullmatch(tokens[index]):
            result.append(tokens[index])
            index += 1
        require(index > first, f"IMPORT_PARSE: empty import at token {start}")
    return result


def module_path(module):
    require(isinstance(module, str) and NAME.fullmatch(module), f"SCHEMA: module {module!r}")
    return module.replace(".", "/") + ".lean"


def source_fingerprint(root, claim, reader):
    paths = set(CONFIG) | set(claim["checks"])
    visited = set()

    def visit(module):
        path = module_path(module)
        if path in visited:
            return
        visited.add(path)
        paths.add(path)
        for imported in imports(reader(path)):
            imported_path = module_path(imported)
            if (root / imported_path).is_file():
                visit(imported)
            else:
                require(imported.split(".")[0] in ("Init", "Lean", "Std", "Lake"),
                        f"IMPORT: missing local dependency {imported}")

    for proof in claim["proofs"]:
        visit(proof["module"])
    entries = [f"{path}\t{digest(reader(path))}" for path in sorted(paths)]
    return digest("\n".join(entries)), len(paths)


def slug(text):
    text = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", text).lower()
    return "".join(c for c in text if c.isalnum() or c in " _-").replace(" ", "-")


def check_links(root, paths):
    for relative in sorted(paths):
        content = outside_fences(read_current(root, relative))
        content = re.sub(r"(`+).*?\1", "", content, flags=re.S)
        destinations = re.findall(r"!?\[[^]\n]*\]\(\s*(<[^>]+>|[^\s)]+)", content)
        definitions = dict(re.findall(r"(?m)^ {0,3}\[([^]]+)\]:\s*(<[^>]+>|\S+)", content))
        destinations.extend(definitions.values())
        for _, reference in re.findall(r"\[([^]\n]+)\]\[([^]\n]*)\]", content):
            if reference:
                require(reference in definitions, f"LINK: missing reference {relative}: {reference}")
        for destination in destinations:
            destination = destination.strip("<>")
            parsed = urlsplit(destination)
            if parsed.scheme or parsed.netloc:
                continue
            local = (root / relative).parent / unquote(parsed.path) if parsed.path else root / relative
            resolved = local.resolve()
            require(resolved.is_relative_to(root.resolve()), f"LINK: escapes repository in {relative}")
            require(resolved.exists(), f"LINK: missing {destination} in {relative}")
            if parsed.fragment and resolved.suffix == ".md":
                counts, ids = {}, set()
                for title, _, _ in headings(resolved.read_text(encoding="utf-8")):
                    base = slug(title)
                    count = counts.get(base, 0)
                    ids.add(base if count == 0 else f"{base}-{count}")
                    counts[base] = count + 1
                require(unquote(parsed.fragment) in ids, f"LINK: missing fragment {destination} in {relative}")


def validate_review(root, review, revision, context):
    require(isinstance(review, dict) and review.get("status") in
            ("pending", "not_recorded", "reviewed", "qualified"), f"REVIEW: invalid status {context}")
    if review["status"] in ("pending", "not_recorded"):
        fields(review, ("status",), context)
        return
    fields(review, ("status", "evidence", "sha256", "responsible", "revision"), context)
    prose(review["responsible"], context + " responsible")
    require(review["revision"] == revision, f"REVIEW: stale revision {context}")
    require(isinstance(review["sha256"], str) and SHA.fullmatch(review["sha256"]), "REVIEW: invalid hash")
    require(digest(read_current(root, review["evidence"])) == review["sha256"],
            f"REVIEW: stale evidence {context}")
    # Presence and integrity only; a human must read and interpret this evidence.


def load_registry(root):
    def unique_pairs(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"SCHEMA: duplicate JSON key {key}")
            result[key] = value
        return result
    return json.loads(read_current(root, REGISTRY), object_pairs_hook=unique_pairs)


def validate(root, registry):
    fields(registry, ("schema_version", "evidence_revision", "immutable_target", "claims"), "registry")
    require(type(registry["schema_version"]) is int and registry["schema_version"] == 1, "SCHEMA: version")
    revision = registry["evidence_revision"]
    require(isinstance(revision, str) and REV.fullmatch(revision), "SCHEMA: revision")
    exists = subprocess.run(["git", "cat-file", "-e", revision + "^{commit}"], cwd=root,
                            capture_output=True, check=False)
    require(exists.returncode == 0, f"SNAPSHOT: unavailable commit {revision}")
    current = lru_cache(maxsize=None)(lambda path: read_current(root, path))
    snapshot = lru_cache(maxsize=None)(lambda path: git_text(root, revision, path))
    target = registry["immutable_target"]
    fields(target, ("revision", "anchors"), "immutable target")
    require(isinstance(target["revision"], str) and REV.fullmatch(target["revision"]), "SCHEMA: target revision")
    require(isinstance(target["anchors"], list) and len(target["anchors"]) == 4, "SCHEMA: four target paragraphs required")
    require(all(isinstance(a, dict) for a in target["anchors"]), "SCHEMA: target anchors")
    require([a.get("paragraph") for a in target["anchors"]] == [1, 2, 3, 4], "SCHEMA: target paragraph order")
    require(len({(a.get("path"), a.get("heading")) for a in target["anchors"]}) == 1,
            "SCHEMA: target must have one canonical source")
    for anchor in target["anchors"]:
        validate_anchor(root, anchor, current)
        validate_anchor(root, anchor, lambda path: git_text(root, target["revision"], path))
    require(isinstance(registry["claims"], list) and bool(registry["claims"]), "SCHEMA: empty claims")
    ids, docs, references, open_reviews = set(), {"README.md", "AGENTS.md", "docs/methode-de-travail-scientifique.fr.md"}, [], []
    for claim in registry["claims"]:
        fields(claim, ("id", "kind", "scope", "anchors", "proofs", "checks", "dependencies",
                       "consumers", "source_sha256", "reviews"), "claim")
        identifier = claim["id"]
        require(isinstance(identifier, str) and re.fullmatch(r"[A-Z][A-Z0-9_-]*", identifier), "SCHEMA: claim id")
        require(identifier not in ids, f"SCHEMA: duplicate claim {identifier}")
        ids.add(identifier)
        require(claim["kind"] in ("constitution", "causal", "cardinality", "behavioral", "implementation"), "SCHEMA: claim kind")
        prose(claim["scope"], identifier + " scope")
        require(isinstance(claim["anchors"], list) and bool(claim["anchors"]), "SCHEMA: missing anchors")
        for anchor in claim["anchors"]:
            validate_anchor(root, anchor, current)
            validate_anchor(root, anchor, snapshot)
            docs.add(anchor["path"])
        require(isinstance(claim["proofs"], list) and bool(claim["proofs"]), "SCHEMA: missing proofs")
        for proof in claim["proofs"]:
            fields(proof, ("module", "name", "role"), identifier + " proof")
            safe_path(root, module_path(proof["module"]))
            require(isinstance(proof["name"], str) and NAME.fullmatch(proof["name"]), "SCHEMA: declaration name")
            require(proof["role"] in ("production", "test"), "SCHEMA: proof role")
            require(proof["module"].startswith("Tests.") == (proof["role"] == "test"), "SCHEMA: production/test mismatch")
            require(proof["role"] == "test" or proof["module"].split(".")[0] in
                    ("RelationalPerimeter", "SegmentedResidualRole", "AbstractSegmentedTurning",
                     "ExactTypeTransport", "StrongPerimetralTurning"), "SCHEMA: nonlocal proof")
            references.append(proof)
        fields(claim["dependencies"], ("formation", "execution", "proof", "transport"), identifier + " dependencies")
        for key, description in claim["dependencies"].items():
            prose(description, identifier + " " + key)
        require(isinstance(claim["checks"], list) and all(isinstance(x, str) for x in claim["checks"]), "SCHEMA: checks")
        require(len(set(claim["checks"])) == len(claim["checks"]), "SCHEMA: duplicate checks")
        for check in claim["checks"]:
            require(check.startswith("scripts/"), "SCHEMA: check path")
            safe_path(root, check)
        require(isinstance(claim["consumers"], list) and all(isinstance(x, str) for x in claim["consumers"]), "SCHEMA: consumers")
        require(len(set(claim["consumers"])) == len(claim["consumers"]), "SCHEMA: duplicate consumers")
        require(isinstance(claim["source_sha256"], str) and SHA.fullmatch(claim["source_sha256"]), "SCHEMA: source hash")
        require(source_fingerprint(root, claim, current)[0] == claim["source_sha256"], f"STALE_SOURCE: {identifier}")
        require(source_fingerprint(root, claim, snapshot)[0] == claim["source_sha256"], f"STALE_SNAPSHOT: {identifier}")
        fields(claim["reviews"], ("reader", "translation", "independent"), identifier + " reviews")
        for key, review in claim["reviews"].items():
            validate_review(root, review, revision, identifier + " " + key)
            if review["status"] in ("pending", "not_recorded", "qualified"):
                open_reviews.append(f"{identifier}:{key}={review['status']}")
    for claim in registry["claims"]:
        require(all(consumer in ids and consumer != claim["id"] for consumer in claim["consumers"]),
                f"SCHEMA: invalid consumer for {claim['id']}")
    check_links(root, docs)
    print(f"SCIENTIFIC_DOCS_STATIC_OK claims={len(ids)} declarations={len({p['name'] for p in references})}")
    print("SCIENTIFIC_DOCS_OPEN_REVIEWS " + ", ".join(open_reviews))
    return references


def lean_check(root, references):
    groups = {"public": set(), "test": set()}
    for proof in references:
        groups["test" if proof["role"] == "test" else "public"].add((proof["module"], proof["name"]))
    for label, refs in groups.items():
        if not refs:
            continue
        imported = {"RelationalPerimeter"} if label == "public" else {module for module, _ in refs}
        names = sorted({name for _, name in refs})
        source = "\n".join("import " + module for module in sorted(imported)) + "\n\n"
        source += "\n".join("#check " + name for name in names) + "\n\n/- AXIOM_AUDIT_BEGIN -/\n"
        source += "\n".join("#print axioms " + name for name in names) + "\n/- AXIOM_AUDIT_END -/\n"
        with tempfile.TemporaryDirectory(prefix="scientific-docs-") as directory:
            path = Path(directory) / "References.lean"
            path.write_text(source, encoding="utf-8", newline="\n")
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                                    capture_output=True, text=True, encoding="utf-8", timeout=180, check=False)
            output = result.stdout + result.stderr
            require(result.returncode == 0 and "warning:" not in output and
                    "depends on axioms:" not in output and "sorryAx" not in output,
                    f"LEAN_REFERENCES: {label}\n{output}")
            for name in names:
                require(f"'{name}' does not depend on any axioms" in output,
                        f"LEAN_REFERENCES: missing axiom output for {name}")
        print(f"SCIENTIFIC_DOCS_LEAN_OK surface={label} declarations={len(names)}")


class SelfTests(unittest.TestCase):
    def rejects(self, expected, action):
        with self.assertRaises(Invalid) as caught:
            action()
        self.assertIn(expected, str(caught.exception))

    def test_imports(self):
        source = '/- outer /- import Bad.X -/ -/\nimport\n A.B\n /- nested /- x -/ -/ C.D\npublic import E.F\nnamespace N\ndef x := "import Wrong.X"'
        self.assertEqual(imports(source), ["A.B", "C.D", "E.F"])
        self.assertEqual(imports('import A.B -- import Bad.X\nset_option x true\n'), ["A.B"])
        self.assertEqual(imports('module\nprelude\nmeta import Lean\nimport Init\n'), ["Lean", "Init"])
        self.rejects("IMPORT_PARSE", lambda: imports("/- missing"))

    def test_anchors(self):
        anchor = {"path": "docs/x.md", "heading": "Target", "paragraph": 2, "sha256": digest("second")}
        reader = lambda _: "# Target\n\nfirst\n\nsecond\n\n## Next\nignored\n"
        validate_anchor(ROOT, anchor, reader)
        self.rejects("STALE_TEXT", lambda: validate_anchor(ROOT, {**anchor, "sha256": "0" * 64}, reader))
        self.rejects("ANCHOR", lambda: passage("# Target\n\nX\n# Target\n\nY", anchor))
        self.rejects("ANCHOR", lambda: passage("# Missing\n\nX", anchor))
        self.assertEqual(passage("```\n# Target\n```\n# Target\n\nfirst\n\nsecond", anchor), "second")
        self.assertEqual(digest("a\r\nb"), digest("a\nb"))
        self.assertNotEqual(digest("a b"), digest("a  b"))

    def test_schema_paths_reviews(self):
        for path in ("../bad", "/bad", "C:/bad", "a/../bad", "a\\bad", "a//bad"):
            self.rejects("PATH", lambda path=path: safe_path(ROOT, path))
        self.rejects("SCHEMA", lambda: fields({"a": 1, "extra": 2}, ("a",), "test"))
        self.rejects("SCHEMA", lambda: module_path("X\n#eval 1"))
        self.rejects("SCHEMA", lambda: prose(" ", "empty"))
        self.rejects("SCHEMA", lambda: validate_review(ROOT, {"status": "reviewed"}, "a" * 40, "test"))
        self.rejects("REVIEW", lambda: validate_review(ROOT, {"status": "pass"}, "a" * 40, "test"))

    def test_source_fingerprint_and_links(self):
        with tempfile.TemporaryDirectory(prefix="scientific-docs-tests-") as directory:
            root = Path(directory)
            for path, text in {"A.lean": "import\n B\n", "B.lean": "def x := 0\n",
                               "README.md": "[ok](docs/x.md#next)\n", "docs/x.md": "# Next\n"}.items():
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(text, encoding="utf-8")
            table = {p: "fixed\n" for p in CONFIG}
            reader = lambda path: table[path] if path in table else read_current(root, path)
            claim = {"checks": [], "proofs": [{"module": "A"}]}
            before, count = source_fingerprint(root, claim, reader)
            self.assertEqual(count, 5)
            (root / "B.lean").write_text("def x := 1\n", encoding="utf-8")
            self.assertNotEqual(before, source_fingerprint(root, claim, reader)[0])
            check_links(root, {"README.md"})
            (root / "README.md").write_text("[bad](docs/x.md#absent)", encoding="utf-8")
            self.rejects("LINK: missing fragment", lambda: check_links(root, {"README.md"}))
            (root / "README.md").write_text("[bad](missing.md)", encoding="utf-8")
            self.rejects("LINK: missing", lambda: check_links(root, {"README.md"}))

    def test_lean_failure_is_not_success(self):
        references = [{"module": "RelationalPerimeter", "name": "MissingDeclaration", "role": "production"}]
        failure = subprocess.CompletedProcess([], 1, stdout="unknown identifier MissingDeclaration", stderr="")
        with patch.object(subprocess, "run", return_value=failure):
            self.rejects("LEAN_REFERENCES: public", lambda: lean_check(ROOT, references))
        # A command returning success without every axiom output also fails.
        empty = subprocess.CompletedProcess([], 0, stdout="", stderr="")
        with patch.object(subprocess, "run", return_value=empty):
            self.rejects("missing axiom output", lambda: lean_check(ROOT, references))

    def test_registry_and_stale_source(self):
        with tempfile.TemporaryDirectory(prefix="scientific-registry-tests-") as directory:
            root = Path(directory)
            files = {path: "fixed\n" for path in CONFIG}
            files.update({"README.md": "[target](docs/target.md)\n", "AGENTS.md": "instructions\n",
                          "docs/methode-de-travail-scientifique.fr.md": "procedure\n",
                          "docs/target.md": "# Target\n\none\n\ntwo\n\nthree\n\nfour\n",
                          "RelationalPerimeter/Example.lean": "def example := 0\n"})
            for relative, text in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            anchors = [{"path": "docs/target.md", "heading": "Target", "paragraph": i,
                        "sha256": digest(value)} for i, value in enumerate(("one", "two", "three", "four"), 1)]
            claim = {"id": "EXAMPLE", "kind": "cardinality", "scope": "finite only",
                     "anchors": [anchors[0]], "proofs": [{"module": "RelationalPerimeter.Example",
                     "name": "example", "role": "production"}], "checks": [],
                     "dependencies": dict.fromkeys(("formation", "execution", "proof", "transport"), "explicit"),
                     "consumers": [], "source_sha256": "0" * 64,
                     "reviews": {k: {"status": "pending"} for k in ("reader", "translation", "independent")}}
            claim["source_sha256"] = source_fingerprint(root, claim, lambda p: files[p])[0]
            registry = {"schema_version": 1, "evidence_revision": "a" * 40,
                        "immutable_target": {"revision": "a" * 40, "anchors": anchors}, "claims": [claim]}
            git_ok = subprocess.CompletedProcess([], 0, stdout=b"", stderr=b"")
            with redirect_stdout(io.StringIO()), patch.object(subprocess, "run", return_value=git_ok), patch.dict(
                    validate.__globals__, {"git_text": lambda _, revision, path: files[path]}):
                validate(root, registry)
                self.rejects("duplicate claim", lambda: validate(root, {**registry, "claims": [claim, claim]}))
                (root / "RelationalPerimeter/Example.lean").write_text("def example := 1\n", encoding="utf-8")
                self.rejects("STALE_SOURCE", lambda: validate(root, registry))
                (root / "RelationalPerimeter/Example.lean").write_text(files["RelationalPerimeter/Example.lean"], encoding="utf-8")
                (root / "docs/target.md").write_text(files["docs/target.md"].replace("one", "changed"), encoding="utf-8")
                self.rejects("STALE_TEXT", lambda: validate(root, registry))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--static", action="store_true")
    modes.add_argument("--lean", action="store_true")
    modes.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests))
        require(result.wasSuccessful(), "SELF_TEST: failure")
        print("SCIENTIFIC_DOCS_SELF_TEST_OK")
        return
    references = validate(ROOT, load_registry(ROOT))
    if args.lean:
        lean_check(ROOT, references)


if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, UnicodeError, json.JSONDecodeError, subprocess.TimeoutExpired) as error:
        print(f"SCIENTIFIC_DOCS_ERROR: {error}", file=sys.stderr)
        sys.exit(1)
