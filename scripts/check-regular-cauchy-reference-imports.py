#!/usr/bin/env python3
"""Exact Gate 7.4 module DAG and transitive numerical/runtime boundary.

The shared Lean header parser reads split and commented imports. This checks
module dependencies, not scientific interpretation or equality of primitives.
"""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from lean_imports import imports

ROOT = Path(__file__).resolve().parent.parent
PREFIX = "RelationalPerimeter.Constitution.Reals."


def validate(graph, expected, roots, allowed):
    for module, dependencies in expected.items():
        if module not in graph or set(graph[module]) != dependencies:
            raise ValueError("Direct import DAG changed: " + module)
    for root in roots:
        seen, active = set(), set()

        def visit(module, path):
            if module in active:
                raise ValueError("Numerical import cycle: " + " -> ".join(path + [module]))
            if module in seen:
                return
            if module not in graph:
                if module == "Init" or module.startswith("Init."):
                    return
                raise ValueError("Non-numerical external import: " + " -> ".join(path + [module]))
            if module not in allowed:
                raise ValueError("Non-numerical import: " + " -> ".join(path + [module]))
            active.add(module)
            for dependency in graph[module]:
                visit(dependency, path + [module])
            active.remove(module)
            seen.add(module)

        visit(root, [])


def self_test():
    expected = {"Names": {"Finite"}, "Classes": {"Names"}}
    roots, allowed = {"Classes"}, {"Classes", "Names", "Finite"}
    baseline = {"Names": ["Finite"], "Classes": ["Names"], "Finite": []}
    validate(baseline, expected, roots, allowed)
    validate({**baseline, "Finite": ["Init", "Init.Data.Nat.Basic"]}, expected, roots, allowed)
    for graph, needle in (
        ({**baseline, "Names": ["Runtime"]}, "Direct import DAG"),
        ({**baseline, "Finite": ["Runtime"], "Runtime": []}, "Non-numerical import"),
        ({**baseline, "Finite": ["Classes"]}, "Numerical import cycle"),
        ({**baseline, "Finite": ["Mathlib.Real"]}, "Non-numerical external import"),
    ):
        try:
            validate(graph, expected, roots, allowed)
        except ValueError as error:
            if needle not in str(error):
                raise
        else:
            raise ValueError("Import mutation was accepted")


def main():
    self_test()
    expected, roots, allowed = {}, set(), set()
    manifest = ROOT / "scripts/regular-cauchy-reference-import-boundaries.txt"
    for raw in manifest.read_text(encoding="utf-8").splitlines():
        if not raw.strip() or raw.startswith("#"):
            continue
        kind, *names = raw.split()
        if kind == "module" and len(names) >= 1:
            if PREFIX + names[0] in expected:
                raise ValueError("Duplicate module manifest entry")
            expected[PREFIX + names[0]] = {PREFIX + name for name in names[1:]}
        elif kind == "numeric-root" and len(names) == 1:
            roots.add(PREFIX + names[0])
        elif kind == "numeric-allow" and names:
            allowed.update(PREFIX + name for name in names)
        else:
            raise ValueError("Malformed import manifest")
    if not expected or not roots or not allowed:
        raise ValueError("Incomplete import manifest")
    graph = {path.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."):
             imports(path.read_text(encoding="utf-8-sig"))
             for path in (ROOT / "RelationalPerimeter").rglob("*.lean")}
    validate(graph, expected, roots, allowed)
    print("REGULAR_CAUCHY_REFERENCE_IMPORTS_OK: seven exact module import sets; three transitive numerical roots; Init-only external imports; four rejected mutations")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print("REGULAR_CAUCHY_REFERENCE_IMPORTS_FAILED: " + str(error), file=sys.stderr)
        raise SystemExit(1)
