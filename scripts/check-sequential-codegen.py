#!/usr/bin/env python3
"""Direct compiled dependencies of the dependent assignment component."""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CALL = re.compile(r"\b((?:l|lp)_\w+)\s*\(")
INDIRECT = re.compile(r"\blean_apply_[0-9]+\s*\(")


def main():
    previous = runpy.run_path(str(ROOT / "scripts/check-assignment-codegen.py"))
    helper = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    denied = previous["DENIED"]
    bodies = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        bodies.update(helper["bodies_with_objects"](path.read_text(encoding="utf-8")))
    suffixes = (
        "SequentialPortable_limit", "SequentialPortable_safeDecidable",
        "SequentialPortable_assemble", "SequentialPortable_load",
        "SequentialPortable_validate", "SequentialPortable_restore",
        "SequentialPortable_restoreAt", "SequentialCapture_restoreState",
        "SequentialCapture_incorporateState", "SequentialPortable_stage__formed",
    )
    roots = [helper["shared"]["select"](bodies, "Agent_Local_Documentary_" + suffix) for suffix in suffixes]
    # First-order codec callbacks are permitted in loaders. State reads may
    # apply the received resource-reading closure; no producer is authorized.
    no_indirect = {0, 1, 2, 8, 9}

    def check(current):
        counts = []
        for index, root in enumerate(roots):
            pending, seen = [root], set()
            while pending:
                name = pending.pop()
                if name in seen:
                    continue
                seen.add(name)
                body = current[name]
                calls = CALL.findall(body)
                if denied.search(name) or any(denied.search(callee) for callee in calls):
                    raise ValueError("Historical production/generation or reader query executed: " + name)
                if index in no_indirect and INDIRECT.search(body):
                    raise ValueError("Validation/latent construction applies an indirect closure: " + name)
                pending.extend(callee for callee in calls if callee in current and callee not in seen)
            counts.append(len(seen))
        return counts

    counts = check(bodies)
    producer = helper["shared"]["select"](bodies, "Resources_Support_extend")
    query = helper["shared"]["select"](bodies, "EndogenousDecomposition_readAssignmentQueries")
    generation = helper["shared"]["select"](bodies, "EndogenousDecomposition_constructStage")
    mutations = 0
    for index, root in enumerate(roots):
        injections = ["\nv_replay = " + producer + "();\n"]
        if index in no_indirect:
            injections.append("\nv_query = lean_apply_1(v_reader, v_query);\n")
        if index in (2, 5, 7):
            injections += ["\nv_query = " + query + "();\n", "\nv_generation = " + generation + "();\n"]
        for injection in injections:
            changed = dict(bodies)
            changed[root] += injection
            try:
                check(changed)
            except ValueError as error:
                if "reader query" not in str(error) and "indirect closure" not in str(error):
                    raise ValueError("Unrelated mutation rejection") from error
                mutations += 1
            else:
                raise ValueError("Forbidden production/query injection accepted in " + suffixes[index] + ": " + injection.strip())
    print("SEQUENTIAL_CODEGEN_OK: ten direct-call paths=" + ",".join(map(str, counts)) +
          f"; {mutations} replay/generation/query mutations rejected; retained environment supplied")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("SEQUENTIAL_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
