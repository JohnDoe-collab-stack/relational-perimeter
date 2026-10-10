#!/usr/bin/env python3
"""Loader direct-call reachability and one actual continuation execution site.

The scope is generated C direct calls, not a global process-initialization,
indirect-closure, physical cost or heap-identity theorem.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def main():
    helpers = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(helpers["bodies_with_objects"](path.read_text(encoding="utf-8")))
    select = helpers["shared"]["select"]
    base = "Agent_Local_Documentary_"
    loader = select(functions, base + "PortableCheckpoint_load")
    finish = select(functions, base + "Portable_finish___redArg")
    execute = select(functions, base + "Deduction_execute___redArg")
    denied = re.compile(r"Resources_Support_extend|Documentary_(?:Deduction_(?:quote|form|execute)|"
                        r"Program_(?:step|execute)|Dossier_(?:step|execute)|Master_search|"
                        r"Adaptive_(?:run|takeTurn))|VariableMaster_masterHead")

    def check(current):
        seen, pending = set(), [loader]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            if denied.search(name):
                raise ValueError("Loader reaches a production function: " + name)
            calls = re.findall(r"\b((?:l|lp)_\w+)\s*\(", current.get(name, ""))
            for target in calls:
                if denied.search(target):
                    raise ValueError("Loader reaches a production function: " + target)
                if target in current:
                    pending.append(target)
        count = len(re.findall(r"\b" + re.escape(execute) + r"\s*\(", current[finish]))
        if count != 1:
            raise ValueError("Continuation execute sites: expected one, found " + str(count))
        return len(seen)

    reachable = check(functions)
    replay = dict(functions); replay[loader] += "\nv_replay = " + execute + "();\n"
    duplicate = dict(functions); duplicate[finish] += "\nv_duplicate = " + execute + "();\n"
    for label, changed in (("load replay", replay), ("continue duplicate", duplicate)):
        try:
            check(changed)
        except ValueError:
            pass
        else:
            raise ValueError("Mutation accepted: " + label)
    print(f"DOCUMENTARY_CHECKPOINT_CODEGEN_OK: loader {reachable} direct-call bodies; "
          "no production reachable; one continuation execute site; two mutations rejected; explicit direct-call scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_CHECKPOINT_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
