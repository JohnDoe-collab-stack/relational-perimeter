#!/usr/bin/env python3
"""Store loader direct C calls: no past production; two rejected mutations.

This check does not cover indirect closures, process initialization or heap identity.
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
    loader = helpers["shared"]["select"](functions, "Agent_Local_Documentary_PortableStore_load")
    denied = re.compile(r"Resources_Support_extend|Documentary_(?:Deduction_(?:quote|form|execute)|"
                        r"Program_(?:step|execute)|Dossier_(?:step|execute)|Master_search|"
                        r"Adaptive_(?:run|takeTurn)|Memory_(?:step|advance|run))|VariableMaster_masterHead")

    def check(current):
        seen, pending = set(), [loader]
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            if denied.search(name):
                raise ValueError("Store loader reaches a production function: " + name)
            for target in re.findall(r"\b((?:l|lp)_\w+)\s*\(", current.get(name, "")):
                if denied.search(target):
                    raise ValueError("Store loader reaches a production function: " + target)
                if target in current:
                    pending.append(target)
        return len(seen)

    reachable = check(functions)
    for suffix in ("Agent_Local_Documentary_Deduction_execute___redArg", "Resources_Support_extend"):
        target = helpers["shared"]["select"](functions, suffix)
        mutated = dict(functions)
        mutated[loader] += "\nv_replay = " + target + "();\n"
        try:
            check(mutated)
        except ValueError:
            pass
        else:
            raise ValueError("Replay mutation accepted: " + suffix)
    print(f"DOCUMENTARY_PORTABLE_STORE_CODEGEN_OK: {reachable} loader direct-call bodies; "
          "no production reachable; two mutations rejected; explicit direct-call scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_PORTABLE_STORE_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
