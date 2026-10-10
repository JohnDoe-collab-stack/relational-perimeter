#!/usr/bin/env python3
"""Direct compiled call sites for snapshots and documentary future execution.

This checks dispatcher/recursive sites, not path counts or physical cost.
Received policy closures and binding lookups remain explicit boundaries.
The existing adaptive gate checks sharing inside each actual bounded turn.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(agent["bodies_with_objects"](path.read_text(encoding="utf-8")))
    select = agent["shared"]["select"]
    base = "Agent_Local_Documentary_"
    names = {name: select(functions, base + name) for name in (
        "Memory_advance___redArg", "Memory_step___redArg", "Memory_run___redArg",
        "Memory_sourceStep___redArg", "Memory_sourceRun___redArg", "Memory_finish___redArg",
        "Adaptive_takeTurn___redArg", "Adaptive_run___redArg", "MemoryCases_resumedComplete")}
    pairs = [("Memory_advance___redArg", "Adaptive_takeTurn___redArg"),
             ("Memory_step___redArg", "Memory_advance___redArg"),
             ("Memory_run___redArg", "Memory_step___redArg"),
             ("Memory_run___redArg", "Memory_run___redArg"),
             ("Memory_sourceStep___redArg", "Memory_step___redArg"),
             ("Memory_sourceRun___redArg", "Memory_sourceStep___redArg"),
             ("Memory_sourceRun___redArg", "Memory_sourceRun___redArg"),
             ("Memory_finish___redArg", "Adaptive_run___redArg")]
    certificate = names["MemoryCases_resumedComplete"]

    def check(current):
        for caller, target in pairs:
            count = len(re.findall(r"\b" + re.escape(names[target]) + r"\s*\(", current[names[caller]]))
            if count != 1:
                raise ValueError(f"{caller}: expected one {target} site, found {count}")
        if any(re.search(r"\b" + re.escape(names[name]) + r"\s*\(", current[certificate]) for name in
               ("Memory_finish___redArg", "Memory_run___redArg", "Memory_step___redArg",
                "Memory_advance___redArg", "Adaptive_run___redArg", "Adaptive_takeTurn___redArg")):
            raise ValueError("Certificate replays a documentary producer")

    check(functions)
    for caller, target in pairs:
        current = dict(functions)
        current[names[caller]] += "\nv_memory_duplicate = " + names[target] + "();\n"
        try:
            check(current)
        except ValueError as error:
            if "found 2" not in str(error):
                raise ValueError("Unexpected duplicate rejection: " + str(error)) from error
        else:
            raise ValueError("Duplicate accepted: " + caller)
    current = dict(functions)
    current[certificate] += "\nv_memory_replay = " + names["Memory_finish___redArg"] + "();\n"
    try:
        check(current)
    except ValueError as error:
        if "replays" not in str(error):
            raise ValueError("Unexpected certificate rejection: " + str(error)) from error
    else:
        raise ValueError("Certificate replay accepted")
    print("DOCUMENTARY_MEMORY_CODEGEN_OK: eight direct site checks and certificate no-replay check; "
          "eight duplicates and one certificate replay rejected; explicit direct-site scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_MEMORY_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
