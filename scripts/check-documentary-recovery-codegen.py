#!/usr/bin/env python3
"""Direct sharing checks for the recovery adapter, with rejecting mutations.

This checks named C bodies, not an entire call graph or physical cost. Existing
memory/adaptive gates check the downstream productions and their sharing.
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
    keys = ("RecoveryData_prepare___redArg", "RecoveryData_recover___redArg",
            "RecoveryData_preserves___redArg", "RecoveryData_recover__complete___redArg",
            "RecoveryDataCases_initialComplete", "RecoveryDataCases_prefixComplete",
            "Memory_step___redArg", "Memory_finish___redArg",
            "Memory_advance___redArg", "Memory_run___redArg",
            "Adaptive_takeTurn___redArg", "Adaptive_run___redArg",
            "Program_step___redArg", "Program_execute")
    names = {key: select(functions, base + key) for key in keys}
    pairs = (("RecoveryData_prepare___redArg", "Memory_step___redArg"),
             ("RecoveryData_recover___redArg", "Memory_finish___redArg"))
    certificates = ("RecoveryData_preserves___redArg", "RecoveryData_recover__complete___redArg",
                    "RecoveryDataCases_initialComplete", "RecoveryDataCases_prefixComplete")
    producers = tuple(key for key in keys if key not in certificates)

    def calls(body, target):
        return len(re.findall(r"\b" + re.escape(names[target]) + r"\s*\(", body))

    def check(current):
        for caller, target in pairs:
            count = calls(current[names[caller]], target)
            if count != 1:
                raise ValueError(f"{caller}: expected one {target} site, found {count}")
        for certificate in certificates:
            if any(calls(current[names[certificate]], producer) for producer in producers):
                raise ValueError(f"{certificate}: certificate replays a recovery producer")

    check(functions)
    mutations = [(caller, target, "found 2") for caller, target in pairs]
    mutations += [(certificate, "RecoveryData_recover___redArg", "replays")
                  for certificate in certificates]
    for caller, target, reason in mutations:
        changed = dict(functions)
        changed[names[caller]] += "\nv_recovery_replay = " + names[target] + "();\n"
        try:
            check(changed)
        except ValueError as error:
            if reason not in str(error):
                raise ValueError("Unexpected mutation rejection: " + str(error)) from error
        else:
            raise ValueError("Replay accepted: " + caller)
    print("DOCUMENTARY_RECOVERY_CODEGEN_OK: two direct production sites, four consuming certificates; "
          "two duplicates and four certificate replays rejected; direct-site scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_RECOVERY_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
