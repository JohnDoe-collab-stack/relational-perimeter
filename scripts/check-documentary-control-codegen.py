#!/usr/bin/env python3
"""Named compiled dependencies of control capture, serialization and loading.

Received context-codec closures and whole-process module initialization are
explicit boundaries. This is not an arbitrary closure or heap-identity theorem.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
DENIED = re.compile(
    r"Resources_(?:Support_extend|Producer_arguments)|"
    r"MasterResources_(?:discover|applyStage|decompose|assemble|headNext|continue|execute)|"
    r"VariableMaster_masterHead|Documentary_(?:extractionProducer|extract|authorize|incorporate|"
    r"Deduction_(?:quote|form|execute)|Program_(?:step|execute)|Dossier_(?:step|execute)|"
    r"Master_search|Adaptive_(?:run|takeTurn)|Memory_(?:step|advance|run))"
)


def main():
    helper = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    shared = helper["shared"]
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(helper["bodies_with_objects"](path.read_text(encoding="utf-8")))
    roots = [shared["select"](functions, "Agent_Local_Documentary_PortableControl_" + suffix)
             for suffix in ("capture", "record", "save", "restore", "load", "loadPresent")]

    def check(current):
        counts = []
        for root in roots:
            seen = shared["reachable"](current, root)
            for name in seen:
                if DENIED.search(name) or any(DENIED.search(token) for token in shared["TOKEN"].findall(current[name])):
                    raise ValueError("Control path reaches a historical producer: " + name)
            counts.append(len(seen))
        return counts

    counts = check(functions)
    producer = shared["select"](functions, "Resources_Support_extend")
    for root in roots:
        mutated = dict(functions)
        mutated[root] += "\nv_control_replay = " + producer + "();\n"
        try:
            check(mutated)
        except ValueError as error:
            if "historical producer" not in str(error):
                raise ValueError("Unrelated mutation rejection: " + str(error)) from error
        else:
            raise ValueError("Injected historical production was accepted")
    print("PORTABLE_CONTROL_CODEGEN_OK: six named-dependency paths=" + ",".join(map(str, counts)) +
          "; six replay mutations rejected; received-codec closure boundary; full-present bytes still open")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("PORTABLE_CONTROL_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
