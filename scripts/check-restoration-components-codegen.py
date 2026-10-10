#!/usr/bin/env python3
"""Typed master capture/restore and dossier-byte loader do not replay producers.

Checks generated bodies, named static closures and their initializers. The master
paths reject indirect application throughout. For the dossier loader this rejects
indirect application in its direct call graph; its constructed evidence reader
can later call the earlier evidence reader. Whole-process module initialization
and physical byte decoding of the master are outside this check's scope.
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
INDIRECT = re.compile(r"\blean_apply_[0-9]+\s*\(")


def main():
    helpers = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    shared = helpers["shared"]
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(helpers["bodies_with_objects"](path.read_text(encoding="utf-8")))
    roots = [shared["select"](functions, suffix) for suffix in (
        "Agent_Local_Documentary_PortableMemory_load",
        "Agent_Local_Documentary_MasterPayload_cursor",
        "Agent_Local_Documentary_MasterPayload_CursorData_restore",
        "Agent_Local_Documentary_MaterializedPresent_present",
        "Agent_Local_Documentary_MaterializedPresent_PresentData_restore",
    )]

    def check(current):
        groups = []
        for index, root in enumerate(roots):
            seen = shared["reachable"](current, root)
            direct, pending = set(), [root]
            while pending:
                name = pending.pop()
                if name in direct:
                    continue
                direct.add(name)
                pending.extend(target for target in re.findall(r"\b((?:l|lp)_\w+)\s*\(", current[name])
                               if target in current and target not in direct)
            for name in seen:
                if DENIED.search(name) or any(DENIED.search(token) for token in shared["TOKEN"].findall(current[name])):
                    raise ValueError("Restoration path reaches historical production: " + name)
                if (index > 0 or name in direct) and INDIRECT.search(current[name]):
                    raise ValueError("Restoration path invokes an indirect closure: " + name)
            groups.append(len(seen))
        return groups

    counts = check(functions)
    producer = shared["select"](functions, "Resources_Support_extend")
    for root in (roots[0], roots[1]):
        for injection in ("\nv_replay = " + producer + "();\n", "\nv_replay = lean_apply_1(v_operation, v_arguments);\n"):
            mutated = dict(functions)
            mutated[root] += injection
            try:
                check(mutated)
            except ValueError:
                pass
            else:
                raise ValueError("Historical production mutation accepted")
    print("RESTORATION_COMPONENTS_CODEGEN_OK: five paths=" + ",".join(map(str, counts)) +
          "; no historical production; master paths without indirect application; "
          "dossier direct-call scope; four mutations rejected; typed-master scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("RESTORATION_COMPONENTS_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
