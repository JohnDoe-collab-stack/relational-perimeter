#!/usr/bin/env python3
"""Direct generated-call check for recipe capture, restoration and port reads.

The seven producer factories may construct latent operation closures for future
use. These roots may not execute those closures or a historical production.
Checks direct named calls and indirect application in that call graph. It does
not cover construction of membership witnesses, latent closure execution,
whole-process initialization, byte restoration of master values or heap identity.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CALL = re.compile(r"\b((?:l|lp)_\w+)\s*\(")
INDIRECT = re.compile(r"\blean_apply_\d+\s*\(")
DENIED = re.compile(
    r"Resources_(?:Support_extend|Producer_arguments)|"
    r"MasterResources_(?:continue|execute)|VariableMaster_masterHead|"
    r"runThreadedNextDiscovery|buildFromExecutedDiscovery|prefixLocalOperationalProducer|"
    r"executeCausalOperationalHead|Documentary_(?:Master_search|Dossier_step|Program_step|"
    r"Adaptive_(?:takeTurn|run)|Memory_(?:step|advance|run))"
)


def main():
    helper = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(helper["bodies_with_objects"](path.read_text(encoding="utf-8")))
    roots = [helper["shared"]["select"](functions, "Agent_Local_Documentary_" + suffix) for suffix in (
        "MasterFormation_captureFrom", "MasterFormation_captureTree",
        "MasterFormation_resources", "MasterFormation_cursor",
        "MasterFormation_Tree_formation", "MasterFormation_CursorData_restore",
        "MasterObservation_observedPorts",
    )]

    def check(current):
        counts = []
        for root in roots:
            seen, pending = set(), [root]
            while pending:
                name = pending.pop()
                if name in seen:
                    continue
                seen.add(name)
                body = current[name]
                calls = CALL.findall(body)
                if DENIED.search(name) or any(DENIED.search(callee) for callee in calls):
                    raise ValueError("Recipe path executes historical production: " + name)
                if INDIRECT.search(body):
                    raise ValueError("Recipe path applies an indirect closure: " + name)
                pending.extend(callee for callee in calls if callee in current and callee not in seen)
            counts.append(len(seen))
        return counts

    counts = check(functions)
    producer = helper["shared"]["select"](functions, "Resources_Support_extend")
    mutations = 0
    for root in roots:
        for injection in ("\nv_replay = " + producer + "();\n",
                          "\nv_replay = lean_apply_1(v_operation, v_arguments);\n"):
            changed = dict(functions)
            changed[root] += injection
            try:
                check(changed)
            except ValueError as error:
                if "historical production" not in str(error) and "indirect closure" not in str(error):
                    raise ValueError("Unrelated mutation rejection") from error
                mutations += 1
            else:
                raise ValueError("Historical production injection accepted")
    print("MASTER_RECIPES_CODEGEN_OK: seven direct-call paths=" + ",".join(map(str, counts)) +
          f"; {mutations} replay/application mutations rejected; latent factories retained; typed-payload scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("MASTER_RECIPES_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
