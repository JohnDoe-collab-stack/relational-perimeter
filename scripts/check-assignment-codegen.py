#!/usr/bin/env python3
"""Check direct compiled paths for assignment capture and latent restoration.

Codec callbacks operate on first-order words. Capture/interpret paths may not
apply arbitrary closures. Latent reader bodies execute only when later queried.
Whole-process initialization, heap identity and full master loading are outside
this direct-call check.
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
    r"executeCausalOperationalHead|applyDiscoveryExecution|"
    r"constitutedHistory|constitutedEndpoint|constructStage|generateCanonicalStage|"
    r"ConstitutiveGeneration_iteratedHistory|StrongPerimetralTurning_generate|"
    r"readAssignmentQueries|readFlippedAssignment|readAlternatingAssignment|compareUnary|"
    r"Documentary_(?:Master_search|Dossier_step|Program_step|Adaptive_(?:takeTurn|run)|Memory_(?:step|advance|run))"
)


def main():
    helper = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    bodies = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        bodies.update(helper["bodies_with_objects"](path.read_text(encoding="utf-8")))
    suffixes = (
        "AssignmentCapture_retained", "AssignmentCapture_cursor",
        "PortableAssignment_reflect", "PortableAssignment_interpret",
        "PortableAssignment_capture", "PortableAssignment_stage__formed",
        "AssignmentCodec_load", "AssignmentCodec_restore",
    )
    roots = [helper["shared"]["select"](bodies, "Agent_Local_Documentary_" + suffix) for suffix in suffixes]

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
                if DENIED.search(name) or any(DENIED.search(callee) for callee in calls):
                    raise ValueError("Historical production/generation or reader query executed: " + name)
                if index < 6 and INDIRECT.search(body):
                    raise ValueError("Capture/latent construction applies an indirect closure: " + name)
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
        if index < 6:
            injections += ["\nv_query = lean_apply_1(v_reader, v_query);\n"]
        if index in (3, 7):
            injections += ["\nv_query = " + query + "();\n"]
        if index in (0, 5):
            injections += ["\nv_generation = " + generation + "();\n"]
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
                raise ValueError("Forbidden production/query injection accepted")
    print("ASSIGNMENT_CODEGEN_OK: eight direct-call paths=" + ",".join(map(str, counts)) +
          f"; {mutations} replay/query mutations rejected; latent readers retained; component scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("ASSIGNMENT_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
