#!/usr/bin/env python3
"""Direct compiled paths for foundation/history/generation/state and assembly.

Checks named calls, including package-mangled lp_ names and constant objects.
Codec callbacks operate on finite words. Latent functions are constructed;
reader queries and historical producers/executors are forbidden on these paths.
This is not a whole-process initialization or byte-only master certificate.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
CALL = re.compile(r"\b((?:l|lp)_\w+)\s*\(")
INDIRECT = re.compile(r"\blean_apply_\d+\s*\(")
EXTRA = re.compile(
    r"StrongPerimetralTurning_(?:canonicalTarget|generatedStepOfFreeK)|"
    r"executeSequentialStage|realizeNextOperationalState|buildThreadedConstitutiveStage|"
    r"exploreRecordedCandidates|runCandidateExtraction|constructMeasuredOperationalRoot|"
    r"executedStageDecomposition|relationalConstitutiveRoleStage|"
    r"ProducedOutputImage_regime"
)


def main():
    previous = runpy.run_path(str(ROOT / "scripts/check-assignment-codegen.py"))
    helper = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    denied = previous["DENIED"]
    bodies = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        bodies.update(helper["bodies_with_objects"](path.read_text(encoding="utf-8")))
    suffixes = (
        "FoundationPortable_capture", "FoundationPortable_materialize", "FoundationPortable_restore",
        "HistoryPortable_capture", "HistoryPortable_stepFields", "HistoryPortable_restoreCode",
        "HistoryPortable_restore", "GenerationPortable_capture", "GenerationPortable_fields",
        "GenerationPortable_restoreRecord", "GenerationPortable_restore",
        "StatePortable_capture", "StatePortable_bit", "StatePortable_holdsDecidable",
        "StatePortable_fields", "StatePortable_validate", "StatePortable_restore",
        "StateCapture_record", "StateCapture_save", "AssembledCheckpoint_decodedState",
        "AssembledCheckpoint_putValues", "AssembledCheckpoint_putSource",
        "AssembledCheckpoint_capture", "AssembledCheckpoint_restoreMaster",
        "AssembledCheckpoint_restore",
        "StatePortable_freshDecidable", "StatePortable_restoreForNext",
        "StateCapture_prefixHistory", "StateCapture_history",
    )
    roots = [helper["shared"]["select"](bodies, "Agent_Local_Documentary_" + suffix) for suffix in suffixes]
    strict = {0, 1, 3, 4, 7, 8, 11, 12, 13, 14, 17, 19, 20, 21, 25, 27, 28}

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
                if denied.search(name) or EXTRA.search(name) or any(denied.search(callee) or EXTRA.search(callee) for callee in calls):
                    raise ValueError("Historical production/generation or reader query executed: " + name)
                if index in strict and INDIRECT.search(body):
                    raise ValueError("Constructor/capture invokes an indirect closure: " + name)
                pending.extend(callee for callee in calls if callee in current and callee not in seen)
            counts.append(len(seen))
        return counts

    counts = check(bodies)
    historical = helper["shared"]["select"](bodies, "Resources_Support_extend")
    stage = helper["shared"]["select"](bodies, "EndogenousDecomposition_executeSequentialStage")
    query = helper["shared"]["select"](bodies, "EndogenousDecomposition_readAssignmentQueries")
    mutations = 0
    for index, root in enumerate(roots):
        injections = ["\nv_replay = " + historical + "();\n", "\nv_stage = " + stage + "();\n",
                      "\nv_reader = " + query + "();\n"]
        if index in strict:
            injections.append("\nv_indirect = lean_apply_1(v_reader, v_query);\n")
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
                raise ValueError("Forbidden compiled-call mutation accepted: " + suffixes[index])
    print("STATE_ASSEMBLY_CODEGEN_OK paths=" + ",".join(map(str, counts)) +
          f"; mutations_rejected={mutations}; source restored from bytes; master payload still typed")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("STATE_ASSEMBLY_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
