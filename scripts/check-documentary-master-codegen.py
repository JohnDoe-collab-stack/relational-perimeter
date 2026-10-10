#!/usr/bin/env python3
"""Compiled sharing checks for the two-source documentary master bridge.

Count applications through the generated helpers, on actual branches. The checks
cover one bridge step; they do not state a bound for recursive SAT normalization.
"""
from pathlib import Path
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions, texts = {}, []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        functions.update(agent["bodies_with_objects"](text))
    params = agent["parameters"](texts)
    select = agent["shared"]["select"]
    applications = agent["applications"]
    entry = select(functions, "Agent_Local_Documentary_Master_run")
    targets = [
        ("EndogenousDecomposition_VariableMaster_masterHead", 1),
        ("Agent_Local_Documentary_Selection_check___redArg", 2),
        ("EndogenousDecomposition_VariableMaster_openFrontier___redArg", 1),
        ("SAT_normalizeGeneratedStructuralFrontierByFlip___redArg", 1),
    ]
    for suffix, maximum in targets:
        applications(functions, params, entry, select(functions, suffix), maximum)
    complete = select(functions, "Agent_Local_Documentary_Master_complete")
    applications(functions, params, complete,
                 select(functions, "Agent_Local_Documentary_extract"), 1)
    applications(functions, params, complete,
                 select(functions, "Agent_Local_Documentary_incorporate___redArg"), 1)
    print("DOCUMENTARY_MASTER_CODEGEN_OK: run has one actual master head, two source checks "
          "and one opening/normalization; complete shares one extraction/incorporation. "
          "Higher-order routing is outside these application-count checks.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_MASTER_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
