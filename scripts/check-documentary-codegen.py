#!/usr/bin/env python3
"""Sharing checks for the first documentary semantic layer, not a master bridge.

Reuse the existing C-IR call analysis with its hidden-call regressions. Check
maximum applications over actual branches, rather than count textual call sites.
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
    prefix = "Agent_Local_Documentary_"
    execute = select(functions, prefix + "execute")
    certified = select(functions, prefix + "executeCertified")
    extract = select(functions, prefix + "extract")
    incorporate = select(functions, prefix + "incorporate___redArg")
    applications = agent["applications"]
    applications(functions, params, execute, certified, 1)
    applications(functions, params, certified, extract, 1)
    applications(functions, params, certified, incorporate, 1)
    print("DOCUMENTARY_CODEGEN_OK: one shared extraction/incorporation on allowed branches")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
