#!/usr/bin/env python3
"""Compiled sharing checks for one unfolding of finite dossier composition.

The shared binary master bridge is checked separately. Here the next-state
projection and recursive tail are explicit boundaries for application counting.
These counts do not bound SAT normalization or physical execution cost.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
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
    worker = select(functions, "Agent_Local_Documentary_Dossier_execute")
    step = select(functions, "Agent_Local_Documentary_Dossier_step")
    next_state = select(functions, "Agent_Local_Documentary_Dossier_Step_next___redArg")
    bridge = select(functions, "Agent_Local_Documentary_Master_run")
    applications(functions, params, step, bridge, 1)
    applications(functions, params, worker, step, 1,
                 unfolds=(worker,), boundaries=(next_state,))
    applications(functions, params, worker, next_state, 1,
                 unfolds=(worker,), boundaries=(step,))
    alias = worker + "__independent_unfolding"
    if alias in functions:
        raise ValueError("Dossier analysis alias already exists")
    augmented, alias_params = dict(functions), dict(params)
    augmented[alias], alias_params[alias] = functions[worker], params[worker]
    applications(augmented, alias_params, alias, worker, 1,
                 boundaries=(step, next_state))

    # Alter only the in-memory C-IR body. Repeating a reachable producer must fail
    # the same check used above; repository sources and compiled artifacts stay intact.
    for caller, target, unfolds, boundaries in (
        (step, bridge, (), ()),
        (worker, step, (worker,), (next_state,)),
        (worker, next_state, (worker,), (step,)),
    ):
        pattern = re.compile(r"\b(v_\w+)\s*=\s*" + re.escape(target) + r"\([^;]*\);")
        matches = list(pattern.finditer(functions[caller]))
        if len(matches) != 1:
            raise ValueError("Expected one mutation site for " + target)
        match = matches[0]
        repeated = match.group(0).replace(match.group(1), "v_dossier_duplicate", 1)
        mutated = dict(functions)
        mutated[caller] = functions[caller][:match.start()] + repeated + "\n" + functions[caller][match.start():]
        try:
            with redirect_stdout(io.StringIO()):
                applications(mutated, params, caller, target, 1,
                             unfolds=unfolds, boundaries=boundaries)
        except ValueError as error:
            if "found [2,2]" not in str(error) and "found [0,2]" not in str(error):
                raise ValueError("Unexpected mutation failure: " + str(error)) from error
        else:
            raise ValueError("Repeated dossier producer accepted: " + target)
    print("DOCUMENTARY_DOSSIER_CODEGEN_OK: one bridge, one next-state projection and one tail "
          "per unfolding; three reachable duplicate-call mutations rejected; explicit boundaries")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_DOSSIER_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
