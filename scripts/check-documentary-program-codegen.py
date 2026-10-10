#!/usr/bin/env python3
"""Sharing checks for one finite-program node and its stored completion witness.

Two checks count direct producer sites in the dispatcher: abstract received
binding closures are outside that scope. The other checks follow compiled
applications, with the recursive tail explicitly cut. This is not a cost bound.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def scalar_literals(source):
    # Scalar tails appear after the pointer fields in compiler constructor
    # objects. Eight literal bytes contain no callable symbol. Represent only
    # their numeric value as an analysis immediate; keep symbols unresolved.
    pattern = re.compile(r"LEAN_SCALAR_PTR_LITERAL\((\d+(?:\s*,\s*\d+){7})\)")

    def replace(match):
        octets = [int(value.strip()) for value in match[1].split(",")]
        if any(value > 255 for value in octets):
            raise ValueError("Invalid compiler scalar byte")
        value = sum(octet << (8 * index) for index, octet in enumerate(octets))
        return f"((lean_object*)(size_t)(({value} << 1) | 1))"

    return pattern.sub(replace, source)


def direct_site(functions, entry, target):
    count = len(re.findall(r"\b" + re.escape(target) + r"\s*\(", functions[entry]))
    if count != 1:
        raise ValueError(f"{entry}: expected one direct {target} site, found {count}")


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions, texts = {}, []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        source = scalar_literals(path.read_text(encoding="utf-8"))
        texts.append(source)
        functions.update(agent["bodies_with_objects"](source))
    params = agent["parameters"](texts)
    select, applications = agent["shared"]["select"], agent["applications"]
    base = "Agent_Local_Documentary_"
    worker = select(functions, base + "Program_execute")
    step = select(functions, base + "Program_step___redArg")
    quotation = select(functions, base + "Program_quotationStep___redArg")
    deduction = select(functions, base + "Program_deductionStep___redArg")
    missing = select(functions, base + "Program_missingStep___redArg")
    quote = select(functions, base + "Deduction_quote___redArg")
    incorporate = select(functions, base + "Deduction_incorporateDerived___redArg")
    bridge = select(functions, base + "Dossier_step")
    operation = select(functions, base + "Deduction_execute___redArg")
    extend = select(functions, "Resources_Support_extend___redArg")
    certificate = select(functions, base + "ProgramCases_actualComplete")
    completion = select(functions, base + "Program_Execution_complete___redArg")
    actuals = [name for name in functions if name.startswith("_init_") and
               name.endswith(base + "ProgramCases_actual___closed__0")]
    if len(actuals) != 1:
        raise ValueError("Expected actual execution and stored-certificate initializers")
    actual = actuals[0]

    def check(current):
        applications(current, params, worker, step, 1, unfolds=(worker,))
        applications(current, params, quotation, quote, 1)
        applications(current, params, deduction, incorporate, 1)
        applications(current, params, missing, extend, 0)
        alias = worker + "__program_tail_analysis"
        if alias in current:
            raise ValueError("Program analysis alias already exists")
        augmented, alias_params = dict(current), dict(params)
        augmented[alias], alias_params[alias] = current[worker], params[worker]
        applications(augmented, alias_params, alias, worker, 1, boundaries=(step,))
        applications(current, params, certificate, worker, 0, boundaries=(completion,))
        applications(current, params, actual, worker, 1)
        direct_site(current, step, bridge)
        direct_site(current, step, operation)

    check(functions)
    for caller, target in ((worker, step), (quotation, quote), (deduction, incorporate),
                           (step, bridge), (step, operation)):
        pattern = re.compile(r"\b(v_\w+)\s*=\s*" + re.escape(target) + r"\([^;]*\);")
        sites = list(pattern.finditer(functions[caller]))
        if len(sites) != 1:
            raise ValueError("Expected one reachable mutation site for " + target)
        site = sites[0]
        duplicate = site.group(0).replace(site.group(1), "v_program_duplicate", 1)
        current = dict(functions)
        current[caller] = current[caller][:site.start()] + duplicate + "\n" + current[caller][site.start():]
        try:
            with redirect_stdout(io.StringIO()):
                check(current)
        except ValueError as error:
            if "found [0,2]" not in str(error) and "found [2,2]" not in str(error) and "found 2" not in str(error):
                raise ValueError("Unexpected mutation rejection: " + str(error)) from error
        else:
            raise ValueError("Duplicate program producer accepted: " + target)
    current = dict(functions)
    current[certificate] = "v_program_replay = " + worker + "(" + ",".join(
        "lean_box(0)" for _ in params[worker]) + ");\n" + current[certificate]
    try:
        with redirect_stdout(io.StringIO()):
            check(current)
    except ValueError as error:
        if "found [1,1]" not in str(error):
            raise ValueError("Unexpected certificate replay rejection: " + str(error)) from error
    else:
        raise ValueError("Certificate execution replay accepted")
    print("DOCUMENTARY_PROGRAM_CODEGEN_OK: seven application checks, two direct dispatcher-site checks; "
          "six mutations rejected; explicit closure and recursive-tail and completion-engine scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_PROGRAM_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
