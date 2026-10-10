#!/usr/bin/env python3
"""Sharing checks for deduction formation, admission and quotation composition.

Application counts stop at named boundaries. The operation closure and admitted
resource field are checked separately in the pinned compiler's emitted C.
"""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def sharing(body, params):
    action = params[-2]
    matches = re.findall(r"lean_ctor_set\((v_\w+), 0, " + re.escape(action) + r"\);", body)
    if len(matches) != 1 or "return " + matches[0] + ";" not in body:
        raise ValueError("Admission does not return the actual formed support")


def operands(body, params, evaluate):
    args = params[-1]
    left = re.search(r"(v_\w+) = lean_ctor_get\(" + re.escape(args) + r", 0\);", body)
    rest = re.search(r"(v_\w+) = lean_ctor_get\(" + re.escape(args) + r", 1\);", body)
    right = re.search(r"(v_\w+) = lean_ctor_get\(" + re.escape(rest.group(1)) + r", 0\);", body) if rest else None
    if not left or not right or not re.search(re.escape(evaluate) +
            r"\(v_\w+, " + re.escape(left.group(1)) + ", " + re.escape(right.group(1)) + r"\)", body):
        raise ValueError("Deduction does not evaluate its ordered actual input ports")


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions, texts = {}, []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        functions.update(agent["bodies_with_objects"](text))
    params = agent["parameters"](texts)
    select, applications = agent["shared"]["select"], agent["applications"]
    names = {key: select(functions, suffix) for key, suffix in {
        "form": "Documentary_Deduction_form___redArg",
        "producer": "Documentary_Deduction_producer___redArg",
        "extend": "Resources_Support_extend___redArg",
        "execute": "Documentary_Deduction_execute___redArg",
        "admit": "Documentary_Deduction_incorporateDerived___redArg",
        "result": "Documentary_Deduction_Decision_result___redArg",
        "read": "Resources_Support_read___redArg",
        "kind": "Documentary_Deduction_derivedKind___redArg",
        "quoteAll": "Documentary_Deduction_quoteAll___redArg",
        "step": "Documentary_Dossier_step",
        "next": "Documentary_Dossier_Step_next___redArg",
        "ingest": "Documentary_Deduction_ingest___redArg",
        "quote": "Documentary_Deduction_quote___redArg",
        "operation": "Documentary_Deduction_producer___redArg___lam__1",
        "evaluate": "Documentary_Deduction_evaluate",
        "goal": "Documentary_Dossier_Execution_goal___redArg",
    }.items()}
    checks = [
        ("form", "extend", 1, (), ()),
        ("form", "producer", 1, (), ("extend",)),
        ("execute", "form", 1, (), ()),
        ("result", "admit", 1, (), ("read", "kind")),
        ("admit", "extend", 0, (), ()),
        ("quoteAll", "step", 1, ("quoteAll",), ("next", "ingest")),
        ("quoteAll", "ingest", 1, ("quoteAll",), ("step", "next")),
        ("ingest", "quote", 1, (), ()),
    ]
    for caller, target, count, unfolds, boundaries in checks:
        applications(functions, params, names[caller], names[target], count,
                     unfolds=tuple(names[n] for n in unfolds),
                     boundaries=tuple(names[n] for n in boundaries))
    sharing(functions[names["admit"]], params[names["admit"]])
    operands(functions[names["operation"]], params[names["operation"]], names["evaluate"])
    initializers = [name for name in functions if name.startswith("_init_") and
                    name.endswith("DeductionCases_actual__quotations__complete")]
    if len(initializers) != 1:
        raise ValueError("Expected one actual quotation certificate initializer")
    certificate = initializers[0]
    applications(functions, params, certificate, names["quoteAll"], 0, boundaries=(names["goal"],))
    if "DeductionCases_quotationRun;" not in functions[certificate]:
        raise ValueError("Quotation certificate does not consume the produced run")

    for caller, target, boundaries in (
        ("form", "extend", ()),
        ("execute", "form", ()),
        ("quoteAll", "step", ("next", "ingest")),
    ):
        body = functions[names[caller]]
        pattern = re.compile(r"\b(v_\w+)\s*=\s*" + re.escape(names[target]) + r"\([^;]*\);")
        matches = list(pattern.finditer(body))
        if len(matches) != 1:
            raise ValueError("Expected one reachable duplication site")
        match = matches[0]
        repeated = match.group(0).replace(match.group(1), "v_deduction_duplicate", 1)
        changed = dict(functions)
        changed[names[caller]] = body[:match.start()] + repeated + "\n" + body[match.start():]
        try:
            with redirect_stdout(io.StringIO()):
                applications(changed, params, names[caller], names[target], 1,
                    unfolds=(names["quoteAll"],) if caller == "quoteAll" else (),
                    boundaries=tuple(names[n] for n in boundaries))
        except ValueError as error:
            if "found [2,2]" not in str(error) and "found [0,2]" not in str(error):
                raise ValueError("Unexpected duplication failure: " + str(error)) from error
        else:
            raise ValueError("Repeated producer accepted")
    action = params[names["admit"]][-2]
    changed = functions[names["admit"]].replace(", 0, " + action + ");", ", 0, v_reconstructed);")
    try:
        sharing(changed, params[names["admit"]])
    except ValueError:
        pass
    else:
        raise ValueError("Reconstructed admitted support accepted")
    body = functions[names["operation"]]
    call = re.search(re.escape(names["evaluate"]) + r"\((v_\w+), (v_\w+), (v_\w+)\)", body)
    if not call:
        raise ValueError("Missing operation mutation site")
    changed = body[:call.start()] + names["evaluate"] + "(" + call[1] + ", " + call[3] + ", " + call[2] + ")" + body[call.end():]
    try:
        operands(changed, params[names["operation"]], names["evaluate"])
    except ValueError:
        pass
    else:
        raise ValueError("Swapped premise ports accepted")
    changed = dict(functions)
    replay = "v_certificate_replay = " + names["quoteAll"] + "(" + ", ".join(
        "lean_box(0)" for _ in params[names["quoteAll"]]) + ");\n"
    changed[certificate] = functions[certificate].replace("_start:", "_start:\n" + replay, 1)
    try:
        with redirect_stdout(io.StringIO()):
            applications(changed, params, certificate, names["quoteAll"], 0, boundaries=(names["goal"],))
    except ValueError as error:
        if "found [1,1]" not in str(error):
            raise ValueError("Unexpected certificate replay failure: " + str(error)) from error
    else:
        raise ValueError("Replayed quotation certificate accepted")
    print("DOCUMENTARY_DEDUCTION_CODEGEN_OK: actual support shared; ordered input ports; "
          "nine bounded application checks; six in-memory mutations rejected")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_DEDUCTION_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
