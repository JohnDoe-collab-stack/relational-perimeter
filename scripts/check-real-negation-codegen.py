#!/usr/bin/env python3
"""Bounded checks of the pinned C routes for relational negation.

Counts are callback applications, not physical resource bounds. Concrete
compact closure construction is checked in addition to the Lean projections.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
base = runpy.run_path(str(ROOT / "scripts/check-real-addition-codegen.py"))
Value, Analysis = base["Value"], base["AdditiveAnalysis"]
PREFIX, LEFT, LIVE_LEFT = base["PREFIX"], base["LEFT"], base["LIVE_LEFT"]
EXECUTOR, IDENTITY = base["EXECUTOR"], base["IDENTITY"]
COMPACT = base["LIVE_ENVIRONMENT"]
ENTRY = PREFIX + "RelationalRealNegation_produceNegation"
LIVE = PREFIX + "RelationalRealNegation_negationLiveStep"
ENVIRONMENT = PREFIX + "RelationalRealNegation_negEnvironment"
ACTION = PREFIX + "SignedDyadicCode_neg"
OBSERVER = PREFIX + "RelationalRealNegation_NegationProduction_code___redArg"


def arguments(marked=False):
    full = base["arguments"](marked)
    return [full[0], full[1], full[2], full[4], full[6], full[7]]


def require_count(functions, params, entry, args, target, expected=1):
    _, low, high = Analysis(functions, params, base["shared"]["reachable"], target=target).run(entry, args)
    if (low, high) != (expected, expected):
        raise ValueError(f"{entry}: {target}: expected [{expected},{expected}], found [{low},{high}]")


def validate_current(functions, params):
    return Analysis(functions, params, base["shared"]["reachable"], target=EXECUTOR,
                    capture=True, validate=True, stop_executor=True).run(ENTRY, arguments(True))[0]


def validate_compact(functions, params):
    source = Value(fields={slot: base["tagged"](f"rich-{slot}") for slot in range(11)})
    compact, _, _ = Analysis(functions, params, base["shared"]["reachable"], target="",
                             capture=True).run(COMPACT, [source])
    if compact.retained() != frozenset({"rich-8", "rich-9", "rich-10"}):
        raise ValueError("Negation live closure retained rich source machinery")
    # Bound the concrete constructor syntactically: analysing all hypothetical
    # exclusive-reuse branches of this rich Service constructor creates an
    # impossible self-alias in the generic graph join. Do not turn that path
    # into a trusted summary. Instead require these exact direct closure and
    # installation sites, with no reassignment or mutation of the compact
    # value. Any change outside this pinned shape fails for manual review.
    body = functions[ENVIRONMENT]
    child = params[ENVIRONMENT][2]
    made = re.findall(r'\b(\w+)\s*=\s*' + re.escape(COMPACT) + r'\(\s*' + re.escape(child) + r'\s*\);', body)
    closure = re.search(r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' +
                        re.escape(LIVE) + r'\),\s*3,\s*1\);', body)
    if len(made) != 1 or closure is None:
        raise ValueError("Negation live closure retained rich source machinery: constructor shape changed")
    if len(re.findall(r'\b' + re.escape(made[0]) + r'\s*=', body)) != 1:
        raise ValueError("Negation live closure retained rich source machinery: compact value reassigned")
    if re.search(r'lean_(?:ctor|closure)_set\(\s*' + re.escape(made[0]) + r'\s*,', body):
        raise ValueError("Negation live closure retained rich source machinery: compact value mutated")
    captures = re.findall(r'lean_closure_set\(\s*' + re.escape(closure[1]) + r',\s*(\d+),\s*(\w+)\s*\);', body)
    if captures != [("0", made[0])]:
        raise ValueError("Negation live closure retained rich source machinery: wrong capture")
    if len(re.findall(r'lean_ctor_set\(\w+,\s*9,\s*' + re.escape(closure[1]) + r'\);', body)) != 2:
        raise ValueError("Negation live closure retained rich source machinery: wrong installed callback")
    for slot in (8, 10):
        installed = re.findall(r'lean_ctor_set\(\w+,\s*' + str(slot) + r',\s*(\w+)\);', body)
        if len(installed) != 2 or installed[0] != installed[1] or re.search(r'\b' + re.escape(installed[0]) +
                r'\s*=\s*(?:l|lp)_\w+\s*;', body) is None:
            raise ValueError("Negation live closure retained rich source machinery: read/answer must be static")


def reject_mutation(check, functions, params, label, expected):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(expected):
            raise ValueError(f"Unexpected mutation failure {label}: {error}") from error
        print("REAL_NEGATION_MUTATION_REJECTED " + label)
        return
    raise ValueError("Mutation accepted: " + label)


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    texts.append("\n".join(
        f"LEAN_EXPORT lean_object* {name}(lean_object* a, lean_object* p){{ return a; }}"
        for name in (LEFT, LIVE_LEFT)))
    texts.append(f"LEAN_EXPORT lean_object* {base['READ']}(lean_object* a, lean_object* p, lean_object* r){{ return r; }}"
                 f"\nLEAN_EXPORT lean_object* {IDENTITY}(lean_object* a){{ return a; }}")
    functions = {}
    for text in texts:
        functions.update(base["shared"]["bodies"](text))
        base["add_static_objects"](functions, text)
    functions = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                 for name, body in functions.items()}
    params = base["parameters"](texts)
    for name, arity in ((ENTRY, 6), (LIVE, 3), (ENVIRONMENT, 3), (ACTION, 1), (OBSERVER, 1), (COMPACT, 1)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact negation definition/arity: " + name)
    for target in (LEFT, EXECUTOR, ACTION):
        require_count(functions, params, ENTRY, arguments(), target)
        print(f"REAL_NEGATION_APPLICATION_OK {target}=[1,1]")
    result = validate_current(functions, params)
    for slot, tag in ((0, LEFT), (1, "executed-action")):
        if result.fields.get(slot, Value()).retained() != frozenset({tag}):
            raise ValueError("Negation packet lost its actual source/action")
    calls = set(re.findall(r'\b(\w+)\s*\(', functions[OBSERVER]))
    if any(name != "lean_ctor_get" and not name.startswith(("lean_inc", "lean_dec")) for name in calls):
        raise ValueError("Negation code observer does more than project the installed action")

    perform = PREFIX + "HeterogeneousRealRuntime_perform___redArg"
    original = params[ENTRY]
    broken = dict(functions)
    pattern = re.escape(perform) + r'\(' + re.escape(original[2]) + r',\s*' + re.escape(original[3]) + r','
    replacement = perform + "(" + original[2] + ", lean_ctor_get(" + original[2] + ", 0),"
    broken[ENTRY], count = re.subn(pattern, replacement, broken[ENTRY])
    if count != 1:
        raise ValueError("Negation current source archive mutation site changed")
    reject_mutation(validate_current, broken, params, "reset-source-archive", "Child callback does not use its current state")
    broken = dict(functions)
    broken[ENTRY], count = re.subn(r'(\b' + re.escape(EXECUTOR) + r'\([^;]*?,\s*)' +
                                   re.escape(original[4]) + r'(\s*,)', r'\1lean_box(0)\2', broken[ENTRY])
    if count != 1:
        raise ValueError("Negation current journal mutation site changed")
    reject_mutation(validate_current, broken, params, "reset-negation-journal", "Arithmetic action does not use the current journal")

    # Two applications remain two even if the first result is discarded.
    alias = "l_negation_probe_double"
    broken = dict(functions)
    broken[alias] = "{ lean_object* ignored; ignored = " + ENTRY + "(p,d,s,a,j,n); return " + ENTRY + "(p,d,s,a,j,n); }"
    mutated_params = dict(params, **{alias: ["p", "d", "s", "a", "j", "n"]})
    for target in (LEFT, EXECUTOR, ACTION):
        require_count(broken, mutated_params, alias, arguments(), target, 2)
    preserves = PREFIX + "RelationalRealNegation_negationProgram___redArg___lam__4"
    if preserves not in functions:
        raise ValueError("Missing exact negation preservation callback")
    broken = dict(functions)
    broken[preserves] = broken[preserves].replace("{", "{ lean_object* duplicate; duplicate = " + ACTION + "(lean_box(0));", 1)
    require_count(broken, params, ENTRY, arguments(), ACTION, 2)

    live_args = [base["live_environment"](LIVE_LEFT), Value(fields={0: Value(), 1: Value()}), Value()]
    for target in (LIVE_LEFT, ACTION):
        require_count(functions, params, LIVE, live_args, target)
    for target in (LEFT, EXECUTOR):
        require_count(functions, params, LIVE, live_args, target, 0)
    live_args[1] = Value(fields={0: base["tagged"]("live-left"), 1: base["tagged"]("last")})
    Analysis(functions, params, base["shared"]["reachable"], target=ACTION,
             capture=True, validate=True).run(LIVE, live_args)
    validate_compact(functions, params)

    body = functions[ENVIRONMENT]
    compact = re.search(r'\b(\w+)\s*=\s*' + re.escape(COMPACT) + r'\([^;]+\);', body)
    closure = re.search(r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' +
                        re.escape(LIVE) + r'\),\s*3,\s*1\);', body)
    if compact is None or closure is None:
        raise ValueError("Negation live callback must close over one compact source environment")
    capture = r'lean_closure_set\(' + re.escape(closure[1]) + r',\s*0,\s*' + re.escape(compact[1]) + r'\);'
    if re.search(capture, body) is None:
        raise ValueError("Negation live callback captures the wrong environment")
    broken = dict(functions)
    broken[ENVIRONMENT], count = re.subn(capture, "lean_closure_set(" + closure[1] + ", 0, " + params[ENVIRONMENT][2] + ");", body)
    if count != 1:
        raise ValueError("Negation live capture mutation site changed")
    reject_mutation(validate_compact, broken, params, "capture-rich-source", "Negation live closure retained rich source machinery")
    print("REAL_NEGATION_CODEGEN_OK: current source/journal, one source and action, retained packet, projection-only readout; live=one compact source environment/one source step/one negation/no rich executor; multiplicity and capture mutations checked")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"REAL_NEGATION_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
