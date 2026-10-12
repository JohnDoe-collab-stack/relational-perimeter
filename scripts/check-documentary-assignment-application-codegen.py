#!/usr/bin/env python3
"""Named compiled checks of metered assignment readers and their formation.
Textual mutation fixtures test the checker, not executions of corrupted code.
Budget computation, boxing/static objects and physical costs stay outside scope.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = "Agent_Local_Documentary_ControlAssignmentApplication_"
NATIVE_SUFFIXES = (
    "SAT_Assignment_flipAt", "SAT_GeneratedStructuralFlipAtRelation_mapContinuation",
    "Documentary_Control_execute", "Documentary_Control_runCtl",
)
NATIVE = r"\b\w*(?:" + "|".join(map(re.escape, NATIVE_SUFFIXES)) + r")(?:___\w+)?\s*\("

def make_check(functions, select):
    scope = [name for name in functions if BASE in name and not name.endswith("___boxed") and "closed__" not in name]
    if not scope:
        raise ValueError("Assignment reader compiled bodies missing")
    paths = (
        ("constantReadCode___redArg", r"= 112;"),
        ("constantReadCode___redArg", r"lean_alloc_closure\(\(void\*\)\([^)]*constantReadCode___redArg___lam__0"),
        ("flipReadCode___redArg", r"= 112;"),
        ("flipReadCode___redArg", r"lean_closure_set\([^,]+, 0, v_prior_\d+_\)"),
        ("flipReadCode___redArg", r"lean_closure_set\([^,]+, 1, v_query_\d+_\)"),
        ("flipReadCode___redArg", r"lean_closure_set\([^,]+, 1, v_selected_\d+_\)"),
        ("flipReadCode___redArg___lam__0", r"ControlPermission_equalCode\(v_query_\d+_, v_selected_\d+_\)"),
        ("flipReadCode___elam__0", r"(v_readCode_\d+_) = lean_ctor_get\(v_prior_\d+_, 0\)"),
        ("flipReadCode___elam__0", r"lean_apply_1\(v_readCode_\d+_, v_query_\d+_\)"),
        ("flipReadCode___elam__0___lam__1", r"= 113;"),
        ("flipReadCode___elam__0___lam__1", r"lean_closure_set\([^,]+, 0, v___x_\d+_\)"),
        ("flipReadCode___elam__0___lam__1", r"lean_closure_set\([^,]+, 1, v___x_\d+_\)"),
        ("constantReaderCode___lam__1", r"lean_ctor_set\([^,]+, 0, v_read_\d+_\)"),
        ("constantReaderCode___lam__1", r"lean_ctor_set\([^,]+, 1, v_bound_\d+_\)"),
        ("flipReaderCode___lam__1", r"lean_closure_set\([^,]+, 0, v_read_\d+_\)"),
        ("flipReaderCode___lam__1", r"lean_closure_set\([^,]+, 1, v_bound_\d+_\)"),
    )
    paths = [(select(functions, BASE + suffix), pattern) for suffix, pattern in paths]
    read_scope = [name for name in scope if BASE + "flipReadCode" in name or BASE + "constantReadCode" in name]
    equal = select(functions, "Agent_Local_Documentary_ControlPermission_equalCode")
    equal_owner = select(functions, BASE + "flipReadCode___redArg___lam__0")
    prior_owner = select(functions, BASE + "flipReadCode___elam__0")

    def check(current):
        for name in scope:
            if re.search(NATIVE, current[name]):
                raise ValueError("Native assignment producer/evaluator replayed: " + name)
            if re.search(r"lean_apply_\d+\(v_assignment_\d+_", current[name]):
                raise ValueError("Opaque source assignment invoked: " + name)
        for name in read_scope:
            if re.search(r"\blean_nat_dec_eq\s*\(", current[name]):
                raise ValueError("Unpaid native natural comparison: " + name)
        if sum(len(re.findall(re.escape(equal) + r"\s*\(", current[name])) for name in read_scope) != 1:
            raise ValueError("Paid comparison omitted or duplicated")
        for name, pattern in paths:
            if not re.search(pattern, current[name]):
                raise ValueError("Actual paid reader data path dropped: " + name)
        if len(re.findall(r"lean_apply_1\(v_readCode_\d+_, v_query_\d+_\)", current[prior_owner])) != 1:
            raise ValueError("Actual source reader omitted or duplicated")

    mutations = [(name, functions[name] + " lp_forbidden_" + suffix + "();")
                 for name in scope for suffix in NATIVE_SUFFIXES]
    mutations += [(name, functions[name] + " lean_apply_1(v_assignment_777_, v_query_777_);") for name in scope]
    mutations += [(name, functions[name] + " lean_nat_dec_eq();") for name in read_scope]
    mutations += [(name, re.sub(pattern, "lp_dropped_paid_path", functions[name])) for name, pattern in paths]
    mutations += [
        (equal_owner, functions[equal_owner] + equal + "();"),
        (prior_owner, functions[prior_owner] + " lean_apply_1(v_readCode_777_, v_query_777_);"),
    ]
    return check, mutations, scope

def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(agent["bodies_with_objects"](path.read_text(encoding="utf-8")))
    check, mutations, scope = make_check(functions, agent["shared"]["select"])
    check(functions)
    for name, body in mutations:
        current = dict(functions)
        current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError("Assignment reader textual mutation accepted: " + name)
    print("DOCUMENTARY_ASSIGNMENT_APPLICATION_CODEGEN_OK: " + str(len(mutations)) +
          " textual mutations rejected in " + str(len(scope)) +
          " named bodies; one paid natural comparison and one actual source reader; "
          "no opaque source assignment invocation; budget bootstrap and physical costs remain open")

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_ASSIGNMENT_APPLICATION_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
