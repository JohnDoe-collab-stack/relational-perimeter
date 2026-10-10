#!/usr/bin/env python3
"""Named C source-check and master-sharing checks; complex engines stay open.

Mutation fixtures exercise this checker, not compiled mutant executions.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def make_check(functions, select):
    base = "Agent_Local_Documentary_"
    keys = ("ControlMaster_searchCode", "ControlMaster_runCode",
            "ControlSelection_checkCode", "ControlSelection_meetsCode", "ControlSelection_originCode",
            "ControlResources_readCode___redArg", "ControlPermission_locatedLookup___redArg",
            "ControlPermission_equalCode", "Selection_choiceFormula", "Selection_Checked_flag___redArg",
            "ControlCompletion_decideCode___redArg")
    names = {key: select(functions, base + key) for key in keys}
    for key, suffix in (("head", "EndogenousDecomposition_VariableMaster_masterHead"),
                        ("selected", "EndogenousDecomposition_VariableMaster_selected___redArg"),
                        ("opening", "EndogenousDecomposition_VariableMaster_openFrontier___redArg"),
                        ("reduction", "SAT_normalizeGeneratedStructuralFrontierByFlip___redArg")):
        names[key] = select(functions, suffix)
    search = [select(functions, base + "ControlMaster_searchCode___lam__" + str(i)) for i in range(7)]
    run = [select(functions, base + "ControlMaster_runCode___lam__" + str(i)) for i in range(3)]
    selection = [name for name in functions if base + "ControlSelection_" in name and
                 any(word in name for word in ("checkCode", "meetsCode", "originCode")) and
                 not name.endswith("___boxed") and "splitter" not in name and "closed__" not in name]
    scope = search + run + selection + [names["ControlMaster_searchCode"], names["ControlMaster_runCode"]]
    quote_read = select(functions, base + "ControlSelection_checkCode___lam__3")
    citation = select(functions, base + "ControlSelection_checkCode___lam__1")
    paid_readout = select(functions, base + "ControlSelection_checkCode___lam__2")

    def calls(body, target):
        return list(re.finditer(r"\b" + re.escape(names[target]) + r"\s*\(", body))

    def one(body, target):
        found = re.search(re.escape(names[target]) + r"\s*\(([^;]+)\);", body)
        if found is None or len(calls(body, target)) != 1:
            raise ValueError("Missing or repeated call: " + target)
        return found

    def stored(body, operation, field, variable):
        if not re.search(operation + r"\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", body):
            raise ValueError("Actual " + variable + " is not retained in field " + str(field))

    def step(body, callback, label):
        closure = re.search(r"(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(" + re.escape(callback) + r"(?:___boxed)?\)", body)
        if closure is None or not re.search(r"lean_ctor_set\([^,]+, 1, " + re.escape(closure[1]) + r"\)", body):
            raise ValueError("Step continuation missing")
        if not re.search(r"= " + str(label) + r";", body) or "lean_alloc_ctor(1, 2, 0)" not in body:
            raise ValueError("Paid step label missing")

    def check(current):
        for name in scope:
            if re.search(r"\b\w*(?:Documentary_Selection_check|Documentary_Master_search|Documentary_Master_run|"
                         r"Documentary_Master_decide|Documentary_Dossier_step|Documentary_sourceCitation|Documentary_meetsDecision|"
                         r"Resources_Ref_position|Resources_Support_read|Resources_read)"
                         r"(?:___redArg)?\s*\(", current[name]):
                raise ValueError("Original source check, traversal or whole master replayed")
        for target, owner in (("head", search[6]), ("opening", search[2]), ("reduction", search[1]),
                              ("ControlCompletion_decideCode___redArg", run[2])):
            one(current[owner], target)
            for name in scope:
                if name != owner and calls(current[name], target):
                    raise ValueError("Complex primitive outside its named paid callback")
        step(current[names["ControlMaster_searchCode"]], search[6], 37)
        for owner, callback, label in ((search[4], search[3], 38), (search[3], search[2], 39),
                                       (search[2], search[1], 40), (search[1], search[0], 41),
                                       (run[1], run[0], 54)):
            step(current[owner], callback, label)
        for field, variable in enumerate(("head", "leftCheck", "rightCheck", "opening", "reduction")):
            stored(current[search[0]], "lean_ctor_set", field, variable)
        for name in search[:5]:
            if name != search[0]:
                for variable in ("head", "leftCheck", "rightCheck"):
                    if not re.search(r"lean_closure_set\([^,]+, \d+, v_" + variable + r"_\d+_\)", current[name]):
                        raise ValueError("Master stage drops an actual head or source check")
        for owner, variable in ((search[6], "left"), (search[5], "right")):
            found = one(current[owner], "ControlSelection_checkCode")
            if not re.search(r", v_" + variable + r"_\d+_\);", found[0]):
                raise ValueError("Source check substitutes the received occurrence")
        body = current[search[3]]
        selected = one(body, "selected")
        if not re.search(r"\(v_head_\d+_\);", selected[0]):
            raise ValueError("Formula substitutes the actual master head")
        flags = list(re.finditer(r"(\w+)\s*=\s*" + re.escape(names["Selection_Checked_flag___redArg"]) +
                                 r"\((v_(?:leftCheck|rightCheck)_\d+_)\);", body))
        if len(flags) != 2 or "leftCheck" not in flags[0][2] or "rightCheck" not in flags[1][2]:
            raise ValueError("Formula substitutes one of the two actual source flags")
        selected_value = re.search(r"(\w+)\s*=\s*" + re.escape(names["selected"]) + r"\(", body)
        if selected_value is None or one(body, "Selection_choiceFormula")[1].split(", ") != [selected_value[1], flags[0][1], flags[1][1]]:
            raise ValueError("Formula does not consume the selected variable and both flags")
        found = one(current[run[2]], "ControlCompletion_decideCode___redArg")
        if not re.search(r", v_actual_\d+_, v_memory_\d+_\);", found[0]):
            raise ValueError("Decision substitutes the produced stage or retained memory")
        stored(current[run[0]], "lean_ctor_set", 0, "actual")
        stored(current[run[0]], "lean_ctor_set", 1, "decision")
        stored(current[run[1]], "lean_closure_set", 0, "actual")
        stored(current[run[1]], "lean_closure_set", 1, "decision")
        stored(current[run[2]], "lean_closure_set", 0, "actual")
        one(current[names["ControlSelection_checkCode"]], "ControlPermission_locatedLookup___redArg")
        if calls(current[names["ControlSelection_checkCode"]], "ControlResources_readCode___redArg"):
            raise ValueError("Source read before the permission result")
        body = current[quote_read]
        found = one(body, "ControlResources_readCode___redArg")
        guard = body.find("if (lean_obj_tag")
        if guard < 0:
            raise ValueError("Permission dispatch missing")
        opening = body.index("{", guard); depth = 1; ending = opening + 1
        while depth and ending < len(body):
            depth += (body[ending] == "{") - (body[ending] == "}"); ending += 1
        if found.start() < ending or calls(body[opening:ending], "ControlResources_readCode___redArg"):
            raise ValueError("Denied source reads its passage")
        for field, variable in ((0, "fst"), (1, "fst"), (2, "readout")):
            stored(current[citation], "lean_ctor_set", field, variable)
        stored(current[paid_readout], "lean_closure_set", 2, "readout")
        step(current[paid_readout], citation, 36)
        one(current[citation], "ControlSelection_meetsCode")

    mutations = []
    for name in scope:
        mutations.append((name, functions[name] + " lp_forbidden_Documentary_Master_search();"))
    for target, owner in (("head", search[6]), ("opening", search[2]), ("reduction", search[1]),
                          ("ControlCompletion_decideCode___redArg", run[2])):
        mutations.append((owner, functions[owner] + names[target] + "();"))
        mutations.append((names["ControlMaster_searchCode"], functions[names["ControlMaster_searchCode"]] + names[target] + "();"))
    for name, pattern in ((citation, r"v_readout_\d+_"), (paid_readout, r"v_readout_\d+_"),
                          (run[0], r"v_actual_\d+_"), (run[1], r"v_actual_\d+_"),
                          (run[2], r"v_actual_\d+_"), (run[0], r"v_decision_\d+_"), (run[1], r"v_decision_\d+_"),
                          (search[6], r"v_left_\d+_"), (search[5], r"v_right_\d+_")):
        mutations.append((name, re.sub(pattern, "v_substituted", functions[name])))
    for pattern in (r"v_head_\d+_", r"v_leftCheck_\d+_", r"v_rightCheck_\d+_"):
        mutations.append((search[3], re.sub(pattern, "v_substituted", functions[search[3]])))
    for field in ("head", "leftCheck", "rightCheck", "opening", "reduction"):
        mutations.append((search[0], re.sub(r"v_" + field + r"_\d+_", "v_substituted", functions[search[0]])))
    for owner, label in ((names["ControlMaster_searchCode"], 37), (search[4], 38), (search[3], 39),
                         (search[2], 40), (search[1], 41), (run[1], 54), (paid_readout, 36)):
        mutations.append((owner, functions[owner].replace("= " + str(label) + ";", "= 0;")))
    return check, mutations


def verify(functions, select):
    check, mutations = make_check(functions, select)
    check(functions)
    for name, body in mutations:
        changed = dict(functions); changed[name] = body
        try:
            check(changed)
        except ValueError:
            pass
        else:
            raise ValueError("Quotation mutation accepted: " + name)
    print("DOCUMENTARY_MASTER_CONTROL_CODEGEN_OK: actual source checks, guarded reads and shared master stage; " +
          str(len(mutations)) + " textual mutations rejected; head/opening/reduction internals remain open")


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        functions.update(agent["bodies_with_objects"](path.read_text(encoding="utf-8")))
    verify(functions, agent["shared"]["select"])


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_MASTER_CONTROL_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
