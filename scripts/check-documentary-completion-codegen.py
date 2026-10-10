#!/usr/bin/env python3
"""Named compiled completion sharing and paid formation; routing internals stay open.

Textual mutations test the guard, not executions of compiled mutants.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def make_check(functions, select):
    base = "Agent_Local_Documentary_"
    keys = ("ControlCitation_extractCode", "ControlCitation_readoutCode___redArg",
            "ControlCompletion_completeCode___redArg", "ControlCompletion_decideCode___redArg",
            "ControlCompletion_assignmentCode___redArg", "Master_Stage_candidateFromBit___redArg",
            "Master_completionFromParts___redArg", "authorizeFromCitation___redArg",
            "extractionFromSupport___redArg", "ControlResources_readCode___redArg",
            "ControlReference_positionCode___redArg", "extractionProducer___redArg",
            "Selection_seed___redArg", "Master_Stage_preservation___redArg")
    names = {key: select(functions, base + key) for key in keys}
    def callbacks(key, count):
        return [select(functions, base + key + "___lam__" + str(i)) for i in range(count)]
    extract = callbacks("ControlCitation_extractCode", 6)
    readout = callbacks("ControlCitation_readoutCode___redArg", 3)
    complete = callbacks("ControlCompletion_completeCode___redArg", 8)
    decide = callbacks("ControlCompletion_decideCode___redArg", 7)
    assignment = callbacks("ControlCompletion_assignmentCode___redArg", 1)
    scope = extract + readout + complete + decide + assignment + [names[key] for key in keys[:9]]

    def one(body, target):
        calls = list(re.finditer(r"\b" + re.escape(names[target]) + r"\s*\(([^;]*)\);", body))
        if len(calls) != 1:
            raise ValueError("Expected one actual completion call: " + target)
        return calls[0]

    def stored(body, operation, field, variable):
        if not re.search(operation + r"\([^,]+, " + str(field) + r", v_" + variable + r"_\d+_\)", body):
            raise ValueError("Completion drops actual " + variable)

    def step(body, callback, label):
        found = re.search(r"(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(" + re.escape(callback) + r"(?:___boxed)?\)", body)
        if found is None or not re.search(r"lean_ctor_set\([^,]+, 1, " + re.escape(found[1]) + r"\)", body):
            raise ValueError("Completion paid callback missing")
        if not re.search(r"= " + str(label) + r";", body) or "lean_alloc_ctor(1, 2, 0)" not in body:
            raise ValueError("Completion paid label missing")

    owners = (("extractionProducer___redArg", extract[5]), ("ControlResources_readCode___redArg", extract[5]),
              ("ControlReference_positionCode___redArg", names["ControlCitation_readoutCode___redArg"]),
              ("ControlResources_readCode___redArg", readout[2]),
              ("ControlCompletion_assignmentCode___redArg", names["ControlCompletion_completeCode___redArg"]),
              ("Master_Stage_candidateFromBit___redArg", complete[5]),
              ("ControlCitation_extractCode", complete[5]), ("ControlCitation_readoutCode___redArg", complete[4]),
              ("authorizeFromCitation___redArg", complete[2]), ("Master_completionFromParts___redArg", complete[0]),
              ("Selection_seed___redArg", decide[6]), ("Master_Stage_preservation___redArg", decide[4]),
              ("ControlCompletion_completeCode___redArg", decide[3]),
              ("ControlCompletion_assignmentCode___redArg", assignment[0]))
    steps = ((names["ControlCitation_extractCode"], extract[5], 49), (extract[4], extract[3], 23),
             (extract[3], extract[2], 24), (extract[2], extract[1], 25), (extract[1], extract[0], 2),
             (readout[1], readout[0], 36), (complete[7], complete[6], 47), (complete[6], complete[5], 48),
             (complete[3], complete[2], 50), (complete[2], complete[1], 51), (complete[1], complete[0], 52),
             (names["ControlCompletion_decideCode___redArg"], decide[6], 42),
             (decide[6], decide[5], 43), (decide[5], decide[4], 44), (decide[4], decide[3], 45),
             (decide[1], decide[0], 53),
             (names["ControlCompletion_assignmentCode___redArg"], assignment[0], 46))
    names["incorporate"] = select(functions, base + "incorporate___redArg")
    names["formula"] = select(functions, base + "Master_Stage_formula___redArg")
    names["flag"] = select(functions, base + "Selection_Checked_flag___redArg")
    bounds = {key: select(functions, base + key) for key in
              ("ControlMaster_runBound___redArg", "ControlCompletion_pairBound___redArg",
               "ControlCompletion_sourceWorkBound___redArg")}
    owners += (("incorporate", complete[1]), ("formula", decide[5]))

    def check(current):
        for name in bounds.values():
            if re.search(r"\b\w*(?:Documentary_Master_(?:search|run|decide|complete)|Documentary_Selection_seed|"
                         r"Documentary_extract|Documentary_ControlCompletion_(?:decideCode|completeCode))"
                         r"(?:___redArg)?\s*\(", current[name]) or re.search(r"\blean_apply_\d+\s*\(", current[name]):
                raise ValueError("Driver envelope evaluates a producer or deferred continuation")
        pair = bounds["ControlCompletion_pairBound___redArg"]
        if len(re.findall(r"\b" + re.escape(pair) + r"\s*\(", current[bounds["ControlMaster_runBound___redArg"]])) != 1:
            raise ValueError("Driver does not use the structural pair envelope once")
        work = bounds["ControlCompletion_sourceWorkBound___redArg"]
        found = re.findall(r"\b" + re.escape(work) + r"\((v_(?:left|right)_\d+_)\);", current[pair])
        if len(found) != 2 or "left" not in found[0] or "right" not in found[1]:
            raise ValueError("Pair envelope substitutes a received source reference")
        for name in scope:
            if re.search(r"\b\w*(?:Documentary_Master_(?:decide|complete)|Documentary_Master_Stage_candidate|"
                         r"Documentary_Selection_frontierAssignment|Documentary_(?:extract|authorize|sourceCitation)|"
                         r"Resources_(?:Ref_position|read|Support_read|Support_extend|Producer_arguments))"
                         r"(?:___redArg)?\s*\(", current[name]):
                raise ValueError("Native completion, extraction or traversal replayed")
            if name not in (decide[3], complete[6]) and re.search(r"\blean_apply_\d+\s*\(", current[name]):
                raise ValueError("Deferred operation outside its paid callback")
        for target, owner in owners:
            one(current[owner], target)
        for target in {target for target, _ in owners}:
            allowed = {owner for candidate, owner in owners if candidate == target}
            for name in scope:
                if name not in allowed and re.search(r"\b" + re.escape(names[target]) + r"\s*\(", current[name]):
                    raise ValueError("Completion operation outside its named callback: " + target)
        for owner, callback, label in steps:
            step(current[owner], callback, label)
        if not re.search(r"lean_apply_1\(v_forward_\d+_, v_input_\d+_\)", current[decide[3]]) or current[decide[3]].count("lean_apply_1(") != 1:
            raise ValueError("Routing must apply the actual preservation to the actual input once")
        if not re.search(r"lean_apply_1\(v_assignment_\d+_, v___x_\d+_\)", current[complete[6]]) or current[complete[6]].count("lean_apply_1(") != 1:
            raise ValueError("Candidate bit must apply the actual retained assignment once")
        if not re.search(r"lean_ctor_get\(v_preservation_\d+_, 0\)", current[decide[3]]):
            raise ValueError("Routing substitutes its actual preservation")
        for owner, target in ((decide[4], "Master_Stage_preservation___redArg"), (decide[5], "formula")):
            if not re.search(r"\(v_stage_\d+_\);", one(current[owner], target)[0]):
                raise ValueError("Routing substitutes its actual stage")
        if not re.search(r"\(v_left_\d+_, v_right_\d+_, v_stage_\d+_, v_bit_\d+_\);", one(current[complete[5]], "Master_Stage_candidateFromBit___redArg")[0]):
            raise ValueError("Candidate substitutes its received pair or stage")
        body = current[decide[6]]
        for field, variable in ((1, "leftCheck"), (2, "rightCheck")):
            if not re.search(r"v_" + variable + r"_\d+_ = lean_ctor_get\(v_stage_\d+_, " + str(field) + r"\)", body):
                raise ValueError("Seed substitutes an actual source check")
        flags = list(re.finditer(r"(\w+)\s*=\s*" + re.escape(names["flag"]) + r"\((v_(?:leftCheck|rightCheck)_\d+_)\);", body))
        if len(flags) != 2 or "leftCheck" not in flags[0][2] or "rightCheck" not in flags[1][2] or one(body, "Selection_seed___redArg")[1].split(", ") != [flags[0][1], flags[1][1]]:
            raise ValueError("Seed does not consume both actual source flags")
        body = current[extract[5]]
        for field, variable in ((0, "fst"), (1, "snd")):
            if not re.search(r"v_" + variable + r"_\d+_ = lean_ctor_get\(v_origin_\d+_, " + str(field) + r"\)", body):
                raise ValueError("Extraction substitutes the received source occurrence")
        if not re.search(r"\(v_fst_\d+_, v_snd_\d+_\);", one(body, "extractionProducer___redArg")[0]) or not re.search(r", v_values_\d+_, v_snd_\d+_\);", one(body, "ControlResources_readCode___redArg")[0]):
            raise ValueError("Extraction does not consume the same received source port")
        for owner, target, variable in ((decide[3], "ControlCompletion_completeCode___redArg", "retained"),
                                       (complete[5], "Master_Stage_candidateFromBit___redArg", "bit"),
                                       (complete[5], "ControlCitation_extractCode", "origin"),
                                       (complete[4], "ControlCitation_readoutCode___redArg", "action"),
                                       (names["ControlCompletion_completeCode___redArg"], "ControlCompletion_assignmentCode___redArg", "continuation")):
            if not re.search(r",? ?v_" + variable + r"_\d+_\);", one(current[owner], target)[0]):
                raise ValueError("Completion substitutes actual " + variable)
        for owner, operation, field, variable in (
            (extract[3], "lean_ctor_set", 0, "readout"), (extract[2], "lean_ctor_set", 2, "formation"),
            (extract[2], "lean_ctor_set", 3, "producer"), (extract[1], "lean_ctor_set", 0, "values"),
            (extract[1], "lean_ctor_set", 1, "retained"), (extract[0], "lean_ctor_set", 0, "resources"),
            (readout[0], "lean_ctor_set", 0, "fst"), (readout[0], "lean_ctor_set", 1, "position"),
            (readout[0], "lean_ctor_set", 2, "passage"), (complete[6], "lean_closure_set", 3, "bit"),
            (complete[3], "lean_closure_set", 2, "readout"), (complete[1], "lean_closure_set", 6, "result"),
            (decide[0], "lean_ctor_set", 0, "packet"),
            (decide[5], "lean_ctor_set", 2, "assignment"), (decide[5], "lean_closure_set", 1, "input"),
            (decide[4], "lean_closure_set", 0, "preservation"), (decide[4], "lean_closure_set", 1, "input"),
            (names["ControlCompletion_decideCode___redArg"], "lean_closure_set", 0, "stage"),
            (names["ControlCompletion_decideCode___redArg"], "lean_closure_set", 6, "memory"),
            (names["authorizeFromCitation___redArg"], "lean_ctor_set", 0, "item"),
            (names["authorizeFromCitation___redArg"], "lean_ctor_set", 1, "permission")):
            stored(current[owner], operation, field, variable)
        for field, variable in enumerate(("continuation", "candidate", "action", "output", "result")):
            stored(current[names["Master_completionFromParts___redArg"]], "lean_ctor_set", field, variable)
        if not re.search(r"return v_resources_\d+_;", current[names["extractionFromSupport___redArg"]]):
            raise ValueError("Action factory does not retain its actual support")
        if not re.search(r"\(v_origin_\d+_, v_permission_\d+_, v_readout_\d+_\);", one(current[complete[2]], "authorizeFromCitation___redArg")[0]):
            raise ValueError("Admission substitutes origin, permission or readout")
        if not re.search(r"\(v_memory_\d+_, v_output_\d+_\);", one(current[complete[1]], "incorporate")[0]):
            raise ValueError("Incorporation substitutes the actual memory or output")

    mutations = [(name, functions[name] + " lp_forbidden_Documentary_Master_complete();") for name in scope]
    mutations += [(name, functions[name] + " lp_forbidden_Documentary_Master_search();") for name in bounds.values()]
    for variable in ("left", "right"):
        owner = bounds["ControlCompletion_pairBound___redArg"]
        mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    mutations += [(owner, functions[owner] + names[target] + "();") for target, owner in owners]
    mutations += [(owner, functions[owner].replace("= " + str(label) + ";", "= 0;")) for owner, _, label in steps]
    for owner, variable in ((decide[3], "forward"), (decide[3], "input"), (decide[3], "retained"),
                            (decide[3], "preservation"), (decide[4], "stage"), (decide[5], "stage"),
                            (decide[5], "assignment"), (decide[6], "leftCheck"), (decide[6], "rightCheck"),
                            (extract[5], "origin"), (extract[5], "snd"),
                            (complete[5], "stage"), (complete[5], "left"), (complete[5], "right"),
                            (complete[6], "assignment"), (complete[5], "bit"), (complete[4], "action"),
                            (complete[2], "permission"), (complete[2], "readout"),
                            (complete[1], "memory"), (complete[1], "output"), (complete[1], "result"),
                            (extract[3], "readout"), (extract[2], "formation"), (extract[2], "producer"),
                            (readout[0], "position"), (readout[0], "passage"), (decide[0], "packet")):
        mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    for variable in ("continuation", "candidate", "action", "output", "result"):
        owner = names["Master_completionFromParts___redArg"]
        mutations.append((owner, re.sub(r"v_" + variable + r"_\d+_", "v_substituted", functions[owner])))
    return check, mutations


def verify(functions, select):
    check, mutations = make_check(functions, select)
    check(functions)
    for name, body in mutations:
        current = dict(functions); current[name] = body
        try:
            check(current)
        except ValueError:
            pass
        else:
            raise ValueError("Completion mutation accepted: " + name)
    print("DOCUMENTARY_COMPLETION_CODEGEN_OK: paid actual continuation, formation, readout and completion; " +
          str(len(mutations)) + " textual mutations rejected; higher-order internals and allocations remain open")


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
        print("DOCUMENTARY_COMPLETION_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
