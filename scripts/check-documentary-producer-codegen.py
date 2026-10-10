#!/usr/bin/env python3
"""Pinned named C bodies for paid producer construction and actual captures.

Textual fixtures check these guards, not compiled mutants or physical costs.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def verify(functions, select, parameters):
    base = "Agent_Local_Documentary_"
    names = {key: select(functions, base + key) for key in
             ("ControlProducer_code___redArg", "ControlProducer_buildCode___redArg", "Deduction_evaluate",
              "Deduction_producer___redArg", "Deduction_form___redArg", "Deduction_execute___redArg")}
    names["position"] = select(functions, base + "ControlReference_positionCode___redArg")
    for key in ("Ref_position", "read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend"):
        names[key] = select(functions, "Resources_" + key + "___redArg")

    def callbacks(prefix, count):
        matches = {int(re.search(r"__(\d+)$", name)[1]): name for name in functions
                   if re.search(re.escape(base + prefix) + r"___lam__\d+$", name)}
        if len(matches) != count:
            raise ValueError("Unexpected producer callbacks: " + prefix)
        return matches

    build = callbacks("ControlProducer_buildCode___redArg", 10)
    run = callbacks("ControlProducer_code___redArg", 2)
    scope = list(build.values()) + list(run.values()) + [names["ControlProducer_code___redArg"],
                                                       names["ControlProducer_buildCode___redArg"]]

    def call(body, key):
        found = list(re.finditer(r"\b" + re.escape(names[key]) + r"\(([^;]+)\);", body))
        if len(found) != 1:
            raise ValueError("Expected one producer call: " + key)
        return found[0]

    def field(body, object_pattern, slot, variable):
        if not re.search(r"lean_ctor_set\(" + object_pattern + ", " + str(slot) + ", v_" + variable + r"_\d+_\)", body):
            raise ValueError("Producer field substitutes " + variable)

    def step(body, child, label, pass_slot=None):
        closure = re.search(r"(\w+) = lean_alloc_closure\(\(void\*\)\(" + re.escape(child) +
                            r"(?:___boxed)?\)", body)
        if closure is None:
            raise ValueError("Missing delayed producer constructor")
        stored = re.search(r"lean_ctor_set\((\w+), 1, " + re.escape(closure[1]) + r"\)", body)
        if stored is None:
            raise ValueError("Producer step does not retain its continuation")
        boxed = re.search(r"lean_ctor_set\(" + re.escape(stored[1]) + r", 0, (\w+)\)", body)
        if boxed is None:
            raise ValueError("Producer step has no label")
        primitive = re.search(re.escape(boxed[1]) + r" = lean_box\((\w+)\)", body)
        if primitive is None:
            raise ValueError("Producer label is not boxed from its actual primitive")
        if label is not None and not re.search(re.escape(primitive[1]) + " = " + str(label) + ";", body):
            raise ValueError("Wrong producer label")
        if label is None and (not re.fullmatch(r"v___x_\d+_", primitive[1]) or
                              re.search(re.escape(primitive[1]) + r"\s*=", body)):
            raise ValueError("Producer label was not received from its paid parent")
        if pass_slot is not None:
            captured = re.search(r"lean_closure_set\(" + re.escape(closure[1]) + ", " + str(pass_slot) + r", (\w+)\)", body)
            if captured is None or not re.search(re.escape(captured[1]) + r" = lean_box\(" + re.escape(primitive[1]) + r"\)", body):
                raise ValueError("Producer constructor changes its repeated cell label")

    def check(current):
        for name in scope:
            if any(re.search(r"\b" + re.escape(names[key]) + r"\s*\(", current[name]) for key in
                   ("Ref_position", "read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend",
                    "Deduction_producer___redArg", "Deduction_form___redArg", "Deduction_execute___redArg")):
                raise ValueError("Producer reconstruction or original traversal in paid construction")
            if "lean_apply" in current[name] or "lean_obj_tag" in current[name]:
                raise ValueError("Producer factory/constructor enters an unrelated computation")
        step(current[names["ControlProducer_buildCode___redArg"]], build[9], 13, 8)
        for parent, child, label, passed in ((9, 8, None, 9), (8, 7, None, None),
                                           (7, 6, 14, 11), (6, 5, None, 12), (5, 4, None, None),
                                           (4, 3, 15, None), (3, 2, 16, None)):
            step(current[build[parent]], build[child], label, passed)
        body = current[build[8]]
        field(body, r"v_rightKinds_\d+_", 0, "right")
        field(body, r"v_rightKinds_\d+_", 1, "emptyKinds")
        body = current[build[7]]
        field(body, r"v_inputKinds_\d+_", 0, "left")
        field(body, r"v_inputKinds_\d+_", 1, "rightKinds")
        body = current[build[5]]
        field(body, r"v_rightPorts_\d+_", 2, "rightRef")
        field(body, r"v_rightPorts_\d+_", 3, "emptyPorts")
        body = current[build[4]]
        field(body, r"v_inputs_\d+_", 2, "leftRef")
        field(body, r"v_inputs_\d+_", 3, "rightPorts")
        body = current[build[3]]
        for slot, variable in ((1, "rulePosition"), (3, "leftPosition"), (5, "rightPosition")):
            field(body, r"v_outputKind_\d+_", slot, variable)
        if not re.search(r"lean_closure_set\([^,]+, 0, v_outputKind_\d+_\)", body):
            raise ValueError("Output-kind getter does not retain the constructed kind")
        if build[0] + "___boxed)" not in body or build[1] + "___boxed)" not in body:
            raise ValueError("Producer substitutes its operation or kind closure")
        closures = {}
        for key, callback in (("operation", build[0]), ("kind", build[1]), ("assembly", build[2])):
            match = re.search(r"(\w+) = lean_alloc_closure\(\(void\*\)\(" + re.escape(callback) +
                              r"(?:___boxed)?\)", body)
            if match is None:
                raise ValueError("Missing actual producer closure: " + key)
            closures[key] = match[1]
        for slot, key in ((3, "kind"), (4, "operation")):
            if not re.search(r"lean_closure_set\(" + re.escape(closures["assembly"]) + ", " + str(slot) +
                             ", " + re.escape(closures[key]) + r"\)", body):
                raise ValueError("Producer swaps its kind and operation captures")
        body = current[build[2]]
        field(body, r"v_formed_\d+_", 0, "inputKinds")
        field(body, r"v_formed_\d+_", 1, "inputs")
        for slot in (2, 3):
            if not re.search(r"lean_ctor_set\(v_formed_\d+_, " + str(slot) + ", " +
                             re.escape(parameters[build[2]][slot + 1]) + r"\)", body):
                raise ValueError("Producer swaps its kind and operation fields")
        if not re.search(r"lean_ctor_set\([^,]+, 0, v_formed_\d+_\)", body):
            raise ValueError("Producer result drops its actual assembled value")
        tag = re.search(r"(\w+) = lean_ctor_get_uint8\((v_fst_\d+_), sizeof\(void\*\)\*1\)", current[build[2]])
        if tag is None or not re.search(r"lean_ctor_set_uint8\([^,]+, sizeof\(void\*\)\*1, " + re.escape(tag[1]) + r"\)", current[build[2]]):
            raise ValueError("Catalogue tag is not retained from the actual rule")
        rule = re.search(r"(v_fst_\d+_) = lean_ctor_get\(v_request_\d+_, 0\)", current[build[3]])
        if rule is None or not re.search(r"lean_closure_set\(" + re.escape(closures["assembly"]) + r", 0, " + re.escape(rule[1]) + r"\)", current[build[3]]) or not re.search(r"lean_closure_set\(" + re.escape(closures["operation"]) + r", 0, " + re.escape(rule[1]) + r"\)", current[build[3]]):
            raise ValueError("Operation and catalogue tag do not receive the same rule")
        body = current[build[0]]
        call(body, "Deduction_evaluate")
        if len(re.findall(r"lean_ctor_get\(v_arguments_\d+_, 0\)", body)) != 1 or \
                len(re.findall(r"lean_ctor_get\(v_arguments_\d+_, 1\)", body)) != 1:
            raise ValueError("Producer operation does not consume its actual arguments")
        body = current[names["ControlProducer_code___redArg"]]
        if not re.search(r"\(v_leftRef_\d+_\);", call(body, "position")[0]):
            raise ValueError("Producer substitutes its left reference position")
        position_owner = next(name for name in run.values() if names["position"] + "(" in current[name])
        if not re.search(r"\(v_rightRef_\d+_\);", call(current[position_owner], "position")[0]):
            raise ValueError("Producer substitutes its right reference position")
        builder = next(name for name in run.values() if names["ControlProducer_buildCode___redArg"] + "(" in current[name])
        if not re.search(r", v_rulePosition_\d+_, v_leftPosition_\d+_, v_rightPosition_\d+_\);",
                         call(current[builder], "ControlProducer_buildCode___redArg")[0]):
            raise ValueError("Producer builder substitutes its three paid positions")

    check(functions)
    mutations = []
    mutations.append((build[2], re.sub(r"(?<=\*1, )v_operation_\d+_", "v_other_operation", functions[build[2]])))
    mutations.append((build[3], re.sub(r"(?<=0, )v_fst_\d+_", "v_other_rule", functions[build[3]])))
    for key in ("Ref_position", "read", "Support_read", "Producer_arguments", "Deduction_producer___redArg"):
        for name in (names["ControlProducer_buildCode___redArg"], build[3]):
            mutations.append((name, functions[name] + names[key] + "();"))
    for name, old, new in ((names["ControlProducer_buildCode___redArg"], "= 13;", "= 14;"),
                           (build[7], "= 14;", "= 13;"), (build[4], "= 15;", "= 14;"),
                           (build[3], "= 16;", "= 15;")):
        mutations.append((name, functions[name].replace(old, new)))
    for name, pattern in ((build[8], r"(?<=0, )v_right_\d+_"), (build[7], r"(?<=1, )v_rightKinds_\d+_"),
                          (build[5], r"(?<=2, )v_rightRef_\d+_"), (build[4], r"(?<=2, )v_leftRef_\d+_"),
                          (build[3], r"(?<=1, )v_rulePosition_\d+_"), (build[3], r"(?<=3, )v_leftPosition_\d+_"),
                          (build[3], r"(?<=5, )v_rightPosition_\d+_"),
                          (build[2], r"(?<=0, )v_inputKinds_\d+_"), (build[2], r"(?<=1, )v_inputs_\d+_")):
        mutations.append((name, re.sub(pattern, "v_other_packet", functions[name])))
    for name in (names["ControlProducer_buildCode___redArg"], build[3]):
        mutations.append((name, functions[name] + "lean_apply_1(x, y);"))
    for name in (build[9], build[6]):
        label = re.search(r"(v___x_\d+_) = lean_box\((v___x_\d+_)\)", functions[name])
        if label is None:
            raise ValueError("Missing repeated-label fixture site")
        mutations.append((name, functions[name] + label[2] + " = 0;"))
    for slot, other in ((2, 3), (3, 2)):
        mutations.append((build[2], re.sub(r"(?<=" + str(slot) + ", )" +
                         re.escape(parameters[build[2]][slot + 1]), parameters[build[2]][other + 1], functions[build[2]])))
    for slot in (3, 4):
        mutations.append((build[3], re.sub(r"(lean_closure_set\([^,]+, " + str(slot) +
                         r", )v___f_\d+_(\))", r"\1v_other_closure\2", functions[build[3]])))
    for name, changed in mutations:
        mutated = dict(functions)
        mutated[name] = changed
        try:
            check(mutated)
        except ValueError:
            continue
        raise ValueError("Bad producer mutation accepted: " + name)
    print("DOCUMENTARY_PRODUCER_CODEGEN_OK: eight paid constructors, ordered original ports, three paid positions, "
          "actual producer and same-rule catalogue tag returned; " + str(len(mutations)) + " mutations rejected; named direct-body/closure scope")


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    texts = []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        source = path.read_text(encoding="utf-8")
        texts.append(source)
        functions.update(agent["bodies_with_objects"](source))
    verify(functions, agent["shared"]["select"], agent["parameters"](texts))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print("DOCUMENTARY_PRODUCER_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
