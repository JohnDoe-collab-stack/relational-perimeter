#!/usr/bin/env python3
"""Direct C guards for the paid arithmetic and formation path.
Checks dataflow and delayed constructors; no physical heap or time claim.
Fixtures mutate these text bodies, not compiled binaries.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = "Agent_Local_Documentary_"


def make_check(functions, select, parameters):
    keys = ("ControlArithmetic_addCode", "ControlArithmetic_differenceCode",
            "ControlArithmetic_sumCode", "ControlArithmetic_negateCode", "ControlArithmetic_code",
            "ControlFormation_code___redArg", "ControlDeduction_code___redArg")
    names = {key: select(functions, BASE + key) for key in keys}

    def callbacks(key, count):
        found = {int(re.search(r"__(\d+)$", name)[1]): name for name in functions
                 if re.search(re.escape(BASE + key) + r"___(?:lam|elam)__\d+$", name)}
        if len(found) != count:
            raise ValueError("Unexpected arithmetic/formation callbacks: " + key)
        return found

    add = callbacks("ControlArithmetic_addCode", 3)
    difference = callbacks("ControlArithmetic_differenceCode", 2)
    # Compiler hoists two identity continuations; only the paid sign dispatcher
    # and the two delayed sign-return constructors remain in this prefix.
    sums = callbacks("ControlArithmetic_sumCode", 5)
    negative = callbacks("ControlArithmetic_negateCode", 1)
    operation = callbacks("ControlArithmetic_code", 2)
    formation = callbacks("ControlFormation_code___redArg", 4)
    deduction = callbacks("ControlDeduction_code___redArg", 7)
    bind_name = select(functions, BASE + "Control_Code_bind___redArg")
    continuation_edges = []
    for parent, child, slot in ((5, 4, 2), (4, 3, 2), (3, 2, 3)):
        closure = re.search(r"(\w+) = lean_alloc_closure\(\(void\*\)\(" + re.escape(deduction[child]) + r"\)", functions[deduction[parent]])
        if closure is None:
            raise ValueError("Accepted continuation edge missing")
        continuation_edges.append((deduction[parent], r"lean_closure_set\(" + re.escape(closure[1]) + ", " + str(slot) + ", " +
                                   re.escape(parameters[deduction[parent]][2]) + r"\)"))
    continuation_edges.append((deduction[2], re.escape(bind_name) + r"\([^;]*, " +
                               re.escape(parameters[deduction[2]][3]) + r"\);"))
    scope = list(names.values())
    for group in (add, difference, sums, negative, operation, formation, deduction):
        scope += list(group.values())
    forbidden = [select(functions, BASE + key) for key in
                 ("Deduction_evaluate", "Deduction_producer___redArg",
                  "Deduction_execute___redArg", "Deduction_form___redArg",
                  "Deduction_formFromProducerReads___redArg")]
    forbidden += [select(functions, "Resources_" + key + "___redArg") for key in
                  ("read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend")]

    def require(body, pattern, message):
        if not re.search(pattern, body):
            raise ValueError(message)

    def call(body, key):
        found = list(re.finditer(r"\b" + re.escape(names[key]) + r"\(([^;]*)\);", body))
        if len(found) != 1:
            raise ValueError("Expected one actual call: " + key)
        return found[0]

    def step(body, callback, label):
        closure = re.search(r"(\w+) = lean_alloc_closure\(\(void\*\)\(" + re.escape(callback) +
                            r"(?:___boxed)?\)", body)
        if closure is None:
            raise ValueError("Paid callback missing")
        require(body, r"lean_ctor_set\([^,]+, 1, " + re.escape(closure[1]) + r"\)",
                "Paid callback is not stored")
        require(body, r"= " + str(label) + r";", "Incorrect paid label")

    def check(current):
        for name, pattern in continuation_edges:
            require(current[name], pattern, "Deduction drops its actual accepted continuation")
        for name in scope:
            body = current[name]
            for key, owner in (("ControlFormation_code___redArg", deduction[2]),
                               ("ControlArithmetic_code", deduction[3])):
                if name != owner and re.search(r"\b" + re.escape(names[key]) + r"\s*\(", body):
                    raise ValueError("Computation outside its actual continuation")
            if any(re.search(r"\b" + re.escape(target) + r"\s*\(", body) for target in forbidden):
                raise ValueError("Arithmetic/formation replays the original operation or traversal")
            if re.search(r"\blean_int_(?:add|sub|mul)\(", body):
                raise ValueError("Whole input arithmetic in the controlled path")
        for key, child, label in (
            ("ControlArithmetic_addCode", add[2], 17),
            ("ControlArithmetic_differenceCode", difference[1], 17),
            ("ControlArithmetic_sumCode", sums[3], 19),
            ("ControlArithmetic_negateCode", negative[0], 22),
            ("ControlArithmetic_code", operation[0], 21),
            ("ControlFormation_code___redArg", formation[3], 23)):
            body = current[names[key]]
            if re.search(r"\b(?:lean_apply\w*|lean_nat_dec_eq|lean_nat_sub|lean_int_dec_lt|lean_int_to_nat|lean_obj_tag|lean_ctor_get)\(", body):
                raise ValueError("Factory inspects an input before payment")
            step(body, child, label)
        step(current[add[1]], add[0], 18)
        for parent, child, label in ((3, 2, 24), (2, 1, 25), (1, 0, 3)):
            step(current[formation[parent]], formation[child], label)
        for slot, variable in ((0, "computed"), (2, "producer")):
            require(current[names["ControlFormation_code___redArg"]],
                    r"lean_closure_set\([^,]+, " + str(slot + (1 if slot == 0 else 0)) +
                    r", v_" + variable + r"_\d+_\)", "Formation drops its actual input")
        body = current[formation[3]]
        require(body, r"lean_ctor_set\([^,]+, 0, v_computed_\d+_\)", "Formation replaces the computed value")
        require(body, r"lean_closure_set\([^,]+, 3, v_formation_\d+_\)", "Formation replaces the prior witness")
        body = current[formation[2]]
        formed = re.search(r"(\w+) = lean_ctor_get\(v_producer_\d+_, 0\)", body)
        if formed is None:
            raise ValueError("Actual producer field is not consumed")
        for slot, variable in ((0, r"v_kinds_\d+_"), (1, r"v_values_\d+_"),
                               (2, r"v_formation_\d+_"), (3, re.escape(formed[1]))):
            require(body, r"lean_ctor_set\(v_retained_\d+_, " + str(slot) + ", " + variable + r"\)",
                    "Positive formation replaces a constitutive field")
        body = current[formation[1]]
        for slot, variable in ((0, "values"), (1, "retained")):
            require(body, r"lean_ctor_set\(v_resources_\d+_, " + str(slot) + r", v_" + variable + r"_\d+_\)",
                    "Support replaces its actual values or witness")
        require(current[formation[0]], r"lean_ctor_set\([^,]+, 0, v_resources_\d+_\)",
                "Action drops the actual support")
        body = current[deduction[3]]
        tag = re.search(r"(\w+) = lean_ctor_get_uint8\(v_producer_\d+_, sizeof\(void\*\)\*1\)", body)
        if tag is None:
            raise ValueError("Catalogue tag not read from the actual producer packet")
        actual_call = call(body, "ControlArithmetic_code")
        if not re.fullmatch(re.escape(tag[1]) + r", v_leftRead_\d+_, v_rightRead_\d+_", actual_call[1]):
            raise ValueError("Arithmetic replaces the catalogue or actual arguments")
        require(body, r"lean_closure_set\([^,]+, 2, v_producer_\d+_\)", "Formation drops actual producer")
        body = current[deduction[2]]
        if not re.fullmatch(r"v_kinds_\d+_, v_knowledge_\d+_, v_producer_\d+_, v_computed_\d+_",
                            call(body, "ControlFormation_code___redArg")[1]):
            raise ValueError("Formation substitutes the arithmetic result")
        body = current[deduction[1]]
        for slot, variable in ((0, "action"), (1, "val")):
            require(body, r"lean_ctor_set\([^,]+, " + str(slot) + r", v_" + variable + r"_\d+_\)",
                    "Accepted decision drops actual action or permission")
        body = current[add[0]]
        require(body, r"lean_nat_add\(v_actual_\d+_, v___x_\d+_\)", "Arithmetic return replaces recursive output")
        require(body, r"lean_unsigned_to_nat\(1u\)", "Arithmetic return uses a different successor")
        body = current[add[2]]
        require(body, r"lean_nat_sub\(v_right_\d+_, v_one_\d+_\)", "Addition does not descend actual right input")
        if not re.fullmatch(r"v_left_\d+_, v_n_\d+_", call(body, "ControlArithmetic_addCode")[1]):
            raise ValueError("Addition replaces received left input or recursive right tail")
        # The recursion uses the actual decremented naturals; both are inspected
        # inside the paid callback, including the mixed-sign cancellation.
        if current[difference[1]].count("lean_nat_sub(") != 2:
            raise ValueError("Difference must descend both actual natural inputs")
        require(current[difference[1]], r"ControlArithmetic_differenceCode\(v_n_\d+_, v_n_\d+_\)",
                "Difference replaces its actual recursive inputs")
        call(current[operation[2]], "ControlArithmetic_sumCode")
        if not re.fullmatch(r"v_right_\d+_, v_negative_\d+_",
                            call(current[operation[2]], "ControlArithmetic_sumCode")[1]):
            raise ValueError("Subtraction replaces the actual negation")

    return check, scope, names, formation, deduction, add, continuation_edges


def verify(functions, select, parameters):
    check, scope, names, formation, deduction, add, continuation_edges = make_check(functions, select, parameters)
    check(functions)
    mutations = [(name, functions[name] + "lean_int_add(x, y);") for name in scope]
    for name, pattern in continuation_edges:
        changed = re.sub(pattern, "substituted_accepted_continuation();", functions[name])
        if changed == functions[name]:
            raise ValueError("Empty accepted continuation mutation")
        mutations.append((name, changed))
    for name, pattern in (
        (deduction[3], r"v_leftRead_\d+_"), (deduction[3], r"v_rightRead_\d+_"),
        (deduction[3], r"(?<=\()v_operation_\d+_"), (deduction[2], r"v_computed_\d+_"),
        (deduction[2], r"v_producer_\d+_"), (deduction[1], r"(?<=1, )v_val_\d+_"),
        (deduction[1], r"(?<=0, )v_action_\d+_"),
        (formation[3], r"(?<=0, )v_computed_\d+_"),
        (formation[2], r"(?<=2, )v_formation_\d+_"), (formation[2], r"(?<=3, )v_formed_\d+_"),
        (formation[1], r"(?<=1, )v_retained_\d+_"), (formation[0], r"(?<=0, )v_resources_\d+_"),
        (add[0], r"v_actual_\d+_")):
        changed = re.sub(pattern, "v_substituted", functions[name])
        if changed == functions[name]:
            raise ValueError("Empty arithmetic mutation")
        mutations.append((name, changed))
    for key in ("ControlArithmetic_code", "ControlArithmetic_addCode", "ControlFormation_code___redArg"):
        mutations.append((names[key], functions[names[key]] + "lean_nat_dec_eq(x, y);"))
    for name, changed in mutations:
        current = dict(functions); current[name] = changed
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError("Arithmetic/formation mutation accepted: " + name)
    print("DOCUMENTARY_ARITHMETIC_CODEGEN_OK: paid structural arithmetic, same catalogue/read arguments, "
          "shared computed value/producer/prior formation/support; " + str(len(mutations)) +
          " textual mutations rejected; direct-body/closure scope")


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}; texts = []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        source = path.read_text(encoding="utf-8"); texts.append(source)
        functions.update(agent["bodies_with_objects"](source))
    verify(functions, agent["shared"]["select"], agent["parameters"](texts))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("DOCUMENTARY_ARITHMETIC_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
