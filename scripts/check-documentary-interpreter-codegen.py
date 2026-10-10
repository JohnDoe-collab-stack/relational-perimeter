#!/usr/bin/env python3
"""Named C checks for paid entry, actual reads and positive producer sharing.

Checks named direct bodies and their closure edges, not complete call graphs,
heap or CPU bounds. Mutation fixtures exercise this checker, not mutant builds.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def main():
    agent = runpy.run_path(str(ROOT / "scripts/check-agent-codegen.py"))
    functions = {}
    texts = []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        source = path.read_text(encoding="utf-8")
        texts.append(source)
        functions.update(agent["bodies_with_objects"](source))
    select = agent["shared"]["select"]
    base = "Agent_Local_Documentary_"
    keys = ("Control_execute___redArg", "Control_Result_sound___redArg",
            "ControlStep_code___redArg", "ControlStep_complete___redArg",
            "ControlDeduction_code___redArg", "Deduction_form___redArg",
            "Deduction_formFromProducerReads___redArg", "Deduction_evaluate", "Deduction_producer___redArg",
            "ControlProducer_code___redArg", "ControlPermission_locatedLookup___redArg",
            "ControlResources_readCode___redArg", "ControlFormation_code___redArg", "ControlArithmetic_code",
            "Deduction_execute___redArg", "Dossier_step",
            "Program_quotationStep___redArg", "Program_deductionStep___redArg", "ControlAssembly_code___redArg",
            "Program_step___redArg", "ControlPermission_equalCode",
            "ControlPermission_equalDecision", "ControlPermission_lookupCode",
            "ControlPermission_referencedLookup___redArg", "ControlReference_positionCode___redArg",
            "ControlPermission_present___redArg", "ControlPermission_previous___redArg")
    names = {key: select(functions, base + key) for key in keys}
    names["resolvePermission"] = select(functions, "Agent_resolvePermission")
    names["Ref_position"] = select(functions, "Resources_Ref_position___redArg")
    for key in ("read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend"):
        names[key] = select(functions, "Resources_" + key + "___redArg")

    def callbacks(prefix, count):
        found = [name for name in functions if re.search(re.escape(base + prefix) +
                 r"___(?:lam|elam)__\d+$", name)]
        if len(found) != count:
            raise ValueError("Unexpected lowered callback count: " + prefix)
        return found

    steps = callbacks("ControlStep_code___redArg", 7)
    deductions = callbacks("ControlDeduction_code___redArg", 7)
    resources = callbacks("ControlResources_readCode___redArg", 1)
    lookups = callbacks("ControlPermission_lookupCode", 5)
    comparisons = callbacks("ControlPermission_equalCode", 2)
    references = callbacks("ControlReference_positionCode___redArg", 3)
    referred = callbacks("ControlPermission_referencedLookup___redArg", 2)
    located = callbacks("ControlPermission_locatedLookup___redArg", 2)

    def sites(body, target):
        return list(re.finditer(r"\b" + re.escape(names[target]) + r"\s*\(", body))

    def owner(candidates, target):
        found = [name for name in candidates if sites(functions[name], target)]
        if len(found) != 1:
            raise ValueError("Missing or duplicated owner: " + target)
        return found[0]

    quote = owner(steps, "Dossier_step")
    assembly = owner(steps, "ControlAssembly_code___redArg")
    form = owner(deductions, "ControlFormation_code___redArg")
    form_step = owner(deductions, "ControlArithmetic_code")
    producer_entry = owner(deductions, "ControlProducer_code___redArg")
    choose = next(name for name in deductions if "lean_obj_tag" in functions[name])
    right_read = owner([name for name in deductions if name != choose], "ControlResources_readCode___redArg")
    resource_cell = owner(resources, "ControlResources_readCode___redArg")
    cell = owner(lookups, "ControlPermission_equalCode")
    descend = owner(lookups, "ControlPermission_lookupCode")
    compare = owner(comparisons, "ControlPermission_equalCode")
    prior = owner(lookups, "ControlPermission_previous___redArg")
    position = owner(references, "ControlReference_positionCode___redArg")
    lookup_at = owner(referred, "ControlPermission_lookupCode")
    located_at = owner(located, "ControlPermission_lookupCode")
    located_return = next(name for name in located if name != located_at)
    position_return = next(name for name in references if "lean_nat_add(" in functions[name])
    return_step = next(name for name in references if position_return in functions[name] and name != position_return)

    def block(body, opening):
        depth = 0
        for index in range(opening, len(body)):
            if body[index] == "{":
                depth += 1
            elif body[index] == "}":
                depth -= 1
                if depth == 0:
                    return index + 1
        raise ValueError("Unclosed C branch")

    def call(body, target):
        found = re.search(re.escape(names[target]) + r"\s*\(([^;]+)\);", body)
        if found is None or len(sites(body, target)) != 1:
            raise ValueError("Expected one direct call: " + target)
        return found

    def assigned(body, target):
        found = re.search(r"(\w+)\s*=\s*" + re.escape(names[target]) + r"\s*\(", body)
        call(body, target)
        if found is None:
            raise ValueError("Result assignment missing: " + target)
        return found[1]

    def step_closure(body, callback, label):
        closure = re.search(r"(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(" +
                            re.escape(callback) + r"(?:___boxed)?\)", body)
        if closure is None or not re.search(r"lean_ctor_set\([^,]+, 1, " +
                                           re.escape(closure[1]) + r"\)", body):
            raise ValueError("Paid step does not store its continuation: " + callback)
        if "lean_alloc_ctor(1, 2, 0)" not in body or not re.search(r"= " + str(label) + r";", body):
            raise ValueError("Paid step or expected label missing")

    factories = ("ControlStep_code___redArg", "ControlPermission_equalCode",
                 "ControlPermission_lookupCode", "ControlReference_positionCode___redArg",
                 "ControlResources_readCode___redArg")
    scope = steps + deductions + lookups + comparisons + references + referred + located + resources + [names[key] for key in factories] + [
        names["ControlDeduction_code___redArg"], names["ControlPermission_present___redArg"],
        names["ControlPermission_previous___redArg"], names["ControlPermission_referencedLookup___redArg"],
        names["ControlPermission_locatedLookup___redArg"]]

    arithmetic_check = runpy.run_path(str(ROOT / "scripts/check-documentary-arithmetic-codegen.py"))["make_check"](
        functions, select, agent["parameters"](texts))[0]
    assembly_check = runpy.run_path(str(ROOT / "scripts/check-documentary-assembly-codegen.py"))["make_check"](
        functions, select, agent["parameters"](texts))[0]

    def check(current):
        arithmetic_check(current)
        assembly_check(current)
        body = current[names["Control_execute___redArg"]]
        applications = list(re.finditer(r"\blean_apply_1\s*\(", body))
        recursions = sites(body, "Control_execute___redArg")
        if len(applications) != 1 or len(recursions) != 1:
            raise ValueError("Expected one continuation and one recursive evaluation site")
        guard = re.search(r"if \(v_isZero_\d+_ == 1\)\s*\{", body)
        decrement = re.search(r"\blean_nat_sub\s*\(", body)
        if guard is None or decrement is None:
            raise ValueError("Paid transition guard or decrement missing")
        end = block(body, guard.end() - 1)
        if not end < decrement.start() < applications[0].start() < recursions[0].start():
            raise ValueError("Continuation entered before fuel guard/decrement")
        if "return " not in body[guard.end():end] or "lean_apply" in body[guard.end():end]:
            raise ValueError("Zero-fuel branch must return without continuation")

        for name in scope:
            if any(sites(current[name], target) for target in
                   ("resolvePermission", "ControlPermission_equalDecision", "Deduction_execute___redArg",
                    "Program_step___redArg", "Program_deductionStep___redArg", "Ref_position", "Deduction_form___redArg",
                    "read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend",
                    "Deduction_producer___redArg")):
                raise ValueError("Lowered control replays an original search/step")
            if sites(current[name], "Deduction_formFromProducerReads___redArg"):
                raise ValueError("Formation outside its paid callback")
            if name != quote and sites(current[name], "Dossier_step"):
                raise ValueError("Quotation outside its paid callback")

        body = current[quote]
        produced = assigned(body, "Dossier_step")
        if produced not in call(body, "Program_quotationStep___redArg")[1].split(", "):
            raise ValueError("Quotation assembly substitutes its producer packet")
        body = current[assembly]
        arguments = call(body, "ControlAssembly_code___redArg")[1].split(", ")
        if not re.fullmatch(r"v_actualDecision_\d+_", arguments[-1]):
            raise ValueError("Deduction assembly substitutes the received decision")
        if len(arguments) != 5 or not re.fullmatch(r"v_request_\d+_", arguments[1]):
            raise ValueError("Assembly substitutes the original request")

        body = current[choose]
        permission = re.search(r"(\w+) = lean_ctor_get\(v_snd_\d+_, 0\)", body)
        if permission is None or not re.search(r"lean_closure_set\([^,]+, 0, " +
                                               re.escape(permission[1]) + r"\)", body):
            raise ValueError("Formation closure substitutes actual permission")
        for slot, variable in ((3, "leftRead"),):
            if not re.search(r"lean_closure_set\([^,]+, " + str(slot) + ", v_" + variable + r"_\d+_\)",
                             current[right_read]):
                raise ValueError("Right read drops the received left value or permission")
        for name, ref in ((choose, "leftRef"), (right_read, "rightRef")):
            if not re.search(r", v_" + ref + r"_\d+_\);",
                             call(current[name], "ControlResources_readCode___redArg")[0]):
                raise ValueError("Resource read substitutes its received reference")
        guard = current[choose].index("if (lean_obj_tag")
        end = block(current[choose], current[choose].index("{", guard))
        if sites(current[choose][guard:end], "ControlResources_readCode___redArg"):
            raise ValueError("Refusal reads resources before permission")
        call(current[names["ControlDeduction_code___redArg"]], "ControlPermission_locatedLookup___redArg")
        call(current[names["ControlPermission_referencedLookup___redArg"]], "ControlReference_positionCode___redArg")
        call(current[names["ControlPermission_locatedLookup___redArg"]], "ControlReference_positionCode___redArg")
        if not re.search(r", v_actual_\d+_\);", call(current[located_at], "ControlPermission_lookupCode")[0]):
            raise ValueError("Located lookup substitutes the actually computed position")
        for slot, variable in ((0, "actual"), (1, "permission")):
            if not re.search(r"lean_ctor_set\([^,]+, " + str(slot) + ", v_" + variable + r"_\d+_\)",
                             current[located_return]):
                raise ValueError("Located lookup drops actual position or permission")
        if not re.search(r", v_fst_\d+_\);", call(current[producer_entry], "ControlProducer_code___redArg")[0]):
            raise ValueError("Producer substitutes the retained rule position")
        for name, slot in ((choose, 8), (right_read, 9)):
            if not re.search(r"lean_closure_set\([^,]+, " + str(slot) + r", v_fst_\d+_\)", current[name]):
                raise ValueError("Deduction drops the retained rule position")
        if not re.search(r", v_actual_\d+_\);", call(current[lookup_at], "ControlPermission_lookupCode")[0]):
            raise ValueError("Lookup substitutes its received computed position")

        for key in factories:
            body = current[names[key]]
            if "lean_apply" in body or "lean_obj_tag" in body or "lean_nat_dec_eq" in body:
                raise ValueError("Factory inspects data or enters a continuation before payment")
            if any(sites(body, target) for target in
                   ("ControlPermission_equalCode", "ControlPermission_lookupCode", "ControlReference_positionCode___redArg",
                    "ControlResources_readCode___redArg")):
                raise ValueError("Factory eagerly descends a comparison or permission list")
        step_closure(current[names["ControlPermission_lookupCode"]], cell, 6)
        step_closure(current[names["ControlPermission_equalCode"]], compare, 5)
        step_closure(current[names["ControlReference_positionCode___redArg"]], position, 10)
        step_closure(current[return_step], position_return, 11)
        step_closure(current[names["ControlResources_readCode___redArg"]], resource_cell, 12)
        body = current[resource_cell]
        head = re.search(r"(\w+) = lean_ctor_get\(v_values_\d+_, 0\)", body)
        tail = re.search(r"(\w+) = lean_ctor_get\(v_values_\d+_, 1\)", body)
        ref = re.search(r"(\w+) = lean_ctor_get\(v_ref_\d+_, 3\)", body)
        if head is None or not re.search(r"lean_ctor_set\([^,]+, 0, " + re.escape(head[1]) + r"\)", body):
            raise ValueError("Resource head substitutes the stored value")
        arguments = call(body, "ControlResources_readCode___redArg")[1].split(", ")
        if tail is None or ref is None or arguments[-2:] != [tail[1], ref[1]]:
            raise ValueError("Resource traversal does not descend actual values and reference")

        body = current[names["Deduction_formFromProducerReads___redArg"]]
        if any(sites(body, target) for target in ("read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend",
                                                "Deduction_form___redArg", "Deduction_execute___redArg",
                                                "Deduction_producer___redArg", "Deduction_evaluate")):
            raise ValueError("Formation replays original resource reads or producer")
        operation = re.search(r"(\w+) = lean_ctor_get\((v_formed_\d+_), 3\)", body)
        applied = re.search(r"(\w+) = lean_apply_1\((\w+), (\w+)\)", body)
        if operation is None or applied is None or applied[2] != operation[1] or body.count("lean_apply_1(") != 1:
            raise ValueError("Formation must invoke the actual producer operation once")
        if not re.search(r"lean_ctor_set\(" + re.escape(applied[3]) + r", 0, v_leftValue_\d+_\)", body):
            raise ValueError("Operation substitutes the read left argument")
        if len(re.findall(r"lean_ctor_set\([^,]+, 0, v_rightValue_\d+_\)", body)) != 2:
            raise ValueError("Operation substitutes the read right argument")
        output = applied[1]
        if not re.search(r"lean_ctor_set\([^,]+, 0, " + re.escape(output) + r"\)", body):
            raise ValueError("Computed output is not stored")
        formed = re.search(r"(\w+) = lean_alloc_ctor\(1, 4, 0\)", body)
        old = re.search(r"(\w+) = lean_ctor_get\(v_resources_\d+_, 1\)", body)
        if formed is None or old is None:
            raise ValueError("Positive formation or retained formation missing")
        for slot, variable in ((2, old[1]), (3, operation[2])):
            if not re.search(r"lean_ctor_set\(" + re.escape(formed[1]) + ", " + str(slot) + ", " +
                             re.escape(variable) + r"\)", body):
                raise ValueError("Positive formation substitutes its prior or existing producer")
        call(current[position], "ControlReference_positionCode___redArg")
        if not re.search(r"lean_closure_set\([^,]+, 0, v_actual_\d+_\)", current[return_step]):
            raise ValueError("Position return drops the actual recursive value")
        call(current[cell], "ControlPermission_equalCode")
        call(current[descend], "ControlPermission_lookupCode")
        call(current[compare], "ControlPermission_equalCode")
        if current[compare].count("lean_nat_sub(") != 2:
            raise ValueError("Comparison must descend both received naturals")
        if not re.search(r"v_actual_\d+_\s*\);", call(current[prior], "ControlPermission_previous___redArg")[0]):
            raise ValueError("Permission return substitutes its actual recursive result")

        producers = ("Control_execute___redArg", "Dossier_step", "Deduction_execute___redArg",
                     "Deduction_form___redArg", "Program_step___redArg", "ControlStep_code___redArg",
                     "ControlDeduction_code___redArg", "ControlPermission_lookupCode",
                     "Deduction_formFromProducerReads___redArg", "ControlResources_readCode___redArg",
                     "ControlProducer_code___redArg", "ControlPermission_locatedLookup___redArg",
                     "ControlArithmetic_code", "ControlFormation_code___redArg",
                     "ControlAssembly_code___redArg",
                     "ControlPermission_referencedLookup___redArg", "ControlReference_positionCode___redArg")
        for certificate in ("Control_Result_sound___redArg", "ControlStep_complete___redArg"):
            if any(sites(current[names[certificate]], target) for target in producers):
                raise ValueError("Certificate replays a producer")
        sound = current[names["Control_Result_sound___redArg"]]
        if "lean_apply" in sound or re.search(r"lean_ctor_get\([^,]+, 2\)", sound) is None:
            raise ValueError("Sound certificate must project the stored trace")

    check(functions)
    mutations = []

    def append(name, extra):
        mutations.append((name, functions[name] + extra))

    for name, target in ((quote, "Dossier_step"), (form, "ControlFormation_code___redArg"),
                         (assembly, "ControlAssembly_code___redArg"),
                         (cell, "ControlPermission_equalCode"), (descend, "ControlPermission_lookupCode"),
                         (position, "ControlReference_positionCode___redArg")):
        append(name, names[target] + "();")
    for certificate in ("Control_Result_sound___redArg", "ControlStep_complete___redArg"):
        append(names[certificate], names["Control_execute___redArg"] + "();")
        append(names[certificate], names["ControlArithmetic_code"] + "();")
        append(names[certificate], names["ControlFormation_code___redArg"] + "();")
    for factory, target in (("ControlStep_code___redArg", "Dossier_step"),
                            ("ControlDeduction_code___redArg", "ControlFormation_code___redArg"),
                            ("ControlPermission_equalCode", "ControlPermission_equalCode"),
                            ("ControlPermission_lookupCode", "ControlPermission_lookupCode"),
                            ("ControlReference_positionCode___redArg", "ControlReference_positionCode___redArg")):
        append(names[factory], names[target] + "();")
    for target in ("Program_step___redArg", "Deduction_execute___redArg", "resolvePermission",
                   "ControlPermission_equalDecision", "Ref_position"):
        append(quote, names[target] + "();")
    name = names["Control_execute___redArg"]
    body = functions[name]
    mutations.extend(((name, body + "lean_apply_1(x, y);"),
                      (name, body + names["Control_execute___redArg"] + "();"),
                      (name, body.replace("lean_nat_sub", "lean_nat_add")),
                      (name, "lean_apply_1(x, y);" + re.sub(r"lean_apply_1\([^;]+;", "", body, count=1))))
    body = functions[quote]
    produced = assigned(body, "Dossier_step")
    invoked = call(body, "Program_quotationStep___redArg")
    mutations.append((quote, body[:invoked.start()] + invoked[0].replace(produced, "v_other_packet") + body[invoked.end():]))
    for name, pattern in ((assembly, r"v_actualDecision_\d+_"), (choose, r"(?<=0, )v_val_\d+_"),
                          (prior, r"v_actual_\d+_"), (lookup_at, r"v_actual_\d+_"),
                          (return_step, r"v_actual_\d+_")):
        mutations.append((name, re.sub(pattern, "v_other_packet", functions[name])))
    mutations.append((compare, functions[compare].replace("lean_nat_sub", "lean_nat_add")))
    mutations.append((names["ControlPermission_lookupCode"],
                      functions[names["ControlPermission_lookupCode"]].replace("= 6;", "= 5;")))
    for target in ("read", "Ports_read", "Support_read", "Producer_arguments", "Support_extend", "Deduction_form___redArg"):
        append(names["Deduction_formFromProducerReads___redArg"], names[target] + "();")
    for name, target in ((resource_cell, "ControlResources_readCode___redArg"),
                         (right_read, "ControlResources_readCode___redArg"),
                         (names["Deduction_formFromProducerReads___redArg"], "Deduction_evaluate"),
                         (names["Deduction_formFromProducerReads___redArg"], "Deduction_producer___redArg")):
        append(name, names[target] + "();")
    for name, pattern in ((form_step, r"v_leftRead_\d+_"), (form_step, r"v_rightRead_\d+_"),
                          (right_read, r"(?<=3, )v_leftRead_\d+_"),
                          (resource_cell, r"(?<=0, )v_fst_\d+_"),
                          (names["Deduction_formFromProducerReads___redArg"], r"v_leftValue_\d+_"),
                          (names["Deduction_formFromProducerReads___redArg"], r"(?<=2, )v_formation_\d+_"),
                          (names["Deduction_formFromProducerReads___redArg"], r"(?<=3, )v_formed_\d+_"),
                          (form, r"v_producer_\d+_"), (producer_entry, r"v_fst_\d+_"),
                          (located_return, r"(?<=0, )v_actual_\d+_")):
        mutations.append((name, re.sub(pattern, "v_other_packet", functions[name])))
    mutations.append((names["ControlResources_readCode___redArg"],
                      functions[names["ControlResources_readCode___redArg"]].replace("= 12;", "= 11;")))
    append(names["Deduction_formFromProducerReads___redArg"], "lean_apply_1(x, y);")
    for name, changed in mutations:
        mutated = dict(functions)
        mutated[name] = changed
        try:
            check(mutated)
        except ValueError:
            pass
        else:
            raise ValueError("Bad control/producer mutation accepted: " + name)
    runpy.run_path(str(ROOT / "scripts/check-documentary-producer-codegen.py"))["verify"](
        functions, select, agent["parameters"](texts))
    runpy.run_path(str(ROOT / "scripts/check-documentary-arithmetic-codegen.py"))["verify"](
        functions, select, agent["parameters"](texts))
    runpy.run_path(str(ROOT / "scripts/check-documentary-assembly-codegen.py"))["verify"](
        functions, select, agent["parameters"](texts))
    print("DOCUMENTARY_INTERPRETER_CODEGEN_OK: paid lazy evaluator, reference position and permission lookup, "
          "actual paid resource arguments and retained producer/position, retained legacy formation helper and instrumented arithmetic/formation/assembly path, shared decision, two consuming certificates; " +
          str(len(mutations)) + " mutations rejected; named direct-body/closure scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print("DOCUMENTARY_INTERPRETER_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
