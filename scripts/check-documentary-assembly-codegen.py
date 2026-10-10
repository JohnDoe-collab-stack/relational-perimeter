#!/usr/bin/env python3
"""Pinned C bodies for paid deduction assembly and retained positive parts.

Text mutations exercise this checker; they are not compiled mutant runs.
Deferred binding/justification operations and physical allocation costs remain
outside this direct-body/closure scope.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
BASE = "Agent_Local_Documentary_"


def make_check(functions, select, parameters):
    keys = ("ControlAssembly_code___redArg", "ControlAssembly_finishCode___redArg",
            "ControlAssembly_extensionFromKind___redArg", "Program_deductionStepFromParts___redArg",
            "Program_assemble___redArg", "Program_assemble__complete___redArg",
            "Deduction_incorporateDerived___redArg", "ControlReference_positionCode___redArg")
    names = {key: select(functions, BASE + key) for key in keys}

    def callbacks(key, count):
        found = {int(re.search(r"__(\d+)$", name)[1]): name for name in functions
                 if re.search(re.escape(BASE + key) + r"___(?:lam|elam)__\d+$", name)}
        if len(found) != count:
            raise ValueError("Unexpected assembly callbacks: " + key)
        return found

    code = callbacks("ControlAssembly_code___redArg", 12)
    finish = callbacks("ControlAssembly_finishCode___redArg", 2)
    extension = callbacks("ControlAssembly_extensionFromKind___redArg", 1)
    packet = callbacks("Program_deductionStepFromParts___redArg", 1)
    scope = list(names.values()) + list(code.values()) + list(finish.values()) + list(extension.values()) + list(packet.values())
    # assemble_complete invokes retained binding/transport functions. Its body
    # is checked by its existing guards; this increment covers its caller.
    scope.remove(names["Program_assemble__complete___redArg"])
    forbidden = [select(functions, BASE + key) for key in
                 ("Deduction_producer___redArg", "Deduction_derivedKind___redArg", "Deduction_evaluate",
                  "Deduction_execute___redArg", "Deduction_form___redArg", "Deduction_FormationAction_transport___redArg",
                  "Program_deductionStep___redArg", "Program_step___redArg", "Program_decisionExtension___redArg")]
    forbidden += [select(functions, "Resources_" + key + "___redArg") for key in
                  ("Ref_position", "read", "Support_read", "Producer_arguments", "Support_extend")]
    requirements = []

    def require(name, pattern, message):
        requirements.append((name, pattern, message))

    def field(name, slot, value, object_pattern=r"[^,]+"):
        require(name, r"lean_ctor_set\(" + object_pattern + ", " + str(slot) + ", " + value + r"\)",
                "Assembly substitutes a constructed field")

    def capture(parent, child, slot, value):
        body = functions[parent]
        closure = re.search(r"(\w+) = lean_alloc_closure\(\(void\*\)\(" + re.escape(child) + r"(?:___boxed)?\)", body)
        if closure is None:
            raise ValueError("Assembly child closure missing")
        require(parent, r"lean_closure_set\(" + re.escape(closure[1]) + ", " + str(slot) + ", " + value + r"\)",
                "Assembly drops an actual capture")

    def step(parent, child, label):
        body = functions[parent]
        closure = re.search(r"(\w+) = lean_alloc_closure\(\(void\*\)\(" + re.escape(child) + r"(?:___boxed)?\)", body)
        if closure is None:
            raise ValueError("Paid assembly closure missing")
        field(parent, 1, re.escape(closure[1]))
        require(parent, r"= " + str(label) + r";", "Paid assembly label changed")

    def call(current, name, key):
        found = list(re.finditer(r"\b" + re.escape(names[key]) + r"\(([^;]*)\);", current[name]))
        if len(found) != 1:
            raise ValueError("Expected one assembly call: " + key)
        return found[0]

    step(names["ControlAssembly_code___redArg"], code[11], 9)
    for parent, child, label in ((8, 7, 26), (7, 6, 27), (6, 5, 28), (5, 4, 29), (4, 3, 30), (3, 2, 31), (1, 0, 31)):
        step(code[parent], code[child], label)
    require(code[11], r"= 30;", "Refusal extension is not paid")
    capture(names["ControlAssembly_code___redArg"], code[11], 0, r"v_decision_\d+_")
    step(names["ControlAssembly_finishCode___redArg"], finish[1], 32)
    step(finish[1], finish[0], 33)

    # The actual admitted action and permission cross every construction edge.
    for parent, child, action_slot, permission_slot in ((11, 10, 5, 6), (10, 9, 8, 9), (9, 8, 10, 11),
            (8, 7, 11, 12), (7, 6, 8, 9), (6, 5, 6, 7), (5, 4, 4, 5), (4, 3, 2, 3), (3, 2, 2, 3)):
        capture(code[parent], code[child], action_slot, r"v_action_\d+_")
        capture(code[parent], code[child], permission_slot, r"v_permission_\d+_")
    for slot, variable in ((1, "rulePosition"), (3, "leftPosition"), (5, "rightPosition")):
        field(code[7], slot, r"v_" + variable + r"_\d+_", r"v_kind_\d+_")
    for slot in (0, 2, 4):
        field(code[7], slot, re.escape(parameters[code[7]][slot]), r"v_kind_\d+_")
    capture(code[7], code[6], 0, r"v_kind_\d+_")
    field(code[6], 0, r"v_kind_\d+_")
    field(code[6], 1, re.escape(parameters[code[6]][1]))
    capture(code[6], code[5], 8, r"v___x_\d+_")
    capture(code[6], code[5], 10, r"v_kind_\d+_")
    capture(code[5], code[4], 1, r"v_aligned_\d+_")
    field(code[4], 0, re.escape(parameters[code[4]][0]), r"v_after_\d+_")
    field(code[4], 1, r"v_aligned_\d+_", r"v_after_\d+_")
    capture(code[4], code[3], 1, r"v_kind_\d+_")
    capture(code[4], code[3], 5, r"v_after_\d+_")
    capture(code[3], code[2], 0, r"v_kind_\d+_")
    capture(code[3], code[2], 5, r"v_after_\d+_")
    capture(code[3], code[2], 6, r"v_extension_\d+_")
    field(code[2], 0, r"v_kind_\d+_", r"v_canonical_\d+_")
    field(code[2], 0, r"v_canonical_\d+_", r"v_output_\d+_")
    field(code[2], 0, r"v_action_\d+_")
    field(code[2], 1, r"v_permission_\d+_")
    field(names["Deduction_incorporateDerived___redArg"], 0, r"v_action_\d+_")
    for slot, variable in ((0, "knowledge"), (1, "leftRef"), (2, "rightRef"), (5, "request"), (6, "permission")):
        require(names["Deduction_incorporateDerived___redArg"],
                r"lean_closure_set\([^,]+, " + str(slot) + r", v_" + variable + r"_\d+_\)",
                "Knowledge loses a justification input")
    capture(names["ControlAssembly_extensionFromKind___redArg"], extension[0], 0, r"v_kind_\d+_")
    capture(names["ControlAssembly_extensionFromKind___redArg"], extension[0], 1, r"v_kinds_\d+_")
    for slot, param in enumerate(parameters[extension[0]]):
        # The delayed reference constructor receives old kind, added kind,
        # old context and the actual old occurrence in this order.
        field(extension[0], (1, 2, 0, 3)[slot], re.escape(param))
    require(names["ControlAssembly_extensionFromKind___redArg"], r"lean_unsigned_to_nat\(1u\)", "Extension added count changed")
    for slot, variable in ((0, "output"), (1, "before"), (2, "extension")):
        require(names["Program_assemble___redArg"], r"lean_closure_set\([^,]+, " + str(slot) + r", v_" + variable + r"_\d+_\)",
                "Frame loses an actual binding input")
    for slot, variable in ((0, "dossier"), (1, "after")):
        field(names["Program_assemble___redArg"], slot, r"v_" + variable + r"_\d+_")
    for slot, variable in ((0, "decision"), (1, "extension"), (2, "output"), (3, "next")):
        capture(finish[1], finish[0], slot, r"v_" + variable + r"_\d+_")
    for slot, variable in ((0, "next"), (1, "extension")):
        field(names["Program_deductionStepFromParts___redArg"], slot, r"v_" + variable + r"_\d+_")
    for slot, variable in ((0, "decision"), (1, "output"), (2, "extension")):
        capture(names["Program_deductionStepFromParts___redArg"], packet[0], slot, r"v_" + variable + r"_\d+_")
    require(packet[0], r"(v_val_\d+_) = lean_ctor_get\(v_output_\d+_, 0\)", "Progress does not consume the actual output")

    def check(current):
        for name in scope:
            if any(re.search(r"\b" + re.escape(target) + r"\s*\(", current[name]) for target in forbidden):
                raise ValueError("Assembly or certificate replays a producer, kind or traversal")
        for name, pattern, message in requirements:
            if not re.search(pattern, current[name]):
                raise ValueError(message)
        for factory in ("ControlAssembly_code___redArg", "ControlAssembly_finishCode___redArg"):
            if re.search(r"\b(?:lean_apply\w*|lean_obj_tag|lean_ctor_get|lean_nat_\w+)\(", current[names[factory]]):
                raise ValueError("Assembly factory enters work before payment")
        owners = {"Program_assemble___redArg": finish[1], "Program_deductionStepFromParts___redArg": finish[0],
                  "ControlAssembly_extensionFromKind___redArg": code[3], "Deduction_incorporateDerived___redArg": code[5]}
        for key, owner in owners.items():
            for name in scope:
                if name != owner and re.search(r"\b" + re.escape(names[key]) + r"\s*\(", current[name]):
                    raise ValueError("Assembly operation outside its paid owner")
            call(current, owner, key)
        for name, key, pattern in (
            (code[5], "Deduction_incorporateDerived___redArg", r".*, v_action_\d+_, v_permission_\d+_"),
            (code[3], "ControlAssembly_extensionFromKind___redArg", r"v_fst_\d+_, v_kind_\d+_"),
            (finish[0], "Program_deductionStepFromParts___redArg", r"v_decision_\d+_, v_extension_\d+_, v_output_\d+_, v_next_\d+_"),
            (finish[1], "Program_assemble___redArg", r"v_before_\d+_, v_dossier_\d+_, v_after_\d+_, v_extension_\d+_, v_output_\d+_"),
            (code[2], "ControlAssembly_finishCode___redArg", r"v_before_\d+_, v___x_\d+_, v_after_\d+_, v_extension_\d+_, v_output_\d+_"),
            (packet[0], "Program_assemble__complete___redArg", r"v_extension_\d+_, v_complete_\d+_, v_val_\d+_, v___y_\d+_, v___y_\d+_")):
            if not re.fullmatch(pattern, call(current, name, key)[1]):
                raise ValueError("Assembly substitutes actual operation arguments")
        for name, origin in ((code[11], "request"), (code[10], "leftOccurrence"), (code[9], "rightOccurrence")):
            body = current[name]
            ref = re.search(r"(\w+) = lean_ctor_get\(v_" + origin + r"_\d+_, 1\)", body)
            if ref is None or call(current, name, "ControlReference_positionCode___redArg")[1] != ref[1]:
                raise ValueError("Assembly position substitutes the actual reference")

    return check, scope, requirements, names, code, finish


def verify(functions, select, parameters):
    check, scope, requirements, names, code, finish = make_check(functions, select, parameters)
    check(functions)
    replay = select(functions, BASE + "Deduction_producer___redArg")
    mutations = [(name, functions[name] + replay + "();") for name in scope]
    for name, pattern, _ in requirements:
        changed = re.sub(pattern, "replaced_assembly_edge();", functions[name])
        if changed == functions[name]:
            raise ValueError("Empty assembly mutation")
        mutations.append((name, changed))
    for name, key in ((code[5], "Deduction_incorporateDerived___redArg"), (finish[0], "Program_deductionStepFromParts___redArg")):
        mutations.append((name, functions[name] + names[key] + "();"))
    for name, changed in mutations:
        current = dict(functions); current[name] = changed
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError("Assembly mutation accepted: " + name)
    print("DOCUMENTARY_ASSEMBLY_CODEGEN_OK: paid positions and eight assembly stages, retained support/kind/store/extension/output/frame, "
          "progress consumes the actual output; " + str(len(mutations)) + " textual mutations rejected; direct-body/closure scope")


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
    except (OSError, ValueError, KeyError, IndexError) as error:
        print("DOCUMENTARY_ASSEMBLY_CODEGEN_ERROR: " + str(error), file=sys.stderr)
        sys.exit(1)
