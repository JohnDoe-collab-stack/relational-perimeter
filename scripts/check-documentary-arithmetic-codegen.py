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


def make_stack_check(functions, select, parameters):
    """The nine received C bodies, with separate call and closure edges.

    This checks the compiled positive stack producer. Expected-value and Eval
    witness producers remain separate; they must not be reached from this scope.
    Native successor/predecessor and fixed constructors keep the declared host
    boundary. This is neither a C verifier nor a physical-cost measurement.
    """
    suffixes = {
        "wrapper": "ControlArithmetic_addCode",
        "cell_factory": "ControlArithmetic_descendAdd",
        "cell_box": "ControlArithmetic_descendAdd___lam__1___boxed",
        "cell": "ControlArithmetic_descendAdd___lam__1",
        "push": "ControlArithmetic_descendAdd___lam__0",
        "frame_factory": "ControlArithmetic_returns",
        "frame": "ControlArithmetic_returns___lam__1",
        "return_box": "ControlArithmetic_returns___lam__0___boxed",
        "successor": "ControlArithmetic_returns___lam__0",
    }
    names = {key: select(functions, BASE + suffix) for key, suffix in suffixes.items()}
    arities = {"wrapper": 2, "cell_factory": 3, "cell_box": 4, "cell": 4,
               "push": 4, "frame_factory": 2, "frame": 3, "return_box": 3,
               "successor": 3}
    for key, arity in arities.items():
        if len(parameters[names[key]]) != arity:
            raise ValueError("Changed stack producer arity: " + key)

    references = {
        "wrapper": {"cell_factory"}, "cell_factory": {"cell_box"},
        "cell_box": {"cell"}, "cell": {"frame_factory", "push"},
        "push": {"cell_factory"}, "frame_factory": {"frame"},
        "frame": {"return_box"}, "return_box": {"successor"},
        "successor": {"frame_factory"},
    }
    calls = {
        "wrapper": {"cell_factory"}, "cell_factory": set(),
        "cell_box": {"cell"}, "cell": {"frame_factory"},
        "push": {"cell_factory"}, "frame_factory": set(), "frame": set(),
        "return_box": {"successor"}, "successor": {"frame_factory"},
    }
    fixed = {"lean_alloc_ctor", "lean_ctor_set", "lean_alloc_closure", "lean_closure_set",
             "lean_box", "lean_unsigned_to_nat", "lean_ctor_set_uint8", "sizeof",
             "lean_inc", "lean_inc_ref", "lean_dec", "lean_dec_ref"}
    native = {key: set(fixed) for key in names}
    native["cell"].update({"lean_nat_dec_eq", "lean_nat_sub"})
    native["frame"].update({"lean_obj_tag", "lean_ctor_get", "lean_is_exclusive"})
    native["successor"].add("lean_nat_add")
    primitive_counts = {
        "wrapper": {"lean_box": 1},
        "cell_factory": {"lean_alloc_closure": 1, "lean_closure_set": 3, "lean_box": 1,
                         "lean_alloc_ctor": 1, "lean_ctor_set": 2},
        "cell_box": {"lean_dec": 1},
        "cell": {"lean_unsigned_to_nat": 2, "lean_nat_dec_eq": 1, "lean_nat_sub": 1,
                 "lean_alloc_closure": 1, "lean_closure_set": 3, "lean_alloc_ctor": 1,
                 "lean_ctor_set": 2, "lean_ctor_set_uint8": 1, "sizeof": 1},
        "push": {"lean_box": 1, "lean_alloc_ctor": 1, "lean_ctor_set": 2},
        "frame_factory": {"lean_alloc_closure": 1, "lean_closure_set": 2, "lean_unsigned_to_nat": 1,
                          "lean_alloc_ctor": 1, "lean_ctor_set": 2, "lean_ctor_set_uint8": 1, "sizeof": 1},
        "frame": {"lean_obj_tag": 1, "lean_alloc_ctor": 2, "lean_ctor_set": 5, "lean_ctor_get": 2,
                  "lean_is_exclusive": 1, "lean_dec": 2, "lean_inc": 1, "lean_box": 2,
                  "lean_alloc_closure": 1, "lean_closure_set": 2},
        "return_box": {"lean_dec": 1},
        "successor": {"lean_unsigned_to_nat": 1, "lean_nat_add": 1},
    }
    assignment_counts = {"wrapper": 2, "cell_factory": 4, "cell_box": 1, "cell": 8,
                         "push": 3, "frame_factory": 4, "frame": 14, "return_box": 1,
                         "successor": 3}
    multiple_assignments = {key: {} for key in names}
    sensitive = re.compile(r'\b(?:lean_apply\w*|\w*Control_Code_bind\w*|'
                           r'\w*ControlNaturalStackAgreement\w*|\w*historical\w*|'
                           r'\w*ControlArithmetic_\w*__trace\w*|'
                           r'\w*ControlArithmetic_businessLabels\w*|'
                           r'\w*(?:List_length|Nat_max|Nat_min)\w*)\b')
    rules, ordered, ownership, closure_last_capture = [], [], [], {}

    def rule(key, pattern, count=1):
        rules.append((names[key], pattern, count))

    def owned(key, pattern):
        rule(key, pattern)
        ownership.append((names[key], pattern))

    def closure(key, child, arity, fixed_count, captures):
        body = functions[names[key]]
        match = re.search(r'(\w+) = lean_alloc_closure\(\(void\*\)\(' +
                          re.escape(names[child]) + r'\), ' + str(arity) + ', ' +
                          str(fixed_count) + r'\);', body)
        if match is None:
            raise ValueError("Received stack closure missing: " + key)
        pointer = re.escape(match[1])
        rule(key, re.escape(match[0]))
        for slot, value in enumerate(captures):
            rule(key, r'lean_closure_set\(' + pointer + ', ' + str(slot) + ', ' + re.escape(value) + r'\);')
        ordered.append((names[key], re.escape(match[0]),
                        *(r'lean_closure_set\(' + pointer + ', ' + str(slot) + ', ' + re.escape(value) + r'\);'
                          for slot, value in enumerate(captures))))
        closure_last_capture[match[1]] = (r'lean_closure_set\(' + pointer + ', ' +
                                         str(len(captures) - 1) + ', ' + re.escape(captures[-1]) + r'\);')
        return match[1]

    def assigned(key, callee, arguments):
        body = functions[names[key]]
        match = re.search(r'(\w+) = ' + re.escape(names[callee]) + r'\(' +
                          ', '.join(re.escape(value) for value in arguments) + r'\);', body)
        if match is None:
            raise ValueError("Received stack call/arguments missing: " + key)
        rule(key, re.escape(match[0]))
        rule(key, r'\breturn ' + re.escape(match[1]) + r';')
        return match[1]

    def constant(key, function, number):
        suffix = '' if function == 'lean_box' else 'u'
        match = re.search(r'(\w+) = ' + function + r'\(' + str(number) + suffix + r'\);', functions[names[key]])
        if match is None:
            raise ValueError("Received stack constant missing: " + key)
        rule(key, re.escape(match[0]))
        return match[1]

    def code_node(key, callback, constructor, event, forwards=None):
        body = functions[names[key]]
        tag = re.search(r'(\w+) = ' + str(event) + r';', body)
        if tag is None:
            raise ValueError("Received stack paid tag missing: " + key)
        rule(key, re.escape(tag[0]))
        allocated = re.search(r'(\w+) = lean_alloc_ctor\(' + constructor + r'\);', body)
        if allocated is None:
            raise ValueError("Received stack paid node missing: " + key)
        node = re.escape(allocated[1])
        rule(key, re.escape(allocated[0]))
        if forwards is None:
            boxed = re.search(r'(\w+) = lean_box\(' + re.escape(tag[1]) + r'\);', body)
            if boxed is None:
                raise ValueError("Received stack label box missing: " + key)
            rule(key, re.escape(boxed[0]))
            rule(key, r'lean_ctor_set\(' + node + ', 0, ' + re.escape(boxed[1]) + r'\);')
            rule(key, r'lean_ctor_set\(' + node + ', 1, ' + re.escape(callback) + r'\);')
        else:
            rule(key, r'lean_ctor_set\(' + node + ', 0, ' + re.escape(callback) + r'\);')
            rule(key, r'lean_ctor_set\(' + node + ', 1, ' + re.escape(forwards) + r'\);')
            rule(key, r'lean_ctor_set_uint8\(' + node + r', sizeof\(void\*\)\*2, ' + re.escape(tag[1]) + r'\);')
        rule(key, r'\breturn ' + node + r';')
        final_fields = ((r'lean_ctor_set\(' + node + ', 0, ' + re.escape(boxed[1]) + r'\);',
                         r'lean_ctor_set\(' + node + ', 1, ' + re.escape(callback) + r'\);')
                        if forwards is None else
                        (r'lean_ctor_set\(' + node + ', 0, ' + re.escape(callback) + r'\);',
                         r'lean_ctor_set\(' + node + ', 1, ' + re.escape(forwards) + r'\);',
                         r'lean_ctor_set_uint8\(' + node + r', sizeof\(void\*\)\*2, ' + re.escape(tag[1]) + r'\);'))
        ordered.append((names[key], re.escape(tag[0]), re.escape(allocated[0]), *final_fields,
                        r'\breturn ' + node + r';'))
        if forwards is None:
            ordered.append((names[key], re.escape(tag[0]), re.escape(boxed[0]),
                            final_fields[0]))
        ordered.append((names[key], closure_last_capture[callback],
                        re.escape(allocated[0])))

    p = {key: parameters[name] for key, name in names.items()}
    nil = constant("wrapper", "lean_box", 0)
    assigned("wrapper", "cell_factory", [p["wrapper"][0], p["wrapper"][1], nil])
    ordered.append((names["wrapper"], re.escape(nil) + r' = lean_box\(0\);',
                    re.escape(names["cell_factory"]) + r'\('))
    cell_closure = closure("cell_factory", "cell_box", 4, 3,
                           [p["cell_factory"][1], p["cell_factory"][0], p["cell_factory"][2]])
    code_node("cell_factory", cell_closure, "1, 2, 0", 17)
    cell_result = assigned("cell_box", "cell", p["cell_box"])
    cell_release = r'lean_dec\(' + re.escape(p["cell_box"][0]) + r'\);'
    owned("cell_box", cell_release)
    ordered.append((names["cell_box"], re.escape(cell_result) + ' = ' + re.escape(names["cell"]) + r'\(',
                    cell_release, r'\breturn ' + re.escape(cell_result) + r';'))
    frame_closure = closure("frame_factory", "frame", 3, 2,
                            [p["frame_factory"][1], p["frame_factory"][0]])
    forward_zero = constant("frame_factory", "lean_unsigned_to_nat", 0)
    code_node("frame_factory", frame_closure, "2, 2, 1", 3, forward_zero)
    return_result = assigned("return_box", "successor", p["return_box"])
    return_release = r'lean_dec\(' + re.escape(p["return_box"][0]) + r'\);'
    owned("return_box", return_release)
    ordered.append((names["return_box"], re.escape(return_result) + ' = ' + re.escape(names["successor"]) + r'\(',
                    return_release, r'\breturn ' + re.escape(return_result) + r';'))

    zero = constant("cell", "lean_unsigned_to_nat", 0)
    one = constant("cell", "lean_unsigned_to_nat", 1)
    body = functions[names["cell"]]
    comparison = re.search(r'(\w+) = lean_nat_dec_eq\(' + re.escape(p["cell"][0]) + ', ' + re.escape(zero) + r'\);', body)
    predecessor = re.search(r'(\w+) = lean_nat_sub\(' + re.escape(p["cell"][0]) + ', ' + re.escape(one) + r'\);', body)
    if comparison is None or predecessor is None:
        raise ValueError("Addition does not inspect/descend actual received right")
    rule("cell", re.escape(comparison[0]))
    rule("cell", r'if \(' + re.escape(comparison[1]) + r' == 1\)')
    rule("cell", re.escape(predecessor[0]))
    ordered.append((names["cell"], re.escape(zero) + r' = lean_unsigned_to_nat\(0u\);',
                    re.escape(comparison[0]), r'if \(' + re.escape(comparison[1]) + r' == 1\)'))
    base = assigned("cell", "frame_factory", [p["cell"][1], p["cell"][2]])
    rule("cell", r'if \(' + re.escape(comparison[1]) + r' == 1\)\s*\{\s*lean_object\* ' +
         re.escape(base) + r';\s*' + re.escape(base) + ' = ' + re.escape(names["frame_factory"]) +
         r'\(' + re.escape(p["cell"][1]) + ', ' + re.escape(p["cell"][2]) + r'\);\s*return ' +
         re.escape(base) + r';\s*\}\s*else\s*\{[^{}]*' + re.escape(one) +
         r' = lean_unsigned_to_nat\(1u\);\s*' + re.escape(predecessor[0]))
    allocation_closure = closure("cell", "push", 4, 3,
                                 [p["cell"][2], p["cell"][1], predecessor[1]])
    code_node("cell", allocation_closure, "2, 2, 1", 6, zero)
    unit = constant("push", "lean_box", 0)
    cons = re.search(r'(\w+) = lean_alloc_ctor\(1, 2, 0\);', functions[names["push"]])
    if cons is None:
        raise ValueError("Paid natural descent lost its positive Unit cons")
    rule("push", re.escape(cons[0]))
    rule("push", r'lean_ctor_set\(' + re.escape(cons[1]) + ', 0, ' + re.escape(unit) + r'\);')
    rule("push", r'lean_ctor_set\(' + re.escape(cons[1]) + ', 1, ' + re.escape(p["push"][0]) + r'\);')
    child = assigned("push", "cell_factory", [p["push"][1], p["push"][2], cons[1]])
    ordered.append((names["push"], re.escape(unit) + r' = lean_box\(0\);', re.escape(cons[0]),
                    r'lean_ctor_set\(' + re.escape(cons[1]) + ', 0, ' + re.escape(unit) + r'\);',
                    r'lean_ctor_set\(' + re.escape(cons[1]) + ', 1, ' + re.escape(p["push"][0]) + r'\);',
                    re.escape(child) + ' = ' + re.escape(names["cell_factory"]) + r'\('))

    body = functions[names["frame"]]
    rule("frame", r'if \(lean_obj_tag\(' + re.escape(p["frame"][0]) + r'\) == 0\)')
    tail = re.search(r'(\w+) = lean_ctor_get\(' + re.escape(p["frame"][0]) + r', 1\);', body)
    done = re.search(r'(\w+) = lean_alloc_ctor\(0, 1, 0\);', body)
    reused = re.search(r'(\w+) = ' + re.escape(p["frame"][0]) + r';', body)
    allocated = re.search(r'(\w+) = lean_alloc_ctor\(1, 2, 0\);', body)
    tag = re.search(r'(\w+) = 18;', body)
    if any(item is None for item in (tail, done, reused, allocated, tag)):
        raise ValueError("Paid frame inspection/consumption/return changed")
    exclusive = re.search(r'(\w+) = !lean_is_exclusive\(' + re.escape(p["frame"][0]) + r'\);', body)
    head = re.search(r'(\w+) = lean_ctor_get\(' + re.escape(p["frame"][0]) + r', 0\);', body)
    if exclusive is None or head is None:
        raise ValueError("Frame exclusivity/head must come from the actual received frame")
    owned("frame", re.escape(exclusive[0]))
    owned("frame", re.escape(head[0]))
    head_release = r'lean_dec\(' + re.escape(head[1]) + r'\);'
    tail_retain = r'lean_inc\(' + re.escape(tail[1]) + r'\);'
    frame_release = r'lean_dec\(' + re.escape(p["frame"][0]) + r'\);'
    owned("frame", head_release)
    owned("frame", tail_retain)
    owned("frame", frame_release)
    rule("frame", r'if \(' + re.escape(exclusive[1]) + r' == 0\)\s*\{[^{}]*' +
         re.escape(head[0]) + r'\s*' + head_release + r'\s*' + re.escape(reused[0]) +
         r'[^{}]*\}\s*else\s*\{\s*' + tail_retain + r'\s*' + frame_release + r'\s*' +
         re.escape(reused[1]) + r' = lean_box\(0\);')
    ordered.append((names["frame"], re.escape(tail[0]), re.escape(exclusive[0]), re.escape(head[0]),
                    head_release, re.escape(reused[0])))
    ordered.append((names["frame"], tail_retain, frame_release,
                    re.escape(reused[1]) + r' = lean_box\(0\);'))
    for match in (tail, done, reused, allocated, tag):
        rule("frame", re.escape(match[0]))
    rule("frame", r'lean_ctor_set\(' + re.escape(done[1]) + ', 0, ' + re.escape(p["frame"][1]) + r'\);')
    rule("frame", r'\breturn ' + re.escape(done[1]) + r';')
    rule("frame", r'if \(lean_obj_tag\(' + re.escape(p["frame"][0]) + r'\) == 0\)\s*\{\s*lean_object\* ' +
         re.escape(done[1]) + r';\s*' + re.escape(done[0]) + r'\s*lean_ctor_set\(' + re.escape(done[1]) +
         ', 0, ' + re.escape(p["frame"][1]) + r'\);\s*return ' + re.escape(done[1]) +
         r';\s*\}\s*else\s*\{[^{}]*' + re.escape(tail[0]))
    returned_closure = closure("frame", "return_box", 3, 2, [p["frame"][1], tail[1]])
    boxed = re.search(r'(\w+) = lean_box\(' + re.escape(tag[1]) + r'\);', body)
    if boxed is None:
        raise ValueError("Paid natural Return label box missing")
    rule("frame", re.escape(boxed[0]))
    for pointer in (reused[1], allocated[1]):
        rule("frame", r'lean_ctor_set\(' + re.escape(pointer) + ', 0, ' + re.escape(boxed[1]) + r'\);')
        rule("frame", r'lean_ctor_set\(' + re.escape(pointer) + ', 1, ' + re.escape(returned_closure) + r'\);')
    merged = re.search(r'(\w+) = ' + re.escape(reused[1]) + r';', body)
    if merged is None:
        raise ValueError("Consumed frame does not feed actual Return")
    rule("frame", re.escape(merged[0]))
    rule("frame", re.escape(merged[1]) + ' = ' + re.escape(allocated[1]) + r';')
    rule("frame", r'\breturn ' + re.escape(merged[1]) + r';')
    shared = re.search(r'(\w+) = ' + re.escape(exclusive[1]) + r';', body)
    if shared is None:
        raise ValueError("Frame sharing branch does not transfer actual exclusivity")
    rule("frame", re.escape(shared[0]), 2)
    rule("frame", r'if \(' + re.escape(shared[1]) + r' == 0\)\s*\{\s*lean_ctor_set\(' +
         re.escape(reused[1]) + ', 1, ' + re.escape(returned_closure) + r'\);\s*lean_ctor_set\(' +
         re.escape(reused[1]) + ', 0, ' + re.escape(boxed[1]) + r'\);\s*' + re.escape(merged[0]) +
         r'[^{}]*\}\s*else\s*\{[^{}]*' + re.escape(allocated[0]) + r'\s*lean_ctor_set\(' +
         re.escape(allocated[1]) + ', 0, ' + re.escape(boxed[1]) + r'\);\s*lean_ctor_set\(' +
         re.escape(allocated[1]) + ', 1, ' + re.escape(returned_closure) + r'\);\s*' +
         re.escape(merged[1]) + ' = ' + re.escape(allocated[1]) + r';')
    multiple_assignments["frame"] = {reused[1]: 2, shared[1]: 2, merged[1]: 2}
    ordered.append((names["frame"], re.escape(tail[0]), re.escape(exclusive[0]),
                    re.escape(returned_closure) + r' = lean_alloc_closure\(',
                    r'lean_closure_set\(' + re.escape(returned_closure) + ', 1, ' + re.escape(tail[1]) + r'\);',
                    re.escape(tag[0]), re.escape(boxed[0]),
                    r'\breturn ' + re.escape(merged[1]) + r';'))
    one = constant("successor", "lean_unsigned_to_nat", 1)
    successor = re.search(r'(\w+) = lean_nat_add\(' + re.escape(p["successor"][0]) + ', ' + re.escape(one) + r'\);', functions[names["successor"]])
    if successor is None:
        raise ValueError("Return does not perform successor of actual received value")
    rule("successor", re.escape(successor[0]))
    after = assigned("successor", "frame_factory", [successor[1], p["successor"][1]])
    ordered.append((names["successor"], re.escape(one) + r' = lean_unsigned_to_nat\(1u\);', re.escape(successor[0]),
                    re.escape(after) + ' = ' + re.escape(names["frame_factory"]) + r'\('))

    def check(current):
        for key, name in names.items():
            body = current[name]
            assignments = re.findall(r'\b(v_\w+)\s*=(?!=)', body)
            if any(parameter in assignments for parameter in p[key]):
                raise ValueError("Stack rebinds a received parameter: " + key)
            if len(assignments) != assignment_counts[key]:
                raise ValueError("Stack adds/drops a received local assignment: " + key)
            repeated = {variable: assignments.count(variable) for variable in set(assignments)
                        if assignments.count(variable) != 1}
            if repeated != multiple_assignments[key]:
                raise ValueError("Stack rebinds a local outside its explicit reuse/phi branches: " + key)
            if sensitive.search(body):
                raise ValueError("Unpaid composition/expected-index/witness/historical dependency: " + key)
            found_references = set(re.findall(r'\b(?:l|lp)_\w+\b', body))
            if found_references != {names[child] for child in references[key]}:
                raise ValueError("Changed stack call/closure graph: " + key)
            all_calls = re.findall(r'\b([A-Za-z_]\w*)\s*\(', body)
            project_calls = [callee for callee in all_calls if callee.startswith(("l_", "lp_"))]
            if sorted(project_calls) != sorted(names[child] for child in calls[key]):
                raise ValueError("Callback invoked outside its paid closure: " + key)
            if any(callee not in native[key] and callee not in project_calls and callee != "if" for callee in all_calls):
                raise ValueError("Undeclared stack primitive/inspection: " + key)
            actual_counts = {callee: all_calls.count(callee) for callee in set(all_calls)
                             if callee not in project_calls and callee != "if"}
            if actual_counts != primitive_counts[key]:
                raise ValueError("Stack adds/drops a received fixed construction or primitive: " + key)
            for primitive, expected in (("lean_nat_add", int(key == "successor")),
                                        ("lean_nat_sub", int(key == "cell")),
                                        ("lean_nat_dec_eq", int(key == "cell")),
                                        ("lean_obj_tag", int(key == "frame"))):
                if all_calls.count(primitive) != expected:
                    raise ValueError("Changed natural stack operation count: " + key + "/" + primitive)
        for name, pattern, count in rules:
            if len(re.findall(pattern, current[name])) != count:
                raise ValueError("Stack substitutes received data/paid constructor: " + name + "/" + pattern)
        for name, *patterns in ordered:
            positions = [re.search(pattern, current[name]).start() for pattern in patterns]
            if positions != sorted(positions) or len(set(positions)) != len(positions):
                raise ValueError("Stack action moved ahead of its paid construction: " + name)

    def mutations():
        result = []
        # Every actual-data/label/constructor requirement has an omission mutant.
        for name, pattern, _ in rules:
            changed = re.sub(pattern, "substituted_natural_stack_777;", functions[name], count=1)
            if changed == functions[name]:
                raise ValueError("Empty natural-stack requirement mutation")
            result.append((name, changed))
        for name, pattern in ownership:
            statement = re.search(pattern, functions[name])[0]
            changed_statement = re.sub(r'\([^)]*\)', '(v_substituted_refcount_777)', statement, count=1)
            changed = functions[name].replace(statement, changed_statement, 1)
            if changed == functions[name]:
                raise ValueError("Empty natural-stack ownership argument mutation")
            result.append((name, changed))
        for key, name in names.items():
            for parameter in p[key]:
                result.append((name, parameter + ' = v_substituted_received_777;\n' + functions[name]))
            variables = set(re.findall(r'\b(v_\w+)\s*=(?!=)', functions[name]))
            for variable in sorted(variables):
                result.append((name, functions[name] + '\n' + variable + ' = v_substituted_local_777;'))
            result.append((name, functions[name] + '\nv_new_alias_777 = v_substituted_local_777;'))
        comparison_site = re.search(re.escape(comparison[0]), functions[names["cell"]])
        result.append((names["cell"], functions[names["cell"]][:comparison_site.start()] +
                       p["cell"][0] + ' = ' + p["cell"][1] + ';\n' +
                       functions[names["cell"]][comparison_site.start():]))
        capture_site = re.search(r'lean_closure_set\(' + re.escape(returned_closure) + ', 1, ' +
                                 re.escape(tail[1]) + r'\);', functions[names["frame"]])
        result.append((names["frame"], functions[names["frame"]][:capture_site.start()] +
                       tail[1] + ' = ' + p["frame"][1] + ';\n' +
                       functions[names["frame"]][capture_site.start():]))
        for key in ("wrapper", "cell_factory", "frame_factory"):
            for early in ("lean_nat_dec_eq(x, y);", "lean_obj_tag(x);", "lean_ctor_get(x, 1);"):
                result.append((names[key], functions[names[key]] + early))
        for key, child in (("cell_factory", "cell_box"), ("cell", "push"),
                           ("frame_factory", "frame"), ("frame", "return_box")):
            result.append((names[key], functions[names[key]] + names[child] + "(x, y, z);"))
        for key, early in (("cell", "lean_alloc_ctor(1, 2, 0);"),
                           ("frame", "lean_nat_add(x, y);"),
                           ("frame_factory", "lean_nat_add(x, y);")):
            result.append((names[key], functions[names[key]] + early))
        for key in names:
            for forbidden in (BASE + "Control_Code_bind___redArg(x, y);",
                              BASE + "Control_Code_bindForward___redArg(x, y);",
                              "l_List_lengthTR___redArg(x);", "lean_nat_max(x, y);",
                              "lean_nat_min(x, y);", BASE + "ControlArithmetic_add__trace(x, y);",
                              BASE + "ControlNaturalStackAgreement_historicalAddCode(x, y);"):
                result.append((names[key], functions[names[key]] + forbidden))
        for key, pattern in (("successor", r'lean_unsigned_to_nat\(1u\)'),
                             ("cell", r'lean_unsigned_to_nat\(1u\)'),
                             ("frame_factory", r'lean_unsigned_to_nat\(0u\)'),
                             ("wrapper", r'lean_box\(0\)'), ("push", r'lean_box\(0\)')):
            changed = re.sub(pattern, "substituted_natural_constructor_777", functions[names[key]], count=1)
            if changed == functions[names[key]]:
                raise ValueError("Empty natural-stack scalar mutation")
            result.append((names[key], changed))
        for key, before, after in (("cell_factory", " = 17;", " = 18;"),
                                   ("frame", " = 18;", " = 17;"),
                                   ("cell", " = 6;", " = 3;"),
                                   ("frame_factory", " = 3;", " = 6;")):
            changed = functions[names[key]].replace(before, after, 1)
            if changed == functions[names[key]]:
                raise ValueError("Empty natural-stack payment inversion")
            result.append((names[key], changed))
        for key, before, after in (("wrapper", p["wrapper"][0], p["wrapper"][1]),
                                   ("push", p["push"][2], p["push"][1]),
                                   ("successor", p["successor"][1], p["successor"][0]),
                                   ("cell", p["cell"][0], p["cell"][1])):
            result.append((names[key], functions[names[key]].replace(before, after)))
        for key, before, after in (("push", "cell_factory", "frame_factory"),
                                   ("successor", "frame_factory", "cell_factory")):
            result.append((names[key], functions[names[key]].replace(names[before], names[after])))
        for name, *patterns in ordered:
            first = re.search(patterns[0], functions[name])
            last = re.search(patterns[-1], functions[name])
            if last[0].startswith('if '):
                continue
            # Move the last actual action ahead of the first actual action;
            # every original requirement remains for the ordering obligation.
            end = last.end() if last[0].endswith(';') else functions[name].find(';', last.end()) + 1
            statement = functions[name][last.start():end]
            changed = (functions[name][:first.start()] + statement + '\n' +
                       functions[name][first.start():last.start()] + functions[name][end:])
            result.append((name, changed))
        return result

    return check, list(names.values()), mutations


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

    stack_check, stack_scope, stack_mutations = make_stack_check(functions, select, parameters)
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
    for group in (difference, sums, negative, operation, formation, deduction):
        scope += list(group.values())
    scope = list(dict.fromkeys(scope + stack_scope))
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
        stack_check(current)
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
            ("ControlArithmetic_differenceCode", difference[1], 17),
            ("ControlArithmetic_sumCode", sums[3], 19),
            ("ControlArithmetic_negateCode", negative[0], 22),
            ("ControlArithmetic_code", operation[0], 21),
            ("ControlFormation_code___redArg", formation[3], 23)):
            body = current[names[key]]
            if re.search(r"\b(?:lean_apply\w*|lean_nat_dec_eq|lean_nat_sub|lean_int_dec_lt|lean_int_to_nat|lean_obj_tag|lean_ctor_get)\(", body):
                raise ValueError("Factory inspects an input before payment")
            step(body, child, label)
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

    return check, scope, names, formation, deduction, stack_mutations, continuation_edges


def verify(functions, select, parameters):
    check, scope, names, formation, deduction, stack_mutations, continuation_edges = make_check(functions, select, parameters)
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
        (formation[1], r"(?<=1, )v_retained_\d+_"), (formation[0], r"(?<=0, )v_resources_\d+_")):
        changed = re.sub(pattern, "v_substituted", functions[name])
        if changed == functions[name]:
            raise ValueError("Empty arithmetic mutation")
        mutations.append((name, changed))
    for key in ("ControlArithmetic_code", "ControlArithmetic_addCode", "ControlFormation_code___redArg"):
        mutations.append((names[key], functions[names[key]] + "lean_nat_dec_eq(x, y);"))
    mutations += stack_mutations()
    for name, changed in mutations:
        current = dict(functions); current[name] = changed
        try:
            check(current)
        except ValueError:
            continue
        raise ValueError("Arithmetic/formation mutation accepted: " + name)
    print("DOCUMENTARY_ARITHMETIC_CODEGEN_OK: paid structural arithmetic, same catalogue/read arguments, "
          "shared computed value/producer/prior formation/support; " + str(len(mutations)) +
          " textual mutations rejected; positive natural stack, paid Cell/allocation/frame/Return, "
          "actual predecessors/values/tails, closed nine-body call/closure graph; direct-body/closure scope")


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
