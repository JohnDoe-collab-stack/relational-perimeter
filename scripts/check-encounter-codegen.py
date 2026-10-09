#!/usr/bin/env python3
"""Sharing at named encounter boundaries; not a physical or total-cost proof.

Reuse the repository's symbolic C-IR analysis (helpers and applied closures).
The finite-request tail is an explicit boundary when examining the head;
its per-node sharing is checked separately. Missing definitions fail closed.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
checks = runpy.run_path(str(ROOT / "scripts/check-variable-master-codegen.py"))
agent, shared = checks["agent"], checks["shared"]


def switches_as_branches(body):
    """Exact translation of pinned tag switches WITHOUT fallthrough.

    Accept only the emitted tag selector, braced integer cases and a final
    default. Every case must return on all paths; jumps stay inside that case.
    No branch is removed, no producer is replaced by a summary.
    """
    from unified_codegen_analysis import statements

    def closing(text, start):
        depth = 1
        for index in range(start + 1, len(text)):
            depth += (text[index] == '{') - (text[index] == '}')
            if depth == 0:
                return index
        raise ValueError("ENCOUNTER_SWITCH: unclosed block")

    def check_exits(text):
        nodes = statements(text)
        labels = {}

        def collect(items, after):
            for index, node in enumerate(items):
                remaining = items[index + 1:] + after
                if node[0] == 'label':
                    if node[1] in labels:
                        raise ValueError("ENCOUNTER_SWITCH: duplicate label")
                    labels[node[1]] = remaining
                elif node[0] == 'if':
                    collect(node[2], remaining)
                    collect(node[3], remaining)

        collect(nodes, [])

        def returns(items, visited=frozenset()):
            if not items:
                return False
            node, rest = items[0], items[1:]
            if node[0] == 'statement':
                if node[1].startswith('return '):
                    return True
                jump = re.fullmatch(r'goto\s+(\w+)', node[1])
                if jump:
                    if jump[1] not in labels or jump[1] in visited:
                        raise ValueError("ENCOUNTER_SWITCH: foreign or cyclic jump")
                    return returns(labels[jump[1]], visited | {jump[1]})
            if node[0] == 'if':
                return returns(node[2] + rest, visited) and returns(node[3] + rest, visited)
            return returns(rest, visited)

        if not returns(nodes):
            raise ValueError("ENCOUNTER_SWITCH: fallthrough is unsupported")

    start = re.search(r'\bswitch\s*\(\s*lean_obj_tag\((\w+)\)\s*\)\s*\{', body)
    if not start:
        if re.search(r'\bswitch\b', body):
            raise ValueError("ENCOUNTER_SWITCH: unsupported selector")
        return body
    end = closing(body, start.end() - 1)
    content, cursor, cases = body[start.end():end], 0, []
    while cursor < len(content):
        label = re.match(r'\s*(case\s+(\d+)|default)\s*:\s*\{', content[cursor:])
        if not label:
            if content[cursor:].strip():
                raise ValueError("ENCOUNTER_SWITCH: unsupported case")
            break
        opening = cursor + label.end() - 1
        stop = closing(content, opening)
        case_body = switches_as_branches(content[opening + 1:stop])
        check_exits(case_body)
        cases.append((label[2], case_body))
        cursor = stop + 1
    tags = [tag for tag, _ in cases]
    if not tags or tags[-1] is not None or None in tags[:-1] or len(tags) != len(set(tags)):
        raise ValueError("ENCOUNTER_SWITCH: need unique tags and final default")
    translated = []
    for index, (tag, case_body) in enumerate(cases):
        prefix = '' if index == 0 else 'else '
        condition = '' if tag is None else f'if (lean_obj_tag({start[1]}) == {tag}) '
        translated.append(prefix + condition + '{\n' + case_body + '\n}')
    return switches_as_branches(body[:start.start()] + '\n'.join(translated) + body[end + 1:])


def switch_self_test():
    params = {"l_entry": ["x"], "l_helper": ["x"], "l_produce": ["x"]}
    for body, expected in (
        ('switch(lean_obj_tag(x)){case 0:{return l_produce(x);}default:{return x;}}', 1),
        ('switch(lean_obj_tag(x)){case 0:{l_produce(x);return l_helper(x);}default:{return x;}}', 2),
        ('switch(lean_obj_tag(x)){case 0:{switch(lean_obj_tag(x)){case 1:{return l_helper(x);}default:{return x;}}}default:{return x;}}', 1)):
        functions = {"l_entry": switches_as_branches(body), "l_helper": '{return l_produce(x);}', "l_produce": '{return x;}'}
        analysis = agent["AgentAnalysis"](functions, params, shared["reachable"], target="l_produce")
        _, _, high = analysis.run("l_entry", [agent["Value"]()])
        if high != expected:
            raise ValueError("ENCOUNTER_SWITCH: wrong application count")
    for body in ('switch(lean_obj_tag(x)){case 0:{}default:{return x;}}',
                 'switch(lean_obj_tag(x)){case 0:{if (x){return x;}}default:{return x;}}',
                 'switch(lean_obj_tag(x)){case 0:{goto foreign;}default:{return x;}}',
                 'switch(x){case 0:{return x;}default:{return x;}}'):
        try:
            switches_as_branches(body)
        except ValueError as error:
            if not str(error).startswith("ENCOUNTER_SWITCH:"):
                raise
        else:
            raise ValueError("ENCOUNTER_SWITCH: accepted unsupported fixture")
    print("ENCOUNTER_SWITCH_SELFTEST_OK: all branches, nested helpers, duplicate work, no fallthrough")


def main():
    agent["self_test"]()
    checks["erased_application_self_test"]()
    switch_self_test()
    functions, texts, owners = {}, [], {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        parsed = agent["bodies_with_objects"](text)
        functions.update(parsed)
        for name in parsed:
            owners.setdefault(name, set()).add(path.relative_to(ROOT / ".lake/build/ir").as_posix())
    params = agent["parameters"](texts)
    prefix = "lp_relational_x2dperimeter_"

    def symbol(declaration, module, variant=""):
        return shared["owned_symbol"](functions, params, owners, prefix,
            "RelationalPerimeter.Relativity." + declaration,
            "RelationalPerimeter/Relativity/" + module + ".c", variant)

    primitive = symbol("Production.performRecurring", "Production/RecurringInteractions")
    perform = symbol("Production.Encounter.performEncounter", "Production/ConstitutedEncounters")
    delivery = symbol("Production.Encounter.performDelivery", "Production/ConstitutedEncounters", "___redArg")
    signal = symbol("Production.Encounter.performSignal", "Production/ConstitutedEncounters")
    head = symbol("Continuation.Encounter.encounterThen", "Continuation/EncounterFutures")
    runner = symbol("Continuation.Encounter.run", "Continuation/EncounterFutures")
    responder = symbol("Continuation.Encounter.respond", "Continuation/EncounterFutures")
    normalized = {name: re.sub(r"\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)", r"\1", body)
                  for name, body in functions.items()}
    # Translate only sensitive functions actually reached by this lot. Other
    # generated bodies stay untouched, including their unsupported controls.
    relevant = shared["reachable"](functions, responder) | shared["reachable"](functions, runner)
    for name in relevant:
        if primitive in shared["reachable"](functions, name) or name == responder:
            normalized[name] = switches_as_branches(normalized[name])
    for entry, target, boundaries in ((perform, primitive, ()), (delivery, primitive, ()),
                                      (signal, primitive, ()), (head, perform, (runner,))):
        analysis = agent["AgentAnalysis"](normalized, params, shared["reachable"], target=target,
                                           boundaries=boundaries)
        _, low, high = analysis.run(entry, [agent["Value"]() for _ in params[entry]])
        if (low, high) != (1, 1):
            raise ValueError(f"ENCOUNTER_MULTIPLICITY: {entry} -> {target}=[{low},{high}]")
        print(f"ENCOUNTER_PRODUCTION_OK {entry}: {target}=[1,1]")
    agent["applications"](functions, params, runner, responder, 1, unfolds=(runner,))
    agent["applications"](normalized, params, responder, primitive, 1)
    agent["recursive_tail_applications"](functions, params, runner)
    shared["absent"](functions, runner, ["FutureContract_outcome", "Encounter_contract"])
    reader = symbol("Continuation.Encounter.readerRespond", "Continuation/EncounterFutures")
    agent["applications"](functions, params, reader, responder, 1)
    for declaration, module, variant in (
        ("Reconstruction.LocalizedPresentation.prolong", "Reconstruction/LocalizedPresentations", "___redArg"),
        ("Reconstruction.continuedLocationAgreement", "Reconstruction/LocationAgreement", "___redArg")):
        entry = symbol(declaration, module, variant)
        shared["absent"](functions, entry, ["_perform", "_execute", "FutureContract_outcome"])
    print("ENCOUNTER_CODEGEN_OK: named sharing and description-only transport boundaries")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
