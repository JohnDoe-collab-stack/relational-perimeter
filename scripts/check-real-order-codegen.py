#!/usr/bin/env python3
"""Bounded pinned-C checks for finite, nonpersistent relational comparison.

Generic Service callbacks and the separately proved finite dyadic classifier
are explicit boundaries. Counts are applications, not physical costs. This
does not restrict arbitrary implementations of the received family.cauchy.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
base = runpy.run_path(str(ROOT / "scripts/check-real-addition-codegen.py"))
Value, Analysis, PREFIX = base["Value"], base["Analysis"], base["PREFIX"]
LEFT, RIGHT, READ = base["LEFT"], base["RIGHT"], base["READ"]
NEXT, CAUCHY, MONOTONE = "l_order_next", "l_order_cauchy", "l_order_monotone"
MIDDLE = "l_order_middle"
PAIR = PREFIX + "RelationalRealOrder_executePair___redArg"
TRIPLE = PREFIX + "RelationalRealOrder_executeTriple___redArg"
ENTRY = PREFIX + "RelationalRealOrder_produceComparison___redArg"
CONTINUE = PREFIX + "RelationalRealOrder_continueComparison___redArg"
CLASSIFY = PREFIX + "RelationalRealOrder_classifyFinite"
LEAF = PREFIX + "RelationalRealAddition_leafCoherent___redArg___lam__0"
PERFORM = PREFIX + "HeterogeneousRealRuntime_perform___redArg"
tagged = base["tagged"]


class OrderAnalysis(Analysis):
    def run(self, name, args):
        if name in (LEFT, MIDDLE, RIGHT):
            expected = {LEFT: "current-left", MIDDLE: "current-middle", RIGHT: "current-right"}[name]
            if args[0].retained() != frozenset({expected}):
                raise ValueError("Order child is not executed at its current archive: " + name)
            return tagged(name), int(name == self.target), int(name == self.target)
        if name == READ:
            return args[-1], 0, 0
        if name == NEXT:
            tags = args[-1].retained()
            if tags == frozenset({"prior-left"}):
                return tagged("current-left"), 0, 0
            if tags == frozenset({"prior-right"}):
                return tagged("current-right"), 0, 0
            raise ValueError("Order continuation does not read its exact owned prior Step")
        if name == CLASSIFY:
            if args[1].retained() != frozenset({LEFT}) or args[2].retained() != frozenset({RIGHT}):
                raise ValueError("Order classifier does not consume its two actual oriented replies")
            return Value(fields={0: args[1], 1: args[2]}), int(name == self.target), int(name == self.target)
        if name == MONOTONE:
            return tagged("index-budget"), 0, 0
        if name == CAUCHY:
            for slot, expected in ((1, "left-journal"), (2, "right-journal"),
                                   (3, "left-request"), (4, "right-request"),
                                   (9, "left-source-execution"), (10, "right-source-execution")):
                if args[slot].retained() != frozenset({expected}):
                    raise ValueError("Leaf coherence does not consume the received current source: " + expected)
            return tagged("received-source-near"), int(name == self.target), int(name == self.target)
        return super().run(name, args)


def service(callback):
    return Value(fields={0: tagged("initial"), 1: Value(function=callback),
                         2: Value(function=NEXT), 4: Value(function=READ)})


def args():
    return [service(LEFT), service(RIGHT), tagged("current-left"), tagged("current-right"),
            tagged("accuracy"), tagged("response"), tagged("budget")]


def run(functions, params, entry, arguments, target="", expected=0):
    result, low, high = OrderAnalysis(functions, params, base["shared"]["reachable"],
                                     target=target, capture=True).run(entry, arguments)
    if (low, high) != (expected, expected):
        raise ValueError(f"Order multiplicity {entry}/{target}: expected {expected}, found [{low},{high}]")
    return result


def check_packet(functions, params):
    packet = run(functions, params, ENTRY, args(), CLASSIFY, 1)
    if packet.fields.get(0, Value()).retained() != frozenset({"budget"}):
        raise ValueError("Order packet lost its response budget")
    for slot, expected in ((0, LEFT), (1, RIGHT)):
        if packet.fields.get(1, Value()).fields.get(slot, Value()).retained() != frozenset({expected}):
            raise ValueError("Order packet lost its owned role")
        if packet.fields.get(2, Value()).fields.get(slot, Value()).retained() != frozenset({expected}):
            raise ValueError("Order packet lost its oriented classification")


def check_budget(functions, params):
    body = functions[CONTINUE]
    accuracy = params[CONTINUE][-1]
    literal = re.findall(r'(\w+)\s*=\s*lean_unsigned_to_nat\(3u\);', body)
    if len(literal) != 1 or not re.search(r'lean_nat_add\(' + re.escape(accuracy) + r',\s*' + literal[0] + r'\)', body):
        raise ValueError("Order continuation lost its exact three-bit response budget")


def leaf_args():
    family = Value(fields={3: Value(function=MONOTONE), 4: Value(function=CAUCHY)})
    def archive(side):
        return Value(fields={0: Value(fields={0: tagged(side + "-journal")})})
    def step(side):
        produced = Value(fields={0: Value(fields={0: tagged(side + "-request")}),
                                 1: tagged(side + "-source-execution")})
        return Value(fields={1: produced})
    return [Value(fields={0: family}), archive("left"), archive("right"), Value(), Value(), Value(),
            step("left"), step("right"), Value(), Value()]


def check_leaf(functions, params):
    graph = base["shared"]["reachable"](functions, LEAF)
    forbidden = ("_readoutsNear", "_stepAt", "_canonicalStep", "_AuthoritativeRuntime_perform")
    if any(any(part in name for part in forbidden) for name in graph):
        raise ValueError("Leaf coherence reconstructs a canonical execution")
    result = run(functions, params, LEAF, leaf_args(), CAUCHY, 1)
    if result.retained() != frozenset({"received-source-near"}):
        raise ValueError("Leaf coherence lost the received cauchy witness")


def reject(check, functions, params, label, expected):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(expected):
            raise ValueError(f"Wrong failure for {label}: {error}") from error
        print("REAL_ORDER_MUTATION_REJECTED " + label)
        return
    raise ValueError("Order mutation accepted: " + label)


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    texts.append("\n".join(f"LEAN_EXPORT lean_object* {name}(lean_object* a, lean_object* p){{ return a; }}"
                            for name in (LEFT, MIDDLE, RIGHT, NEXT, READ, CAUCHY, MONOTONE)))
    functions = {}
    for source in texts:
        functions.update(base["shared"]["bodies"](source))
        base["add_static_objects"](functions, source)
    functions = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                 for name, body in functions.items()}
    params = base["parameters"](texts)
    for name, arity in ((PAIR, 5), (TRIPLE, 7), (ENTRY, 7), (CONTINUE, 7), (CLASSIFY, 3), (LEAF, 10)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact order C definition/arity: " + name)
    check_packet(functions, params)
    for target in (LEFT, RIGHT):
        run(functions, params, ENTRY, args(), target, 1)
    aliased = [service(LEFT), service(LEFT), tagged("current-left"), tagged("current-left"), Value()]
    run(functions, params, PAIR, aliased, LEFT, 2)
    triple = [service(LEFT)] * 3 + [tagged("current-left")] * 3 + [Value()]
    packet = run(functions, params, TRIPLE, triple, LEFT, 3)
    if packet.fields.get(0, Value()).fields.get(1, Value()).retained() != frozenset({LEFT}):
        raise ValueError("Order triple lost its single middle Step")
    distinct = [service(LEFT), service(MIDDLE), service(RIGHT), tagged("current-left"),
                tagged("current-middle"), tagged("current-right"), Value()]
    for target in (LEFT, MIDDLE, RIGHT):
        packet = run(functions, params, TRIPLE, distinct, target, 1)
    if packet.fields.get(0, Value()).fields.get(1, Value()).retained() != frozenset({MIDDLE}):
        raise ValueError("Order triple substituted another role for its middle Step")
    prior = Value(fields={1: Value(fields={0: tagged("prior-left"), 1: tagged("prior-right")})})
    continued = [service(LEFT), service(RIGHT), Value(), Value(), Value(), prior, tagged("accuracy")]
    for target in (LEFT, RIGHT, CLASSIFY):
        run(functions, params, CONTINUE, continued, target, 1)
    check_budget(functions, params)
    check_leaf(functions, params)
    p = params[PAIR]
    for service_slot, archive_slot, label in ((0, 2, "reset-left"), (1, 3, "reset-right")):
        broken = dict(functions)
        pattern = re.escape(PERFORM) + r'\(' + p[service_slot] + r',\s*' + p[archive_slot] + r','
        broken[PAIR], count = re.subn(pattern, PERFORM + '(' + p[service_slot] + ', lean_ctor_get(' + p[service_slot] + ', 0),', broken[PAIR])
        if count != 1:
            raise ValueError("Order archive mutation site changed")
        reject(check_packet, broken, params, label, "Order child is not executed at its current archive")
    broken = dict(functions)
    p = params[CLASSIFY]
    # Mutate the call site, not the classifier boundary.
    match = re.search(re.escape(CLASSIFY) + r'\((\w+),\s*(\w+),\s*(\w+)\)', functions[ENTRY])
    if match is None:
        raise ValueError("Order classifier mutation site changed")
    broken[ENTRY] = functions[ENTRY].replace(match[0], CLASSIFY + '(' + match[1] + ', ' + match[3] + ', ' + match[2] + ')')
    reject(check_packet, broken, params, "reverse-direction", "Order classifier does not consume")
    broken = dict(functions)
    broken[CONTINUE] = functions[CONTINUE].replace("lean_unsigned_to_nat(3u)", "lean_unsigned_to_nat(2u)")
    reject(check_budget, broken, params, "underbudget", "Order continuation lost its exact three-bit")
    broken = dict(functions)
    successor = PREFIX + "HeterogeneousRealRuntime_Step_next___redArg"
    next_call = re.search(r'(\w+)\s*=\s*' + re.escape(successor) + r'\([^;]+\);', broken[CONTINUE])
    if next_call is None:
        raise ValueError("Order continuation successor mutation site changed")
    broken[CONTINUE] = broken[CONTINUE].replace(next_call[0], next_call[1] + ' = lean_ctor_get(' + params[CONTINUE][0] + ', 0);')
    def check_continue(fs, ps):
        run(fs, ps, CONTINUE, continued, LEFT, 1)
    reject(check_continue, broken, params, "reset-continuation", "Order child is not executed at its current archive")
    broken = dict(functions)
    p = params[LEAF]
    broken[LEAF] = functions[LEAF].replace(p[7], p[6])
    reject(check_leaf, broken, params, "reconstruct-second-source", "Leaf coherence does not consume the received current source")
    canonical = PREFIX + "RuntimeCorrespondence_RuntimeReal_readoutsNear"
    if canonical not in functions:
        raise ValueError("Missing canonical coherence mutation target")
    broken = dict(functions)
    broken[LEAF] = functions[LEAF].replace("{", "{ lean_object* rebuilt; rebuilt = " + canonical + "(a,b,c,d,e,f,g,h);", 1)
    reject(check_leaf, broken, params, "canonical-readoutsNear", "Leaf coherence reconstructs a canonical execution")
    duplicate = "l_order_duplicate"
    broken = dict(functions, **{duplicate: "{ lean_object* ignored; ignored = " + PAIR + "(l,r,a,b,p); return " + PAIR + "(l,r,a,b,p); }"})
    duplicate_params = dict(params, **{duplicate: ["l", "r", "a", "b", "p"]})
    run(broken, duplicate_params, duplicate, args()[:4] + [Value()], LEFT, 2)
    print("REAL_ORDER_CODEGEN_OK: current native archives, two aliased roles, one actual-reply classifier, exact successor continuation and three-bit budget, three aliased triple applications with one middle resource, owned-source leaf coherence; reset/direction/budget/source/multiplicity mutations checked; no persistent comparison closure introduced")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"REAL_ORDER_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
