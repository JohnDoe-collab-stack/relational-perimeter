#!/usr/bin/env python3
"""Pinned C routes: probe/refine causality, cross budgets and compact capture.

Callback applications are counted, not physical time, memory or heap cells.
Arithmetic adequacy is proved separately by the individually audited Lean
amplitude and error lemmas. Unsupported sensitive C shapes fail closed.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
base = runpy.run_path(str(ROOT / "scripts/check-real-addition-codegen.py"))
from unified_codegen_analysis import split_arguments
Value, Analysis = base["Value"], base["Analysis"]
PREFIX, LEFT, RIGHT = base["PREFIX"], base["LEFT"], base["RIGHT"]
LL, LR, IDENTITY = base["LIVE_LEFT"], base["LIVE_RIGHT"], base["IDENTITY"]
EXECUTOR, COMPACT = base["EXECUTOR"], base["LIVE_ENVIRONMENT"]
ENTRY = PREFIX + "RelationalRealMultiplication_produceMultiplication"
LIVE = PREFIX + "RelationalRealMultiplication_multiplicationLiveStep"
ENVIRONMENT = PREFIX + "RelationalRealMultiplication_mulEnvironment"
ACTION = PREFIX + "SignedDyadicCode_mul"
BUDGET = PREFIX + "RelationalRealMultiplication_productBudget"
OBSERVER = PREFIX + "RelationalRealMultiplication_MultiplicationProduction_code___redArg"
NEXT, CODE, ANSWER = "l_product_probe_next", "l_product_probe_code", "l_product_probe_answer"
EVENT = "l_product_probe_event"
NAT_ADD = "l_product_probe_exact_nat_add"
PERFORM = PREFIX + "HeterogeneousRealRuntime_perform___redArg"
INSTALL = PREFIX + "RelationalRealMultiplication_multiplicationNext"
PROJECT_EVENT = PREFIX + "RelationalRealMultiplication_MultiplicationRichEvent_project___redArg"


def tag(name):
    return base["tagged"](name)


class ProductAnalysis(Analysis):
    def __init__(self, *args, validate=False, **kwargs):
        super().__init__(*args, **kwargs)
        self.validate = validate

    def global_value(self, name):
        body = self.functions.get(name, "")
        if ".m_fun" in body:
            return super().global_value(name)
        objects = re.search(r'\.m_objs\s*=\s*\{(.*?)\}', body, re.S)
        if objects:
            fields = {}
            for index, item in enumerate(split_arguments(objects[1])):
                scalar = re.fullmatch(r'\(\(lean_object\*\)\(\(\(size_t\)\((\d+)\) << 1\) \| 1\)\)', item)
                if scalar:
                    fields[index] = Value(number=int(scalar[1]))
                else:
                    symbols = re.findall(r'\b(?:l|lp)_\w+\b', item)
                    if len(symbols) != 1 or symbols[0] not in self.functions:
                        raise ValueError("Unsupported exact static field: " + item)
                    fields[index] = self.global_value(symbols[0])
            return Value(fields=fields)
        return super().global_value(name)

    def run(self, name, arguments):
        if name == NAT_ADD:
            number = sum(v.number for v in arguments) if all(v.number is not None for v in arguments) else None
            return Value(tags=frozenset().union(*(v.retained() for v in arguments)), number=number), 0, 0
        if name in (LEFT, RIGHT, LL, LR):
            role = "left" if name in (LEFT, LL) else "right"
            live = name in (LL, LR)
            phase = "probe" if arguments[1].number == 0 else "fine"
            if self.validate:
                expected = ("live-" if live else "current-") + role if phase == "probe" else role + "-probe-next"
                if arguments[0].retained() != frozenset({expected}):
                    raise ValueError("Wrong current/probe-successor archive: " + role + "/" + phase)
                if phase == "fine":
                    other = "right" if role == "left" else "left"
                    expected_budget = frozenset({"request", other + "-probe-positive", other + "-probe-negative"})
                    if arguments[1].retained() != expected_budget:
                        raise ValueError("Wrong cross-probe precision dependency: " + role)
            code = Value(fields={0: tag(role + "-" + phase + "-positive"),
                                 1: tag(role + "-" + phase + "-negative"), 2: Value(number=0)})
            resource = Value(tags=frozenset({role + "-" + phase}),
                             fields={0: code, 1: tag(role + "-" + phase + "-next")})
            if live:
                resource = Value(fields={0: resource.fields[1], 1: resource})
            count = int(name == self.target)
            return resource if self.capture else Value(), count, count
        if name == NEXT:
            return arguments[-1].fields.get(1, Value()), 0, 0
        if name in (CODE, ANSWER):
            return arguments[-1].fields.get(0, Value()), 0, 0
        if name == EVENT:
            return arguments[-1], 0, 0
        if name == IDENTITY:
            return arguments[0], 0, 0
        if name == ACTION:
            if self.validate:
                for value, role in zip(arguments, ("left", "right")):
                    if value.retained() != frozenset({role + "-fine-positive", role + "-fine-negative"}):
                        raise ValueError("Arithmetic action did not consume owned refinement: " + role)
            count = int(name == self.target)
            return tag("product-target") if self.capture else Value(), count, count
        if name == EXECUTOR and self.validate:
            if arguments[3].retained() != frozenset({"current-journal"}):
                raise ValueError("Wrong current arithmetic journal")
            # Explicit executor boundary: the shared executor gates check its
            # phase route. Here inspect its actual received owned pair and run
            # the concrete action callback, rather than exploring hypothetical
            # exclusive-reuse branches of every journal allocation.
            program = arguments[0]
            receive = program.fields.get(1, Value())
            action = program.fields.get(3, Value())
            expected_receive = PREFIX + "RelationalRealMultiplication_multiplicationProgram___redArg___lam__1"
            expected_action = PREFIX + "RelationalRealMultiplication_multiplicationProgram___redArg___lam__3"
            if receive.function != expected_receive or receive.fixed != 2 or action.function != expected_action or action.fixed != 2:
                raise ValueError("Product receive/action callback boundary changed")
            operands = Value(fields={0: receive.fields[0], 1: receive.fields[1]})
            for slot, role in ((0, "left"), (1, "right")):
                if role + "-fine" not in operands.fields[slot].retained():
                    raise ValueError("Product executor did not receive owned refinement: " + role)
            self.run(action.function, [action.fields[0], action.fields[1], Value(), operands])
            count = int(name == self.target)
            return tag("executed-action"), count, count
        return super().run(name, arguments)


def service(callback, live_callback):
    return Value(fields={0: tag("initial"), 1: Value(function=callback), 2: Value(function=NEXT),
                         3: Value(function=EVENT), 4: Value(function=CODE), 5: Value(function=IDENTITY),
                         6: Value(function=IDENTITY), 7: Value(function=IDENTITY),
                         8: Value(function=IDENTITY), 9: Value(function=live_callback), 10: Value(function=ANSWER)})


def live_environment(callback):
    return Value(fields={0: Value(function=IDENTITY), 1: Value(function=callback), 2: Value(function=ANSWER)})


def arguments():
    return [Value(), Value(), service(LEFT, LL), service(RIGHT, LR),
            tag("current-left"), tag("current-right"), tag("current-journal"), tag("request")]


def require_count(functions, params, entry, args, target, expected):
    def unmark(value):
        return Value(fields={slot: unmark(field) for slot, field in value.fields.items()},
                     function=value.function, fixed=value.fixed, number=value.number)
    args = [unmark(value) for value in args]
    _, low, high = ProductAnalysis(functions, params, base["shared"]["reachable"], target=target).run(entry, args)
    if (low, high) != (expected, expected):
        raise ValueError(f"{entry}: {target}: expected [{expected},{expected}], found [{low},{high}]")


def validate_current(functions, params):
    result, _, _ = ProductAnalysis(functions, params, base["shared"]["reachable"], target=EXECUTOR,
                                  capture=True, validate=True).run(ENTRY, arguments())
    for slot, expected in enumerate(("left-probe", "right-probe", "left-fine", "right-fine", "executed-action")):
        if expected not in result.fields.get(slot, Value()).retained():
            raise ValueError("Packet did not retain original chronological production: " + str(slot))
    return result


def validate_budget(functions, params):
    for lp, ln, ls, rp, rn, rs, p in ((17, 5, 2, 3, 8, 8, 7), (0, 0, 0, 0, 0, 0, 0),
                                    (10000, 10000, 20, 2, 1, 0, 3)):
        left = Value(fields={0: Value(number=lp), 1: Value(number=ln), 2: Value(number=ls)})
        right = Value(fields={0: Value(number=rp), 1: Value(number=rn), 2: Value(number=rs)})
        value, _, _ = ProductAnalysis(functions, params, base["shared"]["reachable"], target="",
                                      capture=True).run(BUDGET, [left, right, Value(number=p)])
        actual = [value.fields.get(i, Value()).number for i in range(4)]
        expected = [lp + ln + 1, rp + rn + 1, p + 1 + rp + rn + 1, p + 1 + lp + ln + 1]
        if actual != expected:
            raise ValueError("Incorrect numerical budget: " + str(actual) + " != " + str(expected))


def validate_consumers(functions, params):
    # Exact pinned stored-code path. Installation/event projection must not
    # invoke a child producer, the executor, or the arithmetic operation.
    target = tag("installed-target")
    production = Value(fields={0: Value(), 1: Value(), 2: Value(), 3: Value(),
                               4: Value(fields={1: Value(fields={1: target})})})
    observed, _, _ = ProductAnalysis(functions, params, base["shared"]["reachable"], target="",
                                     capture=True).run(OBSERVER, [production])
    if observed.retained() != frozenset({"installed-target"}):
        raise ValueError("Stored target projection changed")
    left, right = service(LEFT, LL), service(RIGHT, LR)
    archive = Value(fields={0: Value(), 1: Value(), 2: Value(), 3: Value(), 4: Value()})
    next_args = [Value(), Value(), left, right, archive, Value(), production]
    for entry, args in ((OBSERVER, [production]), (INSTALL, next_args)):
        for symbol in (LEFT, RIGHT, EXECUTOR, ACTION):
            require_count(functions, params, entry, args, symbol, 0)
    # Event projection recursively maps the owned finite outcomes. Check its
    # static graph, not an invented finite count for all recursion branches.
    graph = base["shared"]["reachable"](functions, PROJECT_EVENT)
    if any(symbol in graph for symbol in (PERFORM, EXECUTOR, ACTION)):
        raise ValueError("Event projection reconstructs target/production")


def validate_compact(functions, params):
    body, original = functions[ENVIRONMENT], params[ENVIRONMENT]
    compact = []
    for child in original[2:4]:
        made = re.findall(r'\b(\w+)\s*=\s*' + re.escape(COMPACT) + r'\(\s*' + re.escape(child) + r'\s*\);', body)
        if len(made) != 1:
            raise ValueError("Rich capture: compact child constructor changed")
        compact.extend(made)
        if len(re.findall(r'\b' + re.escape(made[0]) + r'\s*=', body)) != 1 or re.search(
                r'lean_(?:ctor|closure)_set\(\s*' + re.escape(made[0]) + r'\s*,', body):
            raise ValueError("Rich capture: compact child mutated")
    closure = re.search(r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' + re.escape(LIVE + "___boxed") +
                        r'\),\s*4,\s*2\);', body)
    if closure is None:
        raise ValueError("Rich capture: live callback shape changed")
    captures = re.findall(r'lean_closure_set\(\s*' + re.escape(closure[1]) + r',\s*(\d+),\s*(\w+)\s*\);', body)
    if captures != [("0", compact[0]), ("1", compact[1])]:
        raise ValueError("Rich capture: wrong callback captures")
    if len(re.findall(r'lean_ctor_set\(\w+,\s*9,\s*' + re.escape(closure[1]) + r'\);', body)) != 2:
        raise ValueError("Rich capture: wrong installed live callback")
    for slot in (8, 10):
        installed = re.findall(r'lean_ctor_set\(\w+,\s*' + str(slot) + r',\s*(\w+)\);', body)
        if len(installed) != 2 or installed[0] != installed[1] or re.search(r'\b' + re.escape(installed[0]) +
                r'\s*=\s*(?:l|lp)_\w+\s*;', body) is None:
            raise ValueError("Rich capture: live read/answer must be static")
    return closure[1], compact


def reject(check, functions, params, label, prefix):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(prefix):
            raise ValueError(f"Wrong mutation diagnostic {label}: {error}") from error
        print("REAL_MULTIPLICATION_MUTATION_REJECTED " + label)
        return
    raise ValueError("Mutation accepted: " + label)


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    texts.append("\n".join(f"LEAN_EXPORT lean_object* {n}(lean_object* a, lean_object* p){{ return a; }}"
                            for n in (LEFT, RIGHT, LL, LR)))
    texts.append("\n".join(f"LEAN_EXPORT lean_object* {n}(lean_object* a, lean_object* p, lean_object* r){{ return r; }}"
                            for n in (NEXT, CODE, EVENT)))
    texts.append("\n".join(f"LEAN_EXPORT lean_object* {n}(lean_object* a){{ return a; }}" for n in (ANSWER, IDENTITY)))
    functions = {}
    for source in texts:
        functions.update(base["shared"]["bodies"](source))
        base["add_static_objects"](functions, source)
    functions = {n: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', b) for n, b in functions.items()}
    # Exact literal conversion; unlike symbolic arithmetic this preserves the
    # zero probe request as a known scalar in the bounded analyser.
    functions = {n: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'lean_box(\1)', b) for n, b in functions.items()}
    # Exact semantics of the natural-add primitive; unlike a callback summary,
    # this also preserves concrete numerals for the budget mutation checks.
    functions = {n: re.sub(r'\blean_nat_add\(', NAT_ADD + "(", b) for n, b in functions.items()}
    params = base["parameters"](texts)
    for name, arity in ((ENTRY, 8), (LIVE, 4), (ENVIRONMENT, 4), (ACTION, 2), (BUDGET, 3), (OBSERVER, 1),
                        (INSTALL, 7), (PROJECT_EVENT, 3)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact product definition/arity: " + name)
    args = arguments()
    for target, count in ((LEFT, 2), (RIGHT, 2), (EXECUTOR, 1), (ACTION, 1), (BUDGET, 1)):
        require_count(functions, params, ENTRY, args, target, count)
        print(f"REAL_MULTIPLICATION_APPLICATION_OK {target}=[{count},{count}]")
    aliased = arguments()
    aliased[3], aliased[5] = aliased[2], aliased[4]
    for target, count in ((LEFT, 4), (RIGHT, 0), (ACTION, 1), (EXECUTOR, 1)):
        require_count(functions, params, ENTRY, aliased, target, count)
    validate_current(functions, params)
    validate_budget(functions, params)
    validate_consumers(functions, params)
    ProductAnalysis(functions, params, base["shared"]["reachable"], target=ACTION,
                    capture=True, validate=True).run(ENTRY, arguments())
    calls = set(re.findall(r'\b(\w+)\s*\(', functions[OBSERVER]))
    if any(n != "lean_ctor_get" and not n.startswith(("lean_inc", "lean_dec")) for n in calls):
        raise ValueError("Product readout reconstructs instead of projecting")

    original = params[ENTRY]
    # Both first probes must use the incoming archives, not initial states.
    for source, archive, label in ((2, 4, "reset-left-probe"), (3, 5, "reset-right-probe")):
        broken = dict(functions)
        pattern = re.escape(PERFORM) + r'\(' + re.escape(original[source]) + r',\s*' + re.escape(original[archive]) + r','
        broken[ENTRY], count = re.subn(pattern, PERFORM + "(" + original[source] + ", lean_ctor_get(" + original[source] + ", 0),", broken[ENTRY])
        if count != 1:
            raise ValueError("Probe mutation site changed")
        reject(validate_current, broken, params, label, "Wrong current/probe-successor archive")
    # Replace the computed probe successor at the second application only.
    for source, archive, label in ((2, 4, "reset-left-refinement"), (3, 5, "reset-right-refinement")):
        broken = dict(functions)
        pattern = re.escape(PERFORM) + r'\(' + re.escape(original[source]) + r',\s*(\w+)\s*,\s*(\w+)\s*\)'
        sites = list(re.finditer(pattern, broken[ENTRY]))
        if len(sites) != 2:
            raise ValueError("Refinement mutation site changed")
        site = sites[1]
        broken[ENTRY] = broken[ENTRY][:site.start(1)] + original[archive] + broken[ENTRY][site.end(1):]
        reject(validate_current, broken, params, label, "Wrong current/probe-successor archive")
    broken = dict(functions)
    broken[ENTRY], count = re.subn(r'(\b' + re.escape(EXECUTOR) + r'\([^;]*?,\s*)' + re.escape(original[6]) + r'(\s*,)',
                                   r'\1lean_box(0)\2', broken[ENTRY])
    if count != 1:
        raise ValueError("Journal mutation site changed")
    reject(validate_current, broken, params, "reset-journal", "Wrong current arithmetic journal")
    for slot in (0, 1):
        broken = dict(functions)
        # Substitute a zero code only at the budget call, retaining both actual probes.
        call = re.search(r'\b' + re.escape(BUDGET) + r'\((\w+),\s*(\w+),\s*(\w+)\)', broken[ENTRY])
        if call is None:
            raise ValueError("Budget mutation site changed")
        start, end = call.span(slot + 1)
        broken[ENTRY] = broken[ENTRY][:start] + "lean_box(0)" + broken[ENTRY][end:]
        reject(validate_current, broken, params, "discard-probe-budget-" + str(slot), "Wrong cross-probe precision dependency")
    broken = dict(functions)
    # Exchange the two probes only at the budget call; archives remain right.
    call = re.search(r'\b' + re.escape(BUDGET) + r'\((\w+),\s*(\w+),\s*(\w+)\)', broken[ENTRY])
    broken[ENTRY] = broken[ENTRY][:call.start()] + BUDGET + "(" + call[2] + ", " + call[1] + ", " + call[3] + ")" + broken[ENTRY][call.end():]
    reject(validate_current, broken, params, "swap-cross-amplitudes", "Wrong cross-probe precision dependency")
    for consumer in (OBSERVER, INSTALL):
        broken = dict(functions)
        broken[consumer] = broken[consumer].replace("{", "{ lean_object* duplicate; duplicate = " +
                                                   ACTION + "(lean_box(0),lean_box(0));", 1)
        reject(validate_consumers, broken, params, "recompute-target-in-" + consumer,
               consumer + ": " + ACTION + ": expected [0,0]")
    broken = dict(functions)
    broken[PROJECT_EVENT] = broken[PROJECT_EVENT].replace("{", "{ lean_object* duplicate; duplicate = " +
                                                       ACTION + "(lean_box(0),lean_box(0));", 1)
    reject(validate_consumers, broken, params, "recompute-target-in-event-projection", "Event projection reconstructs")
    for symbol, label in ((BUDGET, "drop-successor-error-bit"), (PREFIX + "probeAmplitude", "drop-probe-unit-margin")):
        broken = dict(functions)
        broken[symbol], count = re.subn(r'lean_box\(1\)', "lean_box(0)", broken[symbol])
        if count != 1:
            raise ValueError("Exact unit-budget mutation site changed: " + label)
        reject(validate_budget, broken, params, label, "Incorrect numerical budget")

    alias = "l_product_probe_double"
    broken = dict(functions)
    broken[alias] = "{ lean_object* ignored; ignored = " + ENTRY + "(p,d,l,r,la,ra,j,n); return " + ENTRY + "(p,d,l,r,la,ra,j,n); }"
    doubled_params = dict(params, **{alias: ["p", "d", "l", "r", "la", "ra", "j", "n"]})
    for target, count in ((LEFT, 4), (RIGHT, 4), (ACTION, 2), (EXECUTOR, 2)):
        require_count(broken, doubled_params, alias, args, target, count)
    preserves = PREFIX + "RelationalRealMultiplication_multiplicationProgram___redArg___lam__4"
    if preserves not in functions:
        raise ValueError("Missing exact erased-preservation callback")
    broken = dict(functions)
    broken[preserves] = broken[preserves].replace("{", "{ lean_object* duplicate; duplicate = " + ACTION + "(lean_box(0),lean_box(0));", 1)
    require_count(broken, params, ENTRY, args, ACTION, 2)

    live_args = [live_environment(LL), live_environment(LR),
                 Value(fields={0: tag("live-left"), 1: tag("live-right"), 2: tag("last")}), tag("request")]
    for target, count in ((LL, 2), (LR, 2), (ACTION, 1), (BUDGET, 1), (LEFT, 0), (RIGHT, 0), (EXECUTOR, 0)):
        require_count(functions, params, LIVE, live_args, target, count)
    ProductAnalysis(functions, params, base["shared"]["reachable"], target=ACTION,
                    capture=True, validate=True).run(LIVE, live_args)
    aliased_live = list(live_args)
    aliased_live[1] = aliased_live[0]
    for target, count in ((LL, 4), (LR, 0), (ACTION, 1)):
        require_count(functions, params, LIVE, aliased_live, target, count)
    closure, compact = validate_compact(functions, params)
    broken = dict(functions)
    capture = r'lean_closure_set\(' + re.escape(closure) + r',\s*0,\s*' + re.escape(compact[0]) + r'\);'
    broken[ENVIRONMENT], count = re.subn(capture, "lean_closure_set(" + closure + ", 0, " + params[ENVIRONMENT][2] + ");", broken[ENVIRONMENT])
    if count != 1:
        raise ValueError("Rich capture mutation site changed")
    reject(validate_compact, broken, params, "capture-rich-left-service", "Rich capture")
    print("REAL_MULTIPLICATION_CODEGEN_OK: current probes/exact probe successors/current journal; cross-probe budget origins; two calls per role/four under aliasing; one action and shared installed target; compact live capture/no rich executor; mutations checked")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"REAL_MULTIPLICATION_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
