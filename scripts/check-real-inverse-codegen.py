#!/usr/bin/env python3
"""Pinned reciprocal C routes and mutation checks.

These bounded callback/def-use checks are not a C verifier, heap minimality or
cost theorem. Native source execution and quantitative certification are named
boundaries; their Lean types/proofs are audited separately. The arithmetic
executor boundary invokes every actual concrete phase callback, including
preservation and storage, so an extra division in those callbacks is counted.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
product = runpy.run_path(str(ROOT / "scripts/check-real-multiplication-codegen.py"))
base = product["base"]
Value, Analysis = base["Value"], product["ProductAnalysis"]
PREFIX, EXECUTOR = base["PREFIX"], base["EXECUTOR"]
R, D, K = (PREFIX + n for n in ("ReciprocalRuntime_", "ReciprocalDomain_", "DyadicReciprocal_"))
ENTRY, LIVE, ENV = R + "produce", R + "liveStep", R + "inverseEnvironment"
ACTION, DIVIDE = K + "computeReciprocal___redArg", K + "divideFuel___redArg"
AWAY, DIRECTION, ANCHOR = D + "away___redArg", D + "direction___redArg", D + "sourceSuccessor"
SP, ROUND = K + "sourcePrecision", K + "roundingPrecision"
EXECUTE = PREFIX + "RelationalRealAddition_executeAt"
ENVIRONMENT = PREFIX + "RelationalRealAddition_environment"
NONZERO = D + "nonzero___redArg"
STEP_CODE = PREFIX + "HeterogeneousRealRuntime_Step_code___redArg"
STEP_NEXT = PREFIX + "HeterogeneousRealRuntime_Step_next___redArg"
COMPACT = base["LIVE_ENVIRONMENT"]
COMPLETED = PREFIX + "ConstitutiveRuntime_ExecutedRequest_completedJournal___redArg"
OBSERVER, INSTALL, EVENT = R + "Production_code___redArg", R + "next", R + "RichEvent_project"
LIVE_CODE, LIVE_CHILD = R + "liveCode", "l_inverse_probe_live_source"
NAT_ADD = product["NAT_ADD"]


def tag(name):
    return Value(tags=frozenset({name}))


def expect(value, tags, message):
    if value.retained() != frozenset(tags):
        raise ValueError(message + ": " + str(value.retained()))


class InverseAnalysis(Analysis):
    def invoke(self, closure, arguments):
        if closure.function is None:
            raise ValueError("Inverse phase callback is unresolved")
        fixed = [closure.fields[i] for i in range(closure.fixed)]
        return self.run(closure.function, fixed + arguments)

    def run(self, name, args):
        count = int(name == self.target)
        if name == ENVIRONMENT:
            expect(args[2], {"source"}, "Wrong source environment")
            return tag("rich-service"), count, count
        if name in (AWAY, DIRECTION):
            expect(args[0], {"witness"}, "Lost received witness")
            return tag("away" if name == AWAY else "direction"), count, count
        if name == SP:
            expect(args[0], {"away"}, "Wrong precision-bound origin")
            expect(args[1], {"request"}, "Wrong source precision request")
            return tag("source-budget"), count, count
        if name == ROUND:
            expect(args[0], {"request"}, "Wrong rounding request")
            return tag("rounding-budget"), count, count
        if name == EXECUTE:
            expect(args[2], {"source"}, "Wrong executed source")
            expect(args[3], {"current-source"}, "Wrong current source archive")
            expect(args[4], {"source-budget"}, "Wrong source budget")
            return tag("source-step"), count, count
        if name == NONZERO:
            for value, tags, message in zip(args[2:],
                    ({"source"}, {"witness"}, {"current-source"}, {"source-budget"}, {"source-step"}),
                    ("Wrong certificate source", "Lost received witness", "Wrong certificate archive",
                     "Wrong certificate precision", "Certificate ignores received Step")):
                expect(value, tags, message)
            return tag("transported-nonzero"), count, count
        if name in (STEP_CODE, STEP_NEXT):
            expect(args[0], {"rich-service"}, "Wrong native Step service")
            expect(args[1], {"current-source"}, "Wrong native Step archive")
            expect(args[2], {"source-budget"}, "Wrong native Step precision")
            expect(args[3], {"source-step"}, "Observer ignores owned source Step")
            return tag("source-code" if name == STEP_CODE else "source-next"), count, count
        if name == ACTION:
            expect(args[0], {"direction"}, "Lost action direction")
            expect(args[1], {"source-code"}, "Action ignores owned source code")
            expect(args[2], {"rounding-budget"}, "Wrong action rounding budget")
            return Value(fields={0: tag("division-packet"), 1: tag("stored-target")}), count, count
        if name == EXECUTOR:
            expect(args[3], {"current-journal"}, "Wrong current arithmetic journal")
            program, request = args[0], Value(number=0)
            recv, lo, hi = self.invoke(program.fields[1], [request])
            searched, a, b = self.invoke(program.fields[2], [request, recv]); lo += a; hi += b
            acted, a, b = self.invoke(program.fields[3], [request, searched]); lo += a; hi += b
            accepted, a, b = self.invoke(program.fields[4], [request, searched, acted]); lo += a; hi += b
            authorization, a, b = self.invoke(program.fields[5], [request, searched, acted, accepted]); lo += a; hi += b
            decomposed, a, b = self.invoke(program.fields[6], [request, searched, acted, accepted, authorization]); lo += a; hi += b
            resumed, a, b = self.invoke(program.fields[7], [request, searched, acted, accepted, authorization, decomposed]); lo += a; hi += b
            stored, a, b = self.invoke(program.fields[8], [request, searched, acted, accepted, authorization, decomposed, resumed]); lo += a; hi += b
            return Value(fields={1: stored}), lo + count, hi + count
        if name == COMPLETED:
            expect(args[1], {"current-journal"}, "Wrong continued journal")
            return tag("completed-journal"), count, count
        if name == "l_List_appendTR___redArg":
            expect(args[0], {"old-history"}, "Chronology lost old history")
            return Value(fields={0: args[0], 1: args[1]}), count, count
        if name == LIVE_CHILD:
            expect(args[0], {"live-source"}, "Wrong current live memory")
            expect(args[1], {"source-budget"}, "Wrong live source budget")
            return Value(fields={0: tag("live-next"), 1: tag("source-code")}), count, count
        if name == base["IDENTITY"]:
            return args[0], count, count
        if name == LIVE_CODE:
            expect(args[0], {"direction"}, "Lost live direction")
            expect(args[1], {"source-code"}, "Live action ignores received answer")
            expect(args[2], {"request"}, "Wrong live rounding request")
            return tag("stored-target"), count, count
        if name == PREFIX + "HeterogeneousRealRuntime_liveFuture___redArg":
            return tag("live-future"), count, count
        if name == PREFIX + "HeterogeneousRealRuntime_sourceFuture___redArg":
            for value, label in zip(args, ("rich-service", "current-source", "source-budget", "source-step")):
                expect(value, {label}, "Event projection ignores owned Step")
            return tag("source-future"), count, count
        if name == PREFIX + "HeterogeneousRealRuntime_projectOutcome___redArg":
            expect(args[0], {"rich-service"}, "Event projection lost native service")
            expect(args[1], {"source-future"}, "Event projection reconstructs source future")
            return tag("projected-source-future"), count, count
        return super().run(name, args)


def args():
    return [Value(), Value(), tag("source"), tag("witness"), tag("current-source"),
            tag("current-journal"), tag("request")]


def run(functions, params, entry, arguments, target=""):
    return InverseAnalysis(functions, params, base["shared"]["reachable"],
                           target=target, capture=True).run(entry, arguments)


def validate_current(functions, params):
    for target in (EXECUTE, EXECUTOR, ACTION, NONZERO):
        result, low, high = run(functions, params, ENTRY, args(), target)
        if (low, high) != (1, 1):
            raise ValueError("Wrong inverse multiplicity: " + target + str((low, high)))
    operand = result.fields.get(0, Value())
    for slot, label in enumerate(("witness", "source-step", "transported-nonzero")):
        expect(operand.fields.get(slot, Value()), {label}, "Owned inverse operand lost")
    expect(result.fields[1].fields[1].fields[1].fields[1], {"stored-target"}, "Action target not stored")
    return result


def validate_consumers(functions, params):
    produced = validate_current(functions, params)
    observed, _, _ = run(functions, params, OBSERVER, [produced])
    expect(observed, {"stored-target"}, "Observer reconstructs target")
    archive = Value(fields={0: tag("current-source"), 1: tag("current-journal"),
                            2: tag("old-history"), 3: tag("last")})
    installed, _, _ = run(functions, params, INSTALL, args()[:4] + [archive, tag("request"), produced])
    for slot, labels in ((0, {"source-next"}), (1, {"completed-journal"}),
                         (2, {"old-history", "current-source", "current-journal", "request", "witness",
                              "source-step", "transported-nonzero", "division-packet", "stored-target"}),
                         (3, {"stored-target"})):
        expect(installed.fields.get(slot, Value()), labels, "Installation lost exact packet/chronology")
    event = Value(fields={0: archive, 1: tag("request"), 2: produced})
    event_args = args()[:4] + [event]
    projected, _, _ = run(functions, params, EVENT, event_args)
    expect(projected.fields.get(1, Value()), {"stored-target"}, "Event target not shared")
    for entry, arguments in ((OBSERVER, [produced]), (INSTALL, args()[:4] + [archive, tag("request"), produced]),
                             (EVENT, event_args)):
        for target in (EXECUTE, EXECUTOR, ACTION):
            _, low, high = run(functions, params, entry, arguments, target)
            if (low, high) != (0, 0):
                raise ValueError("Consumer reconstructs inverse: " + entry)


def validate_budget(functions, params):
    for away, precision in ((0, 0), (3, 7), (12, 2)):
        # Do not use the symbolic SP/ROUND boundaries for numeric arithmetic.
        numeric = Analysis(functions, params, base["shared"]["reachable"], target="", capture=True)
        source, _, _ = numeric.run(SP, [Value(number=away), Value(number=precision)])
        rounding, _, _ = numeric.run(ROUND, [Value(number=precision)])
        if source.number != precision + 2 + away + away or rounding.number != precision + 2:
            raise ValueError("Incorrect reciprocal budget")


class KernelAnalysis(Analysis):
    def run(self, name, args):
        count = int(name == self.target)
        if name == PREFIX + "powerOfTwo":
            return args[0], count, count
        if name == K + "magnitude":
            expect(args[0], {"kernel-direction"}, "Kernel lost direction")
            expect(args[1], {"positive", "negative", "source-scale"}, "Kernel denominator ignores source code")
            return tag("source-magnitude"), count, count
        if name == DIVIDE:
            for value in args[:2]:
                expect(value, {"source-scale", "rounding"}, "Division lost exact numerator/fuel")
            expect(args[2], {"source-magnitude"}, "Division lost source denominator")
            return Value(fields={0: tag("owned-quotient"), 1: tag("owned-remainder")}), count, count
        if name == K + "signedCode":
            for value, label in zip(args, ("kernel-direction", "owned-quotient", "rounding")):
                expect(value, {label}, "Kernel target ignores owned quotient/direction/rounding")
            return Value(fields=dict(enumerate(args))), count, count
        return super().run(name, args)


def validate_kernel(functions, params):
    code = Value(fields={0: tag("positive"), 1: tag("negative"), 2: tag("source-scale")})
    packet, low, high = KernelAnalysis(functions, params, base["shared"]["reachable"], target=DIVIDE, capture=True).run(
        ACTION, [tag("kernel-direction"), code, tag("rounding")])
    if (low, high) != (1, 1):
        raise ValueError("Kernel division multiplicity changed")
    expect(packet.fields.get(0, Value()), {"owned-quotient", "owned-remainder"}, "Kernel lost division packet")
    expect(packet.fields.get(1, Value()), {"kernel-direction", "owned-quotient", "rounding"}, "Kernel rebuilt target")


def validate_live(functions, params):
    native = Value(fields={0: Value(function=base["IDENTITY"]), 1: Value(function=LIVE_CHILD),
                           2: Value(function=base["IDENTITY"])})
    live_args = [native, tag("direction"), tag("away"),
                 Value(fields={0: tag("live-source"), 1: tag("last")}), tag("request")]
    for target, expected in ((LIVE_CHILD, 1), (LIVE_CODE, 1), (EXECUTE, 0), (EXECUTOR, 0)):
        value, low, high = run(functions, params, LIVE, live_args, target)
        if (low, high) != (expected, expected):
            raise ValueError("Wrong live inverse multiplicity")
    expect(value.fields[0].fields[0], {"live-next"}, "Live continuation lost exact child successor")
    expect(value.fields[0].fields[1], {"stored-target"}, "Live target not shared")
    expect(value.fields[1].fields[1], {"stored-target"}, "Live event recomputes target")


def validate_fallback(functions, params):
    body = functions[LIVE_CODE]
    # Require the actual tested magnitude to guard the exact else/positive
    # branch. A call inserted before the guard is rejected as well.
    pattern = (r'\b(\w+)\s*=\s*' + re.escape(K + "magnitude") + r'\((\w+),\s*(\w+)\);.*?'
               r'\b(\w+)\s*=\s*lean_nat_dec_lt\((\w+),\s*\1\);.*?'
               r'if\s*\(\4\s*==\s*0\)\s*\{(.*?)\}\s*else\s*\{(.*?)\}')
    match = re.search(pattern, body, re.S)
    if match is None or (match[2], match[3]) != tuple(params[LIVE_CODE][:2]):
        raise ValueError("Unsafe fallback guard")
    no, yes = match[6], match[7]
    if re.search(r'\b' + re.escape(match[5]) + r'\s*=\s*lean_box\(0\);', body) is None:
        raise ValueError("Unsafe fallback guard: comparison is not against zero")
    call = re.escape(ACTION) + r'\('
    if len(re.findall(call, body)) != 1 or re.search(call, no) or len(re.findall(call, yes)) != 1:
        raise ValueError("Division executed outside positive fallback branch")
    if re.search(re.escape(K + "signedCode") + r'\(' + re.escape(params[LIVE_CODE][0]) + r',\s*' +
                 re.escape(match[5]) + r',', no) is None or "return" not in no:
        raise ValueError("Fallback no longer returns a signed zero")
    # Both branches use the requested rounding, and the positive branch divides
    # the actual received source answer in the unchanged computational direction.
    for branch in (no, yes):
        rounding = re.search(r'\b(\w+)\s*=\s*' + re.escape(ROUND) + r'\(' +
                             re.escape(params[LIVE_CODE][2]) + r'\);', branch)
        if rounding is None:
            raise ValueError("Fallback lost requested rounding")
        if branch == yes:
            division = re.search(r'\b(\w+)\s*=\s*' + re.escape(ACTION) + r'\(' +
                re.escape(params[LIVE_CODE][0]) + r',\s*' + re.escape(params[LIVE_CODE][1]) +
                r',\s*' + re.escape(rounding[1]) + r'\);', branch)
            if division is None:
                raise ValueError("Live division ignores received answer/direction/rounding")
            projected = re.search(r'\b(\w+)\s*=\s*lean_ctor_get\(' + re.escape(division[1]) + r',\s*1\);', branch)
            if projected is None or re.search(r'\breturn\s+' + re.escape(projected[1]) + r'\s*;', branch) is None:
                raise ValueError("Live division target is not the stored packet target")


def validate_compact(functions, params):
    body = functions[ENV]
    source, witness = params[ENV][2:4]
    env = re.search(r'\b(\w+)\s*=\s*' + re.escape(ENVIRONMENT) + r'\([^;]*\b' + re.escape(source) + r'\);', body)
    if env is None:
        raise ValueError("Rich inverse live capture: missing native environment")
    compact = re.search(r'\b(\w+)\s*=\s*' + re.escape(COMPACT) + r'\(' + re.escape(env[1]) + r'\);', body)
    direction = re.search(r'\b(\w+)\s*=\s*' + re.escape(DIRECTION) + r'\(' + re.escape(witness) + r'\);', body)
    away = re.search(r'\b(\w+)\s*=\s*' + re.escape(AWAY) + r'\(' + re.escape(witness) + r'\);', body)
    closure = re.search(r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' + re.escape(LIVE + "___boxed") + r'\),\s*5,\s*3\);', body)
    if any(x is None for x in (compact, direction, away, closure)):
        raise ValueError("Rich inverse live capture: constructor shape changed")
    boxed = re.search(r'\b(\w+)\s*=\s*lean_box\(' + re.escape(direction[1]) + r'\);', body)
    captures = re.findall(r'lean_closure_set\(' + re.escape(closure[1]) + r',\s*(\d+),\s*(\w+)\);', body)
    if boxed is None or captures != [("0", compact[1]), ("1", boxed[1]), ("2", away[1])]:
        raise ValueError("Rich inverse live capture: wrong captured data")
    for value in (compact[1], env[1], away[1], boxed[1]):
        if len(re.findall(r'\b' + re.escape(value) + r'\s*=', body)) != 1 or re.search(
                r'lean_(?:ctor|closure)_set\(' + re.escape(value) + r',', body):
            raise ValueError("Rich inverse live capture: mutated capture")
    if len(re.findall(r'lean_ctor_set\(\w+,\s*9,\s*' + re.escape(closure[1]) + r'\);', body)) != 1:
        raise ValueError("Rich inverse live capture: wrong installed callback")
    for slot in (8, 10):
        static = re.search(r'lean_ctor_set\(\w+,\s*' + str(slot) + r',\s*(\w+)\);', body)
        if static is None or re.search(r'\b' + re.escape(static[1]) + r'\s*=\s*(?:l|lp)_\w+\s*;', body) is None:
            raise ValueError("Rich inverse live capture: read/answer not static")


def validate_anchor(functions, params):
    body = functions[ENV]
    anchor = re.search(r'\b(\w+)\s*=\s*' + re.escape(ANCHOR) + r'\(' + r',\s*'.join(map(re.escape, params[ENV])) + r'\);', body)
    if anchor is None or re.search(r'lean_ctor_set\(\w+,\s*0,\s*' + re.escape(anchor[1]) + r'\);', body) is None:
        raise ValueError("Inverse anchor lost executed witness successor")
    # Verify both direction branches project the owned source Step and matching
    # native input archive, then call Step.next; no initial source is admitted.
    branches = re.findall(r'\bif\s*\([^\n]*\)\s*\{(.*?)\}\s*else\s*\{(.*?)\}', functions[ANCHOR], re.S)
    if len(branches) != 1:
        raise ValueError("Inverse anchor direction shape changed")
    for role, branch in enumerate(branches[0]):
        order = re.search(r'\b(\w+)\s*=\s*lean_ctor_get\(' + re.escape(params[ANCHOR][-1]) + r',\s*0\);', branch)
        if order is None:
            raise ValueError("Inverse anchor lost owned order")
        pair = re.search(r'\b(\w+)\s*=\s*lean_ctor_get\(' + re.escape(order[1]) + r',\s*5\);', branch)
        archive = re.search(r'\b(\w+)\s*=\s*lean_ctor_get\(' + re.escape(order[1]) + r',\s*' + str(role) + r'\);', branch)
        if pair is None or archive is None:
            raise ValueError("Inverse anchor wrong direction archive")
        step = re.search(r'\b(\w+)\s*=\s*lean_ctor_get\(' + re.escape(pair[1]) + r',\s*' + str(role) + r'\);', branch)
        response = re.search(r'\b(\w+)\s*=\s*lean_ctor_get\(' + re.escape(order[1]) + r',\s*3\);', branch)
        if step is None or response is None or re.search(re.escape(STEP_NEXT) + r'\(\w+,\s*' + re.escape(archive[1]) +
                r',\s*' + re.escape(response[1]) + r',\s*' + re.escape(step[1]) + r'\)', branch) is None:
            raise ValueError("Inverse anchor wrong owned successor")


def reject(check, functions, params, label, prefix):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(prefix):
            raise ValueError("Wrong inverse mutation diagnostic " + label + ": " + str(error)) from error
        print("REAL_INVERSE_MUTATION_REJECTED " + label)
        return
    raise ValueError("Inverse mutation accepted: " + label)


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    texts.append(f"LEAN_EXPORT lean_object* {base['IDENTITY']}(lean_object* a){{ return a; }}")
    functions = {}
    for text in texts:
        functions.update(base["shared"]["bodies"](text)); base["add_static_objects"](functions, text)
    functions = {n: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', b) for n, b in functions.items()}
    functions = {n: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'lean_box(\1)', b) for n, b in functions.items()}
    functions = {n: re.sub(r'\blean_nat_add\(', NAT_ADD + "(", b) for n, b in functions.items()}
    params = base["parameters"](texts)
    for name, arity in ((ENTRY, 7), (LIVE, 5), (ENV, 4), (ACTION, 3), (SP, 2), (ROUND, 1),
                        (OBSERVER, 1), (INSTALL, 7), (LIVE_CODE, 3), (ANCHOR, 4)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact inverse definition/arity: " + name)
    validate_current(functions, params); validate_consumers(functions, params)
    validate_budget(functions, params); validate_fallback(functions, params)
    validate_compact(functions, params); validate_anchor(functions, params)
    validate_kernel(functions, params)
    validate_live(functions, params)

    def replace_call_argument(bodies, name, callee, index, replacement):
        match = re.search(re.escape(callee) + r'\(([^;]*?)\)', bodies[name])
        if match is None:
            raise ValueError("Missing inverse mutation site")
        values = product["split_arguments"](match[1]); values[index] = replacement
        bodies[name] = bodies[name][:match.start()] + callee + "(" + ", ".join(values) + ")" + bodies[name][match.end():]

    for callee, index, label, prefix in ((EXECUTE, 3, "reset-current-source", "Wrong current source archive"),
            (EXECUTE, 4, "discard-source-budget", "Wrong source budget"),
            (AWAY, 0, "discard-witness-bound", "Lost received witness"),
            (NONZERO, 6, "certify-reconstructed-step", "Certificate ignores received Step"),
            (EXECUTOR, 3, "reset-current-journal", "Wrong current arithmetic journal")):
        broken = dict(functions); replace_call_argument(broken, ENTRY, callee, index, "lean_box(0)")
        reject(validate_current, broken, params, label, prefix)
    act = R + "program___lam__3"
    for index, label, prefix in ((0, "lose-direction", "Lost action direction"),
                                 (1, "recompute-source-code", "Action ignores owned source code"),
                                 (2, "discard-rounding-budget", "Wrong action rounding budget")):
        broken = dict(functions); replace_call_argument(broken, act, ACTION, index, "lean_box(0)")
        reject(validate_current, broken, params, label, prefix)
    for name in (OBSERVER, INSTALL):
        broken = dict(functions)
        broken[name] = broken[name].replace("{", "{ lean_object* duplicate; duplicate = " + ACTION + "(lean_box(0),lean_box(0),lean_box(0));", 1)
        reject(validate_consumers, broken, params, "recompute-target-" + name, "Lost action direction")
    # Valid duplicate applications, not merely ill-typed/artificial arguments.
    for name, callee, check, prefix, label in ((act, ACTION, validate_current, "Wrong inverse multiplicity", "duplicate-valid-action"),
            (ENTRY, EXECUTE, validate_current, "Wrong inverse multiplicity", "duplicate-valid-source"),
            (ACTION, DIVIDE, validate_kernel, "Kernel division multiplicity", "duplicate-valid-division")):
        broken = dict(functions)
        site = re.search(re.escape(callee) + r'\(([^;]*?)\);', broken[name])
        if site is None:
            raise ValueError("Missing valid duplicate mutation site")
        broken[name] = broken[name][:site.end()] + " lean_object* discarded; discarded = " + callee + "(" + site[1] + ");" + broken[name][site.end():]
        reject(check, broken, params, label, prefix)
    broken = dict(functions); replace_call_argument(broken, ACTION, K + "signedCode", 1, "lean_box(0)")
    reject(validate_kernel, broken, params, "target-not-from-owned-quotient", "Kernel target ignores")
    broken = dict(functions); replace_call_argument(broken, ACTION, K + "magnitude", 1, "lean_box(0)")
    reject(validate_kernel, broken, params, "denominator-not-from-source", "Kernel denominator ignores")
    for index, label, prefix in ((1, "reset-live-source-memory", "Wrong current live memory"),
                                 (2, "discard-live-source-budget", "Wrong live source budget")):
        broken = dict(functions); replace_call_argument(broken, LIVE, "lean_apply_2", index, "lean_box(0)")
        reject(validate_live, broken, params, label, prefix)
    broken = dict(functions)
    site = re.search(r'lean_apply_2\(([^;]*?)\);', broken[LIVE])
    broken[LIVE] = broken[LIVE][:site.end()] + " lean_object* discarded; discarded = lean_apply_2(" + site[1] + ");" + broken[LIVE][site.end():]
    reject(validate_live, broken, params, "duplicate-valid-live-source", "Wrong live inverse multiplicity")
    preserves = R + "program___lam__4"
    broken = dict(functions)
    # Count an extra division even when its value is discarded in preservation.
    broken[preserves] = broken[preserves].replace("{", "{ lean_object* duplicate; duplicate = " + ACTION + "(lean_box(0),lean_box(0),lean_box(0));", 1)
    reject(validate_current, broken, params, "extra-division-in-preservation", "Lost action direction")
    for symbol in (SP, ROUND):
        broken = dict(functions); broken[symbol] = broken[symbol].replace("lean_box(2)", "lean_box(1)", 1)
        reject(validate_budget, broken, params, "under-budget-" + symbol, "Incorrect reciprocal budget")
    broken = dict(functions)
    guard = re.search(r'if\s*\((\w+)\s*==\s*0\)', broken[LIVE_CODE])
    broken[LIVE_CODE] = broken[LIVE_CODE][:guard.start()] + "if (" + guard[1] + " == 1)" + broken[LIVE_CODE][guard.end():]
    reject(validate_fallback, broken, params, "reverse-positive-guard", "Unsafe fallback guard")
    broken = dict(functions)
    broken[LIVE_CODE] = broken[LIVE_CODE].replace("{", "{ lean_object* invalid; invalid = " + ACTION + "(lean_box(0),lean_box(0),lean_box(0));", 1)
    reject(validate_fallback, broken, params, "division-before-positive-guard", "Division executed outside")
    for slot, label in ((0, "capture-rich-source"), (1, "capture-rich-witness"), (2, "capture-rich-certificate")):
        broken = dict(functions)
        closure = re.search(r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' + re.escape(LIVE + "___boxed") + r'\)', broken[ENV])
        pattern = r'(lean_closure_set\(' + re.escape(closure[1]) + r',\s*' + str(slot) + r',\s*)\w+(\);)'
        broken[ENV], count = re.subn(pattern, r'\g<1>' + params[ENV][2 if slot == 0 else 3] + r'\2', broken[ENV])
        if count != 1:
            raise ValueError("Missing inverse capture mutation site")
        reject(validate_compact, broken, params, label, "Rich inverse live capture")
    broken = dict(functions); replace_call_argument(broken, ENV, ANCHOR, 3, "lean_box(0)")
    reject(validate_anchor, broken, params, "reset-witness-source-anchor", "Inverse anchor lost")
    print("REAL_INVERSE_CODEGEN_OK: current source/witness/successor/journal, explicit budgets, one source/action/division packet, shared target and chronological archive, fallback without division, compact native environment+direction+away; mutations checked")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, IndexError) as error:
        print("REAL_INVERSE_CODEGEN_FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
