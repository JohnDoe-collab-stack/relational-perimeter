#!/usr/bin/env python3
"""Bounded pinned-C checks of shared-term limit mediation and trace projection.

Native Real execution, native Step.next, Near symmetry/composition, and received
convergence/rate callbacks are explicit boundaries. The trace cons branch is
checked once, including its actual recursive-call arguments; the recursive tail
is a named boundary. This is not a C semantics or a universal callback verifier.
No persistent service or new live memory is introduced by this finite trace.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
from unified_codegen_analysis import split_arguments

ROOT = Path(__file__).resolve().parent.parent
base = runpy.run_path(str(ROOT / "scripts/check-real-addition-codegen.py"))
Value, Analysis, PREFIX = base["Value"], base["Analysis"], base["PREFIX"]
tag = base["tagged"]
U = PREFIX + "RelationalRealLimitUniqueness_"
MEDIATE, TRACE, PROJECT = U + "mediate", U + "produceTrace", U + "UniquenessTrace_toNumerical"
FUTURE = U + "numericalFutures___lam__0"
EXECUTE, ENV = PREFIX + "RelationalRealAddition_executeAt", PREFIX + "RelationalRealAddition_environment"
TERM, TERM_ENV = PREFIX + "RelationalRealCauchy_termReal", PREFIX + "RelationalRealCauchy_termEnvironment"
NEXT = PREFIX + "HeterogeneousRealRuntime_Step_next___redArg"
SYM, COMPOSE = PREFIX + "Near_symm___redArg", PREFIX + "Near_compose___redArg"
MODULUS, LEFT_RATE, RIGHT_RATE, LEFT_LAW, RIGHT_LAW = (
    "l_unique_modulus", "l_unique_left_rate", "l_unique_right_rate", "l_unique_left_law", "l_unique_right_law")


def require(value, expected, message):
    if value.retained() != frozenset({expected}):
        raise ValueError(message + ": " + expected)


def number(value, expected, message):
    if value.number != expected:
        raise ValueError(message + f": expected {expected}, found {value.number}")


def candidate(side):
    return Value(fields={0: tag(side + "-real"), 1: Value(function=LEFT_RATE if side == "first" else RIGHT_RATE),
                         2: Value(function=LEFT_LAW if side == "first" else RIGHT_LAW)})


def common_args():
    return [Value(), Value(), Value(fields={2: Value(function=MODULUS)}), candidate("first"), candidate("second")]


def query():
    # p=2, rates at p+1 are 7 and 10, T=17, responses 20 and 21.
    return Value(fields={i: Value(number=n) for i, n in enumerate((2, 20, 21, 3, 4))})


def archives():
    return [tag(side + "-current") for side in ("term", "first", "second")]


def packet():
    return Value(fields={0: Value(fields={0: tag("term-current"),
                                        1: Value(fields={0: tag("first-current"), 1: tag("second-current")})}),
                         1: tag("term-step"), 2: tag("first-step"), 3: tag("second-step"),
                         4: tag("first-near"), 5: tag("second-near"), 6: tag("composed-near")})


class UniquenessAnalysis(Analysis):
    def __init__(self, *args, watched="", mode="mediate", **kwargs):
        super().__init__(*args, target="", capture=True, **kwargs)
        self.watched, self.mode = watched, mode

    def run(self, name, args):
        count = int(name == self.watched)
        if name == "l_unique_nat_add":
            if any(value.number is None for value in args):
                raise ValueError("Unknown uniqueness precision arithmetic")
            return Value(number=args[0].number + args[1].number), count, count
        if name == MODULUS:
            number(args[0], 3, "Mediator modulus did not receive p+1")
            return Value(number=13), count, count
        if name in (LEFT_RATE, RIGHT_RATE):
            number(args[0], 3, "Candidate rate did not receive p+1")
            return Value(number=7 if name == LEFT_RATE else 10), count, count
        if name == TERM:
            number(args[3], 13, "Mediator index does not come from modulus(p+1)")
            return tag("term-real"), count, count
        if name == ENV:
            return args[2], count, count
        if name == EXECUTE:
            role = next((side for side in ("term", "first", "second")
                         if args[2].retained() == frozenset({side + "-real"})), None)
            if role is None:
                raise ValueError("Unknown uniqueness execution role")
            require(args[3], role + "-current", "Uniqueness execution reset its current archive")
            number(args[4], {"term": 3, "first": 20, "second": 21}[role], "Uniqueness execution lost its response budget")
            result = tag(role + "-step")
            hit = int(self.watched == "execute-" + role)
            return result, count + hit, count + hit
        if name in (LEFT_LAW, RIGHT_LAW):
            side = "first" if name == LEFT_LAW else "second"
            for slot, expected in ((0, 3), (1, 13), (2, 3), (3, 20 if side == "first" else 21),
                                   (8, 0), (9, 0), (10, 13 if side == "first" else 11)):
                number(args[slot], expected, "Convergence lost a positive precision/index extension")
            for slot, expected in ((4, "term-current"), (5, side + "-current"),
                                   (6, "term-step"), (7, side + "-step")):
                require(args[slot], expected, "Convergence lost its exact shared term/candidate Step")
            return tag(side + "-near"), count, count
        if name == SYM:
            require(args[0], "first-near", "Uniqueness symmetrizes the wrong convergence")
            return tag("symmetric-first"), count, count
        if name == COMPOSE:
            require(args[0], "symmetric-first", "Uniqueness composition lost its first direction")
            require(args[1], "second-near", "Uniqueness composition lost its second convergence")
            return tag("composed-near"), count, count
        if name == MEDIATE and self.mode != "mediate":
            for slot, side in ((5, "term"), (6, "first"), (7, "second")):
                require(args[slot], side + "-current", "Trace mediation reset an incoming archive")
            return packet(), count, count
        if name == NEXT:
            role = next((side for side in ("term", "first", "second")
                         if args[0].retained() == frozenset({side + "-real"})), None)
            if role is None:
                raise ValueError("Trace successor changed environment")
            require(args[1], role + "-current", "Trace successor changed incoming archive")
            require(args[3], role + "-step", "Trace successor lost its exact owned Step")
            number(args[2], {"term": 3, "first": 20, "second": 21}[role], "Trace successor changed response precision")
            return tag(role + "-next"), count, count
        if name == TRACE:
            for slot, side in ((5, "term"), (6, "first"), (7, "second")):
                require(args[slot], side + ("-current" if self.mode == "future" else "-next"),
                        "Trace recursion lost one of its three exact successors")
            require(args[8], "queries" if self.mode == "future" else "remaining", "Trace recursion changed query tail")
            return tag("whole-rich-trace" if self.mode == "future" else "rich-tail"), count, count
        if name == PROJECT:
            if self.mode == "future":
                for slot, side in ((5, "term"), (6, "first"), (7, "second")):
                    require(args[slot], side + "-current", "Future projection changed its original archives")
                require(args[8], "queries", "Future projection changed query list")
                require(args[9], "whole-rich-trace", "Future projection did not consume its one produced rich trace")
                return tag("whole-numerical-trace"), count, count
            for slot, side in ((5, "term"), (6, "first"), (7, "second")):
                require(args[slot], side + "-next", "Projection recursion lost exact successors")
            require(args[8], "remaining", "Projection changed query tail")
            require(args[9], "rich-tail", "Projection lost the already owned rich tail")
            return tag("numerical-tail"), count, count
        if name == TERM_ENV:
            number(args[3], 0, "Future did not choose the declared initial term context")
            return Value(fields={0: tag("term-current")}), count, count
        value, low, high = super().run(name, args)
        return value, low + count, high + count


def run(functions, params, entry, args, target="", expected=0, mode="mediate"):
    result, low, high = UniquenessAnalysis(functions, params, base["shared"]["reachable"],
                                          watched=target, mode=mode).run(entry, args)
    if (low, high) != (expected, expected):
        raise ValueError(f"Uniqueness multiplicity {target}: expected {expected}, found [{low},{high}]")
    return result


def cons_branch(functions, params, entry, query_slot):
    condition = params[entry][query_slot]
    pattern = (r'\{\s*_start:\s*\{\s*if \(lean_obj_tag\(' + re.escape(condition) +
               r'\) == 0\)\s*(\{.*\})\s*else\s*(\{.*\})\s*\}\s*\}')
    match = re.fullmatch(pattern, functions[entry], re.S)
    if match is None:
        raise ValueError("Pinned uniqueness list-branch shape changed")
    alias = "l_unique_cons_" + str(query_slot)
    return dict(functions, **{alias: match[2]}), dict(params, **{alias: params[entry]}), alias


def check_mediate(functions, params):
    args = common_args() + archives() + [query()]
    for target in ("execute-term", "execute-first", "execute-second", LEFT_LAW, RIGHT_LAW, COMPOSE):
        result = run(functions, params, MEDIATE, args, target, 1)
        for slot, expected in ((1, "term-step"), (2, "first-step"), (3, "second-step"),
                               (4, "first-near"), (5, "second-near"), (6, "composed-near")):
            require(result.fields[slot], expected, "Mediation lost a stored exact resource")
        require(result.fields[0].fields[0], "term-current", "Mediation lost incoming term archive")
        require(result.fields[0].fields[1].fields[0], "first-current", "Mediation lost incoming first archive")
        require(result.fields[0].fields[1].fields[1], "second-current", "Mediation lost incoming second archive")


def check_trace(functions, params):
    functions, params, entry = cons_branch(functions, params, TRACE, 8)
    args = common_args() + archives() + [Value(fields={0: query(), 1: tag("remaining")})]
    for target, expected in ((MEDIATE, 1), (TRACE, 1), (EXECUTE, 0)):
        result = run(functions, params, entry, args, target, expected, "trace")
        require(result.fields[5].fields[1], "term-step", "Trace lost its one mediator packet")
        require(result.fields[6], "rich-tail", "Trace lost its owned continuation")


def check_projection(functions, params):
    functions, params, entry = cons_branch(functions, params, PROJECT, 8)
    rich = Value(fields={5: packet(), 6: tag("rich-tail")})
    args = common_args() + archives() + [Value(fields={0: query(), 1: tag("remaining")}), rich]
    for target, expected in ((PROJECT, 1), (MEDIATE, 0), (EXECUTE, 0), (LEFT_LAW, 0), (RIGHT_LAW, 0), (COMPOSE, 0)):
        result = run(functions, params, entry, args, target, expected, "projection")
        for slot, expected_tag in ((4, "first-step"), (5, "second-step"), (6, "composed-near"), (7, "numerical-tail")):
            require(result.fields[slot], expected_tag, "Numerical projection reconstructed/lost a stored result")


def check_future(functions, params):
    args = common_args() + [tag("first-current"), tag("second-current"), tag("queries")]
    for target in (TRACE, PROJECT):
        require(run(functions, params, FUTURE, args, target, 1, "future"),
                "whole-numerical-trace", "Future lost the shared whole-list trace")
    for name in ("uniqueness", "unique"):
        body = functions[U + name]
        if PREFIX + "RelationalRealAddition_NumericalFutureEquivalent_toEquivalent" not in body:
            raise ValueError("Uniqueness does not derive Equivalent from its numerical futures")
    for name, body in functions.items():
        if name.startswith(U) and any(token in body for token in
            ("_Equivalent_refl", "_Equivalent_toFutures", "_currentReadout", "_readoutsNear", "_executeReal")):
            raise ValueError("Uniqueness replaced mediation by reflexivity/readout transport")


def mutate_call(functions, entry, callee, occurrence, slot, replacement):
    copied = dict(functions)
    matches = list(re.finditer(re.escape(callee) + r'\(([^;]+)\)', copied[entry]))
    if occurrence >= len(matches):
        raise ValueError("Uniqueness mutation call site changed")
    match = matches[occurrence]
    args = split_arguments(match[1])
    args[slot] = replacement
    copied[entry] = copied[entry][:match.start()] + callee + "(" + ",".join(args) + ")" + copied[entry][match.end():]
    return copied


def reject(check, functions, params, label, expected):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(expected):
            raise ValueError(f"Wrong mutation rejection {label}: {error}") from error
        print("REAL_LIMIT_UNIQUENESS_MUTATION_REJECTED " + label)
        return
    raise ValueError("Uniqueness mutation accepted: " + label)


def main():
    texts = [path.read_text(encoding="utf-8") for path in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    functions = {}
    for text in texts:
        functions.update(base["shared"]["bodies"](text))
        base["add_static_objects"](functions, text)
    # The shared analyser deliberately treats lean_* primitives as opaque
    # provenance unions. Give this pinned arithmetic primitive an explicit
    # local boundary so that p+1 and the positive extensions stay numerical.
    functions = {name: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'lean_box(\1)',
                             re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                             .replace("lean_nat_add(", "l_unique_nat_add("))
                 for name, body in functions.items()}
    params = base["parameters"](texts)
    for name, arity in ((MEDIATE, 9), (TRACE, 9), (PROJECT, 10), (FUTURE, 8)):
        if len(params.get(name, [])) != arity:
            raise ValueError("Missing exact uniqueness C definition/arity: " + name)
    for check in (check_mediate, check_trace, check_projection, check_future):
        check(functions, params)
        print("REAL_LIMIT_UNIQUENESS_ROUTE_OK " + check.__name__)
    for occurrence in range(3):
        broken = mutate_call(functions, MEDIATE, EXECUTE, occurrence, 3, "lean_box(0)")
        reject(check_mediate, broken, params, f"reset-execution-{occurrence}", "Uniqueness execution reset its current archive")
    for occurrence in range(2):
        for slot in (5, 6, 7, 8, 11):
            broken = mutate_call(functions, MEDIATE, "lean_apply_11", occurrence, slot, "lean_box(0)")
            expected = "Convergence lost a positive precision/index extension" if slot == 11 else "Convergence lost its exact shared term/candidate Step"
            reject(check_mediate, broken, params, f"convergence-{occurrence}-lost-{slot}", expected)
    for slot in (5, 6, 7):
        broken = mutate_call(functions, TRACE, TRACE, 0, slot, params[TRACE][slot])
        reject(check_trace, broken, params, f"reset-recursive-successor-{slot}", "Trace recursion lost one of its three exact successors")
    broken = mutate_call(functions, MEDIATE, SYM, 0, 0, "lean_box(0)")
    reject(check_mediate, broken, params, "lost-first-direction", "Uniqueness symmetrizes the wrong convergence")
    broken = mutate_call(functions, MEDIATE, COMPOSE, 0, 1, "lean_box(0)")
    reject(check_mediate, broken, params, "lost-second-near", "Uniqueness composition lost its second convergence")
    broken = mutate_call(functions, FUTURE, PROJECT, 0, 9, "lean_box(0)")
    reject(check_future, broken, params, "project-reconstructed-trace", "Future projection did not consume its one produced rich trace")
    # Two valid whole mediations still count twice if the first result is ignored.
    broken, changed_params = dict(functions), dict(params)
    alias = "l_unique_original_mediate"
    broken[alias], changed_params[alias] = functions[MEDIATE], params[MEDIATE]
    duplicate = "lean_object* ignored; ignored = " + alias + "(" + ",".join(params[MEDIATE]) + ");"
    broken[MEDIATE] = functions[MEDIATE].replace("{", "{" + duplicate, 1)
    reject(check_mediate, broken, changed_params, "duplicate-valid-mediation", "Uniqueness multiplicity")
    broken, changed_params = dict(functions), dict(params)
    alias = "l_unique_original_trace_mediation"
    broken[alias], changed_params[alias] = functions[MEDIATE], params[MEDIATE]
    calls = re.findall(r'\b' + re.escape(MEDIATE) + r'\([^;]+\);', functions[TRACE])
    if len(calls) != 1:
        raise ValueError("Trace duplication mutation site changed")
    broken[TRACE] = functions[TRACE].replace(calls[0], calls[0] + "lean_object* ignored; ignored = " + calls[0])
    reject(check_trace, broken, changed_params, "duplicate-trace-mediation", "Uniqueness multiplicity")
    # Projection may not recompute a valid candidate Step, even if ignored.
    p = params[PROJECT]
    injected = ("lean_object* ignored; ignored = " + EXECUTE + "(" + p[0] + "," + p[1] +
                ",lean_ctor_get(" + p[3] + ",0)," + p[6] + ",lean_box(20));")
    broken = dict(functions)
    broken[PROJECT] = functions[PROJECT].replace("else\n{", "else\n{" + injected, 1)
    if broken[PROJECT] == functions[PROJECT]:
        raise ValueError("Projection execution mutation site changed")
    reject(check_projection, broken, params, "projection-reexecutes-candidate", "Uniqueness multiplicity")
    print("REAL_LIMIT_UNIQUENESS_CODEGEN_OK")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError) as error:
        print("REAL_LIMIT_UNIQUENESS_CODEGEN_FAILED " + str(error), file=sys.stderr)
        raise SystemExit(1)
