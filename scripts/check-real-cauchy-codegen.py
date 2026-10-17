#!/usr/bin/env python3
"""Bounded pinned-C checks of the executed-family/common-Real adapter.

Concrete term execution is followed to the constitutive executor, with exact
current journal/request/producer. The existing limit source/grouping route is
checked compositionally. The generic executor, source/limit program bodies,
readout projections, rich next update, and received family laws are explicit
boundaries: Lean proves their contracts. This is neither a universal callback
verifier, a C semantics, nor a physical-memory/cost theorem.
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
C = PREFIX + "RelationalRealCauchy_"
A = PREFIX + "AuthoritativeRuntime_"
P = PREFIX + "ProducedCompleteness_"
EXEC, RAW = base["EXECUTOR"], A + "performRawSource"
TERM, LIVE = C + "termEnvironment___lam__3", C + "termLiveStep"
NEXT, CODE, FACTORY = C + "termEnvironment___lam__5", C + "termEnvironment___lam__1", C + "termEnvironment"
CAUCHY, CONVERGES = C + "termsCauchy___redArg", C + "termLimitNear___redArg"
SOURCE, GROUP = P + "sourceProgram", P + "LimitGrouping_program___redArg"
PRODUCE = P + "ExecutedCauchyFamily_produceSourceAt___redArg"
DIAGONAL = P + "ExecutedCauchyFamily_diagonalSourceAt___redArg"
COMPLETED = P + "ExecutedCauchyFamily_ProducedSourceAt_completedJournal___redArg"
LIMIT = P + "executeLimitProduction"
RAW_NEXT = A + "RawSourceStep_next___redArg"
READOUT = PREFIX + "ConstitutiveRuntime_ExecutedRequest_readout___redArg"
COMMON, COMPACT = base["COMMON_PERFORM"], base["LIVE_ENVIRONMENT"]
LEAF_EXEC = PREFIX + "HeterogeneousRealRuntime_leaf___lam__0"
AUTHORITATIVE = A + "ExecutedCauchyFamily_completeViaRuntime___lam__0"
RESPONSE = A + "executeResponse"
LAW, MONOTONE = "l_cauchy_probe_law", "l_cauchy_probe_monotone"


def require(value, expected, message):
    actual = value.tags if expected in ("current-state", "diagonal-source") else value.retained()
    if actual != frozenset({expected}):
        raise ValueError(message + ": " + expected)


def family():
    return Value(fields={0: tag("producer"), 1: tag("term-coherence"), 2: tag("real-modulus"),
                         3: Value(function=MONOTONE), 4: Value(function=LAW)})


def archive(side="current"):
    return Value(fields={0: Value(tags=frozenset({side + "-state"}),
                                 fields={0: tag(side + "-journal")}), 1: tag(side + "-reachable")})


class CauchyAnalysis(Analysis):
    def __init__(self, *args, watched="", **kwargs):
        super().__init__(*args, target="", capture=True, **kwargs)
        self.watched = watched

    def run(self, name, args):
        count = int(name == self.watched)
        if name == A + "initialState___redArg":
            return tag("initial-rich-state"), count, count
        if name == SOURCE:
            require(args[0], "producer", "Source program lost the received producer")
            return tag("source-program"), count, count
        if name == EXEC:
            if args[0].retained() == frozenset({"source-program"}):
                require(args[3], "current-journal", "Term reset its current source journal")
                require(args[4].fields.get(0, Value()), "term", "Term request changed index")
                require(args[4].fields.get(1, Value()), "precision", "Term request changed precision")
                return tag("source-execution"), count, count
            require(args[0], "group-program", "Limit grouping lost its exact source")
            require(args[3], "source-completed-journal", "Limit grouping reset its source successor")
            return tag("group-execution"), count, count
        if name == RAW_NEXT:
            require(args[1], "current-state", "Term next reset its current archive")
            require(args[2].fields[0], "term", "Term next changed index")
            require(args[2].fields[1], "precision", "Term next changed precision")
            require(args[3], "source-execution", "Term next reconstructed its owned source")
            return tag("next-state"), count, count
        if name == READOUT:
            require(args[2], "source-execution", "Term readout reconstructed its owned source")
            return tag("owned-code"), count, count
        if name == COMMON:
            require(args[0].fields.get(0, Value()).fields.get(0, Value()), "producer", "Live source lost producer")
            require(args[0].fields[1], "live-memory", "Live source reset its current memory")
            request = args[1].fields[0]
            require(request.fields[0], "term", "Live source changed term")
            require(request.fields[1], "precision", "Live source changed precision")
            return Value(fields={0: Value(fields={1: tag("live-next")}), 1: tag("live-event")}), count, count
        if name == LAW:
            for slot, expected in ((0, "accuracy"), (1, "left-journal"), (2, "right-journal"),
                                   (3, "left-request"), (4, "right-request"),
                                   (5, "left-index"), (6, "right-index"),
                                   (7, "left-beyond"), (8, "right-beyond"),
                                   (9, "left-execution"), (10, "right-execution")):
                require(args[slot], expected, "Cauchy law lost an exact received argument")
            return tag("received-near"), count, count
        if name == MONOTONE:
            for slot, expected in ((0, "accuracy"), (1, "right-precision"), (2, "right-beyond")):
                require(args[slot], expected, "Convergence lost its explicit modulus extension")
            return tag("right-index"), count, count
        if name == DIAGONAL:
            require(args[1], "precision", "Limit diagonal changed precision")
            return Value(tags=frozenset({"diagonal-source"}),
                         fields={0: Value(fields={0: tag("term"), 1: tag("precision")})}), count, count
        if name == GROUP:
            require(args[-1], "source-execution", "Limit action reconstructed its source")
            return tag("group-program"), count, count
        if name == COMPLETED:
            require(args[1], "current-journal", "Limit source successor reset journal")
            require(args[2], "diagonal-source", "Limit source successor changed request")
            return tag("source-completed-journal"), count, count
        if name == RESPONSE:
            # The caller constructs RuntimeRequest.limit (tag 1). Select its
            # actual C branch, not a summary of its calls/returned fields.
            require(args[3], "current-state", "Limit reset its current archive")
            require(args[4].fields.get(0, Value()), "precision", "Limit request changed precision")
            request = self.parameters[name][4]
            pattern = (r'\{\s*_start:\s*\{\s*if \(lean_obj_tag\(' + re.escape(request) +
                       r'\) == 0\)\s*(\{.*\})\s*else\s*(\{.*\})\s*\}\s*\}')
            selected = re.fullmatch(pattern, self.functions[name], re.S)
            if selected is None:
                raise ValueError("Pinned limit request dispatch shape changed")
            alias = "l_cauchy_selected_limit_dispatch"
            self.functions[alias], self.parameters[alias] = selected[2], self.parameters[name]
            value, low, high = self.run(alias, args)
            return value, low + count, high + count
        value, low, high = super().run(name, args)
        return value, low + count, high + count


def run(functions, params, entry, args, target="", expected=0):
    value, low, high = CauchyAnalysis(functions, params, base["shared"]["reachable"],
                                    watched=target).run(entry, args)
    if (low, high) != (expected, expected):
        raise ValueError(f"Cauchy multiplicity {entry}/{target}: expected {expected}, found [{low},{high}]")
    return value


def term_args():
    return [tag("term"), Value(), Value(), family(), archive(), tag("precision")]


def check_term(functions, params):
    for target in (RAW, EXEC):
        value = run(functions, params, TERM, term_args(), target, 1)
        require(value, "source-execution", "Term lost the one produced execution")
    arguments = [tag("term"), family(), archive(), tag("precision"), tag("source-execution")]
    result = run(functions, params, NEXT, arguments, RAW_NEXT, 1)
    require(result.fields[0], "next-state", "Term lost its next archive")
    for slot, expected in ((0, "current-state"), (1, "current-reachable"), (3, "source-execution")):
        require(result.fields[1].fields[slot], expected, "Term lost exact rawSource reachability")
    code_args = [tag("producer"), tag("term"), archive(), tag("precision"), tag("source-execution")]
    require(run(functions, params, CODE, code_args, READOUT, 1), "owned-code", "Term readout is not a projection")


def law_args(convergence=False):
    a, b = archive("left"), archive("right")
    right_request = tag("right-request")
    if convergence:
        production = Value(fields={0: Value(fields={0: right_request}), 1: tag("right-execution")})
        limit_step = Value(fields={1: production})
        return [family(), tag("accuracy"), tag("left-term"), tag("left-precision"), tag("right-precision"),
                a, b, tag("left-execution"), limit_step, tag("left-index"), tag("left-beyond"), tag("right-beyond")]
    return [family(), tag("accuracy"), tag("left-term"), tag("right-term"),
            tag("left-precision"), tag("right-precision"), a, b,
            tag("left-execution"), tag("right-execution"), tag("left-index"), tag("right-index"),
            tag("left-beyond"), tag("right-beyond")]


class RequestAnalysis(CauchyAnalysis):
    def run(self, name, args):
        if name == LAW:
            # Requests built here retain the exact term/precision; normalize
            # only their analysis tags before the full received-law check.
            for slot, side in ((3, "left"), (4, "right")):
                if args[slot].retained() != frozenset({side + "-request"}):
                    require(args[slot].fields.get(0, Value()), side + "-term", "Cauchy request lost term")
                    require(args[slot].fields.get(1, Value()), side + "-precision", "Cauchy request lost precision")
                    args[slot] = tag(side + "-request")
        return super().run(name, args)


def check_laws(functions, params):
    for entry in (CAUCHY, CONVERGES):
        graph = base["shared"]["reachable"](functions, entry)
        if any(any(part in name for part in ("_readoutsNear", "_canonicalStep", "_executeReal", "_stepAt", "_performRawSource")) for name in graph):
            raise ValueError("Cauchy proof reconstructs a canonical execution")
        for target, expected in ((LAW, 1), (MONOTONE, int(entry == CONVERGES))):
            value, low, high = RequestAnalysis(functions, params, base["shared"]["reachable"],
                                               watched=target).run(entry, law_args(entry == CONVERGES))
            if (low, high) != (expected, expected):
                raise ValueError("Cauchy proof multiplicity changed")
            require(value, "received-near", "Cauchy proof lost received witness")


def check_compact(functions, params):
    service = run(functions, params, FACTORY, [Value(), Value(), family(), tag("term")])
    step = service.fields[9]
    if step.function != LIVE or step.fixed != 2 or step.retained() != frozenset({"producer", "term"}):
        raise ValueError("Cauchy live closure captured rich family/modulus or lost index")
    compact = run(functions, params, COMPACT, [service])
    if compact.retained() != frozenset({"producer", "term"}):
        raise ValueError("Cauchy compact environment retained rich machinery")
    source = run(functions, params, C + "sourceEnvironment", [tag("producer")])
    dummy_closure = source.fields[1]
    if dummy_closure.function != C + "sourceEnvironment___lam__0___boxed" or dummy_closure.fixed or dummy_closure.retained():
        raise ValueError("Cauchy dummy modulus is not a closed zero")
    dummy = run(functions, params, dummy_closure.function, [tag("anything")])
    if dummy.retained() or dummy.number != 0:
        raise ValueError("Cauchy dummy modulus is not a closed zero")
    if functions[LIVE].count("lean_alloc_ctor(0, 1, 0)") != 1:
        raise ValueError("Cauchy live request is not the source route")
    live = run(functions, params, LIVE, [tag("producer"), tag("term"), tag("live-memory"), tag("precision")], COMMON, 1)
    require(live.fields[0], "live-next", "Cauchy live lost shared next")
    require(live.fields[1], "live-event", "Cauchy live lost shared event")


def check_limit(functions, params):
    real = run(functions, params, C + "limitReal", [Value(), Value(), family()])
    runtime = real.fields[0]
    if runtime.fields[0].retained() != family().retained():
        raise ValueError("Limit leaf changed its received family")
    if not re.search(r'lean_alloc_ctor\(0, 1, 0\)', functions[C + "limitReal"]):
        raise ValueError("Limit is no longer the authoritative leaf")
    if not re.search(r'lean_alloc_ctor\(1, 1, 0\)', functions[AUTHORITATIVE]):
        raise ValueError("Limit producer changed its request direction")
    for target, expected in ((PRODUCE, 1), (EXEC, 2), (GROUP, 1)):
        result = run(functions, params, LEAF_EXEC, [runtime.fields[1], archive(), tag("precision")], target, expected)
        require(result.fields[1].fields[1], "source-execution", "Leaf lost its exact source")
        require(result.fields[1].fields[2], "group-execution", "Leaf lost its exact grouping")
    for target, expected in ((PRODUCE, 1), (EXEC, 2), (GROUP, 1)):
        result = run(functions, params, LIMIT, [Value(), Value(), family(), tag("current-journal"), tag("precision")], target, expected)
        require(result.fields[1], "source-execution", "Limit lost its exact source")
        require(result.fields[2], "group-execution", "Limit lost its exact grouping")


def edit_argument(functions, params, entry, callee, slot, replacement):
    copied = dict(functions)
    pattern = re.escape(callee) + r'\(([^;]+)\)'
    matches = list(re.finditer(pattern, copied[entry]))
    if len(matches) != 1:
        raise ValueError("Cauchy mutation site changed: " + callee)
    match = matches[0]
    args = split_arguments(match[1])
    args[slot] = replacement
    copied[entry] = copied[entry][:match.start()] + callee + "(" + ", ".join(args) + ")" + copied[entry][match.end():]
    return copied


def reject(check, functions, params, label, expected):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(expected):
            raise ValueError(f"Wrong rejection for {label}: {error}") from error
        print("REAL_CAUCHY_MUTATION_REJECTED " + label)
        return
    raise ValueError("Cauchy mutation accepted: " + label)


def main():
    texts = [path.read_text(encoding="utf-8") for path in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    texts.append("\n".join(f"LEAN_EXPORT lean_object* {name}(lean_object* a){{ return a; }}" for name in (LAW, MONOTONE)))
    functions = {}
    for text in texts:
        functions.update(base["shared"]["bodies"](text))
        base["add_static_objects"](functions, text)
    functions = {name: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'lean_box(\1)',
                             re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body))
                 for name, body in functions.items()}
    params = base["parameters"](texts)
    for name, arity in ((TERM, 6), (NEXT, 5), (CODE, 5), (FACTORY, 4), (LIVE, 4), (CAUCHY, 14), (CONVERGES, 12), (LIMIT, 5)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing Cauchy C definition/arity: " + name)
    checks = (check_term, check_laws, check_compact, check_limit)
    for check in checks:
        check(functions, params)
        print("REAL_CAUCHY_ROUTE_OK " + check.__name__)
    mutations = (
        (check_term, TERM, RAW, 3, "lean_box(0)", "reset-term-state", "Term reset its current source journal"),
        (check_term, RAW, EXEC, 3, "lean_box(0)", "reset-term-journal", "Term reset its current source journal"),
        (check_term, TERM, RAW, 4, "lean_box(0)", "replace-term-request", "Term request changed index"),
        (check_term, NEXT, RAW_NEXT, 3, "lean_box(0)", "reconstruct-next-source", "Term next reconstructed its owned source"),
        (check_term, CODE, READOUT, 2, "lean_box(0)", "reconstruct-readout-source", "Term readout reconstructed its owned source"),
        (check_compact, LIVE, COMMON, 0, "lean_box(0)", "reset-live-memory", "Live source lost producer"),
        (check_limit, LIMIT, GROUP, 4, "lean_box(0)", "reconstruct-limit-source", "Limit action reconstructed its source"),
        (check_limit, LIMIT, EXEC, 3, "lean_box(0)", "reset-grouping-successor", "Limit grouping reset its source successor"),
        (check_limit, AUTHORITATIVE, RESPONSE, 3, "lean_box(0)", "reset-limit-current-state", "Limit reset its current archive"),
    )
    for check, entry, callee, slot, replacement, label, expected in mutations:
        reject(check, edit_argument(functions, params, entry, callee, slot, replacement), params, label, expected)
    for entry, slots in ((CAUCHY, (10, 11)), (CONVERGES, (10, 11))):
        for slot in slots:
            broken = edit_argument(functions, params, entry, "lean_apply_11", slot, "lean_box(0)")
            label = "terms" if entry == CAUCHY else "convergence"
            reject(check_laws, broken, params, f"lost-owned-execution-{label}-{slot}", "Cauchy law lost an exact received argument")
    broken = edit_argument(functions, params, CONVERGES, "lean_apply_3", 3, "lean_box(0)")
    reject(check_laws, broken, params, "lost-modulus-extension", "Convergence lost its explicit modulus extension")
    # Each capture slot must be producer/index, never the complete family/modulus.
    for slot in (0, 1):
        broken = dict(functions)
        body = broken[FACTORY]
        closure = re.search(r'(\w+) = lean_alloc_closure\(\(void\*\)\(' + re.escape(LIVE) + r'\), 4, 2\)', body)
        if closure is None:
            raise ValueError("Cauchy compact capture site changed")
        pattern = r'(lean_closure_set\(' + closure[1] + r', ' + str(slot) + r', )\w+(\);)'
        body, count = re.subn(pattern, r'\g<1>' + params[FACTORY][2] + r'\2', body)
        if count != 1:
            raise ValueError("Cauchy capture mutation site changed")
        broken[FACTORY] = body
        reject(check_compact, broken, params, f"capture-rich-family-{slot}", "Cauchy live closure captured rich family/modulus or lost index")
    broken = dict(functions)
    source = C + "sourceEnvironment"
    broken[source], count = re.subn(r'(lean_ctor_set\(\w+, 1, )\w+(\);)',
                                     r'\g<1>' + params[source][0] + r'\2', broken[source])
    if count != 1:
        raise ValueError("Dummy modulus installation mutation site changed")
    reject(check_compact, broken, params, "capture-producer-as-dummy-modulus", "Cauchy dummy modulus is not a closed zero")
    broken = dict(functions)
    broken[LIVE] = broken[LIVE].replace("lean_alloc_ctor(0, 1, 0)", "lean_alloc_ctor(1, 1, 0)")
    reject(check_compact, broken, params, "replace-source-by-limit-request", "Cauchy live request is not the source route")
    for entry, target, check in ((TERM, EXEC, check_term), (LIMIT, EXEC, check_limit)):
        broken = dict(functions)
        args = params[entry]
        # A second valid application with its result ignored still counts twice.
        body = "{ lean_object* ignored; ignored = " + entry + "(" + ",".join(args) + "); "
        broken[entry] = body + functions[entry][1:]
        # Avoid recursive mutation: the first call points to the original body.
        alias = "l_cauchy_original_" + str(len(args))
        broken[alias], broken[entry] = functions[entry], broken[entry].replace("= " + entry + "(", "= " + alias + "(", 1)
        changed_params = dict(params, **{alias: args})
        reject(check, broken, changed_params, "duplicate-valid-" + ("term" if entry == TERM else "limit"), "Cauchy multiplicity")
    print("REAL_CAUCHY_CODEGEN_OK")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError) as error:
        print("REAL_CAUCHY_CODEGEN_FAILED " + str(error), file=sys.stderr)
        raise SystemExit(1)
