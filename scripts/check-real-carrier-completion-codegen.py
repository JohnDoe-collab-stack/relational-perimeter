#!/usr/bin/env python3
"""Bounded compiled checks for the new carrier-completion orchestration.

The native production/continuation boundary is checked separately by
check-real-native-cauchy-codegen.py. This checks the new term/family adapters,
their current owned replies and inner moduli, and the single native packet
whose produced limit is subsequently projected and retained. Logical
comparison/unicity laws, erased equalities and callback internals are not
codegen claims. No universal C semantics, heap or physical cost claim.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
from unified_codegen_analysis import Analysis, Value, parameters, add_static_objects, split_arguments

ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))
PREFIX = "lp_relational_x2dperimeter_RelationalPerimeter_Constitution_Reals_"
F = PREFIX + "RelationalRealCarrierCompleteness_"
R = PREFIX + "RelationalRealAddition_"
N = PREFIX + "RelationalRealNativeCauchy_"
COMPLETE, FACTORY, TERM, LAW = F + "carrierCompletion", F + "carrierNativeFamily", F + "carrierNativeFamily___lam__0", F + "carrierNativeFamily___lam__2"
NATIVE, OF_TERMS = N + "nativeCompleteness", N + "NativeCauchyFamily_ofTerms"
OF_CARRIER, ENV, CODE = R + "ofCarrier", R + "environment", PREFIX + "HeterogeneousRealRuntime_Step_code___redArg"
TO_CARRIER, CONVERGENCE = R + "toCarrier", F + "nativeCarrierConvergence"
ALIGN = PREFIX + "RelationalRealFamilyTransport_alignOwnedNear___redArg"
TERMS, NUMERIC_LAW = "l_carrier_test_terms", "l_carrier_test_cauchy"
LEFT_MODULE, RIGHT_MODULE = "l_carrier_left_module", "l_carrier_right_module"
LEFT_MONO, RIGHT_MONO = "l_carrier_left_monotone", "l_carrier_right_monotone"


def tag(name):
    return Value(tags=frozenset({name}))


def require(value, name, message):
    if value.retained() != frozenset({name}):
        raise ValueError(message + ": " + name)


def require_args(args, names, message):
    if len(args) != len(names):
        raise ValueError(message + ": arity")
    for value, name in zip(args, names):
        require(value, name, message)


def carrier(side):
    return Value(tags=frozenset({side + "-carrier"}), fields={
        1: Value(function=LEFT_MODULE if side == "left" else RIGHT_MODULE),
        2: Value(function=LEFT_MONO if side == "left" else RIGHT_MONO)})


def native_packet():
    return Value(tags=frozenset({"native-packet"}), fields={
        slot: tag(name) for slot, name in enumerate(("realized-family", "produced-native-limit", "rich-service",
          "numerical-correspondence", "term-equivalence", "term-futures", "native-candidate", "native-convergence", "native-uniqueness"))})


class CompletionAnalysis(Analysis):
    def __init__(self, *args, mode, watched="", **kwargs):
        super().__init__(*args, target="", capture=True, **kwargs)
        self.mode, self.watched = mode, watched

    def run(self, name, args):
        count = int(name == self.watched)
        if self.mode == "completion":
            if name == FACTORY:
                require_args(args, ["perimeter", "depth", "received-family"], "Completion adapter changed input")
                return tag("adapted-native-family"), count, count
            if name == NATIVE:
                require_args(args, ["perimeter", "depth", "adapted-native-family"], "Native completion changed input")
                return native_packet(), count, count
            if name == TO_CARRIER:
                require_args(args, ["perimeter", "depth", "produced-native-limit"], "Carrier projection lost produced limit")
                return tag("produced-carrier-limit"), count, count
            if name == CONVERGENCE:
                require_args(args[:3], ["perimeter", "depth", "received-family"], "Convergence changed input family")
                if args[3].retained() != native_packet().retained():
                    raise ValueError("Convergence lost retained native packet")
                return tag("projected-convergence"), count, count
        if name == TERMS:
            if self.mode == "term":
                require_args(args, ["requested-index"], "Term adapter changed requested index")
                return tag("received-term-carrier"), count, count
            if len(args) != 1:
                raise ValueError("Family terms arity")
            if args[0].retained() == frozenset({"left-index"}):
                return carrier("left"), count, count
            require(args[0], "right-index", "Family adapter changed term index")
            return carrier("right"), count, count
        if name == OF_CARRIER:
            require_args(args[:2], ["perimeter", "depth"], "Term realization changed context")
            if self.mode == "term":
                require(args[2], "received-term-carrier", "Term realization lost received term")
                return tag("realized-term"), count, count
            for side in ("left", "right"):
                if args[2].tags == frozenset({side + "-carrier"}):
                    return tag(side + "-real"), count, count
            raise ValueError("Family realization changed source carrier")
        if name == ENV:
            require_args(args[:2], ["perimeter", "depth"], "Current-code environment changed context")
            for side in ("left", "right"):
                if args[2].retained() == frozenset({side + "-real"}):
                    return tag(side + "-environment"), count, count
            raise ValueError("Current-code environment changed source")
        if name == CODE:
            for side in ("left", "right"):
                if args[0].retained() == frozenset({side + "-environment"}):
                    require_args(args, [side + "-environment", side + "-archive", side + "-response", side + "-step"],
                                 "Carrier Cauchy lost owned current Step")
                    return tag(side + "-owned-code"), count, count
            raise ValueError("Carrier Cauchy lost owned environment")
        for function, side in ((LEFT_MODULE, "left"), (RIGHT_MODULE, "right")):
            if name == function:
                require_args(args, [side + "-response"], "Carrier Cauchy ignored inner module")
                return tag(side + "-inner-index"), count, count
        for function, side in ((LEFT_MONO, "left"), (RIGHT_MONO, "right")):
            if name == function:
                require_args(args, ["accuracy", side + "-response", side + "-response-extension"],
                             "Carrier Cauchy lost inner monotonicity")
                return tag(side + "-inner-extension"), count, count
        if name == NUMERIC_LAW:
            require_args(args, ["accuracy", "left-index", "right-index", "left-inner-index", "right-inner-index",
              "left-index-extension", "right-index-extension", "left-inner-extension", "right-inner-extension"],
              "Carrier Cauchy changed received numerical law arguments")
            return tag("received-near"), count, count
        if name == ALIGN:
            require_args(args, ["left-owned-code", "right-owned-code", "received-near"], "Carrier Cauchy lost owned Near alignment")
            return tag("owned-near"), count, count
        if name == OF_TERMS:
            require_args(args[:2], ["perimeter", "depth"], "Family factory changed context")
            return Value(fields={0: args[2], 1: tag("derived-kernels"), 2: args[3], 3: args[4], 4: args[5]}), count, count
        return super().run(name, args)


def analyse(functions, params, mode, entry, args, watched="", expected=1):
    result, low, high = CompletionAnalysis(functions, params, shared["reachable"], mode=mode, watched=watched).run(entry, args)
    if watched and (low, high) != (expected, expected):
        raise ValueError("Carrier route multiplicity changed: " + watched + f" [{low},{high}]")
    return result


def check_completion(functions, params):
    args = [tag("perimeter"), tag("depth"), tag("received-family")]
    for watched in (FACTORY, NATIVE, TO_CARRIER, CONVERGENCE):
        result = analyse(functions, params, "completion", COMPLETE, args, watched)
        if result.fields.get(0, Value()).retained() != native_packet().retained():
            raise ValueError("Completion discarded entire native packet")
        require(result.fields.get(1, Value()), "produced-carrier-limit", "Completion replaced projected limit")
        require(result.fields.get(2, Value()), "projected-convergence", "Completion replaced projected convergence")
        closure = result.fields.get(3, Value())
        if closure.function != F + "nativeCarrierUniqueness___boxed" or closure.fixed != 4:
            raise ValueError("Completion uniqueness no longer captures native production")
        if closure.fields.get(3, Value()).retained() != native_packet().retained():
            raise ValueError("Completion uniqueness lost retained native packet")
        require(closure.fields.get(2, Value()), "received-family", "Completion uniqueness changed family")


def check_term(functions, params):
    args = [Value(function=TERMS), tag("perimeter"), tag("depth"), tag("requested-index")]
    for watched in (TERMS, OF_CARRIER):
        require(analyse(functions, params, "term", TERM, args, watched), "realized-term", "Term adapter changed realized output")


def check_law(functions, params):
    args = [Value(function=TERMS), tag("perimeter"), tag("depth"), Value(function=NUMERIC_LAW)]
    args += [tag(name) for name in ("accuracy", "left-index", "right-index", "left-response", "right-response",
      "left-archive", "right-archive", "left-step", "right-step", "left-index-extension", "right-index-extension",
      "left-response-extension", "right-response-extension")]
    for watched, expected in ((TERMS, 2), (CODE, 2), (LEFT_MODULE, 1), (RIGHT_MODULE, 1),
      (LEFT_MONO, 1), (RIGHT_MONO, 1), (NUMERIC_LAW, 1), (ALIGN, 1)):
        require(analyse(functions, params, "law", LAW, args, watched, expected), "owned-near", "Family adapter replaced owned witness")


def check_factory(functions, params):
    family = Value(fields={0: tag("received-terms"), 1: tag("outer-module"), 2: tag("outer-monotonicity"), 3: tag("received-law")})
    result = analyse(functions, params, "factory", FACTORY, [tag("perimeter"), tag("depth"), family], OF_TERMS)
    require(result.fields.get(2, Value()), "outer-module", "Native family changed outer module")
    for slot, function, captures in ((0, TERM, ["received-terms", "perimeter", "depth"]),
      (3, F + "carrierNativeFamily___lam__1", ["outer-monotonicity"]),
      (4, LAW + "___boxed", ["received-terms", "perimeter", "depth", "received-law"])):
        closure = result.fields.get(slot, Value())
        if closure.function != function or closure.fixed != len(captures):
            raise ValueError("Native family changed adapter capture shape")
        for index, capture in enumerate(captures):
            require(closure.fields.get(index, Value()), capture, "Native family changed adapter capture")


def mutate(functions, entry, callee, occurrence, slot, replacement):
    body = functions[entry]
    sites = list(re.finditer(r'\b' + re.escape(callee) + r'\(', body))
    if occurrence >= len(sites):
        raise ValueError("Mutation call site changed: " + callee)
    start = sites[occurrence].end()
    depth, end = 1, start
    while depth:
        depth += (body[end] == '(') - (body[end] == ')')
        end += 1
    args = split_arguments(body[start:end - 1])
    args[slot] = replacement
    broken = dict(functions)
    broken[entry] = body[:start] + ", ".join(args) + body[end - 1:]
    return broken


def reject(check, functions, params, description, expected):
    try:
        check(functions, params)
    except ValueError as error:
        if not str(error).startswith(expected):
            raise ValueError("Mutation rejected for unrelated reason: " + description + ": " + str(error)) from error
        print("REAL_CARRIER_COMPLETION_MUTATION_REJECTED " + description)
        return
    raise ValueError("Carrier mutation accepted: " + description)


def main():
    texts = [path.read_text(encoding="utf-8") for path in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    functions = {}
    for source in texts:
        functions.update(shared["bodies"](source))
        add_static_objects(functions, source)
    functions = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body) for name, body in functions.items()}
    params = parameters(texts)
    for name, arity in ((COMPLETE, 3), (FACTORY, 3), (TERM, 4), (LAW, 17)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact carrier C route/arity: " + name)
    for check in (check_completion, check_term, check_law, check_factory):
        check(functions, params)
        print("REAL_CARRIER_COMPLETION_ROUTE_OK " + check.__name__)
    cases = [
      (check_completion, COMPLETE, FACTORY, 0, 2, "Completion adapter changed input"),
      (check_completion, COMPLETE, NATIVE, 0, 2, "Native completion changed input"),
      (check_completion, COMPLETE, TO_CARRIER, 0, 2, "Carrier projection lost produced limit"),
      (check_completion, COMPLETE, CONVERGENCE, 0, 3, "Convergence lost retained native packet"),
      (check_completion, COMPLETE, "lean_ctor_set", 0, 2, "Completion discarded entire native packet"),
      (check_completion, COMPLETE, "lean_ctor_set", 1, 2, "Completion replaced projected limit"),
      (check_completion, COMPLETE, "lean_closure_set", 3, 2, "Completion uniqueness lost retained native packet"),
      (check_term, TERM, "lean_apply_1", 0, 1, "Term adapter changed requested index"),
      (check_term, TERM, OF_CARRIER, 0, 2, "Term realization lost received term"),
      (check_law, LAW, CODE, 0, 1, "Carrier Cauchy lost owned current Step"),
      (check_law, LAW, CODE, 1, 1, "Carrier Cauchy lost owned current Step"),
      (check_law, LAW, CODE, 0, 3, "Carrier Cauchy lost owned current Step"),
      (check_law, LAW, CODE, 1, 3, "Carrier Cauchy lost owned current Step"),
      (check_law, LAW, "lean_apply_1", 2, 1, "Carrier Cauchy ignored inner module"),
      (check_law, LAW, "lean_apply_1", 3, 1, "Carrier Cauchy ignored inner module"),
      (check_law, LAW, "lean_apply_3", 0, 3, "Carrier Cauchy lost inner monotonicity"),
      (check_law, LAW, "lean_apply_3", 1, 3, "Carrier Cauchy lost inner monotonicity"),
      (check_law, LAW, "lean_apply_9", 0, 4, "Carrier Cauchy changed received numerical law arguments"),
      (check_law, LAW, "lean_apply_9", 0, 5, "Carrier Cauchy changed received numerical law arguments"),
      (check_law, LAW, "lean_apply_9", 0, 6, "Carrier Cauchy changed received numerical law arguments"),
      (check_law, LAW, "lean_apply_9", 0, 7, "Carrier Cauchy changed received numerical law arguments"),
      (check_law, LAW, ALIGN, 0, 0, "Carrier Cauchy lost owned Near alignment"),
      (check_law, LAW, ALIGN, 0, 1, "Carrier Cauchy lost owned Near alignment"),
      (check_law, LAW, ALIGN, 0, 2, "Carrier Cauchy lost owned Near alignment"),
      (check_factory, FACTORY, OF_TERMS, 0, 3, "Native family changed outer module"),
      (check_factory, FACTORY, "lean_closure_set", 4, 2, "Native family changed adapter capture"),
    ]
    for index, (check, entry, callee, occurrence, slot, expected) in enumerate(cases):
        reject(check, mutate(functions, entry, callee, occurrence, slot, "lean_box(0)"), params, str(index), expected)
    for callee in (NATIVE, TO_CARRIER):
        broken = dict(functions)
        call = re.search(r'\b' + re.escape(callee) + r'\([^;]+\)', broken[COMPLETE])
        if call is None:
            raise ValueError("Duplicate mutation site changed")
        # Duplicate after the original call, when all source operands exist;
        # do not inject before its native/family predecessor.
        broken[COMPLETE] = functions[COMPLETE].replace(call.group(0), call.group(0) + "; ignored = " + call.group(0), 1)
        broken[COMPLETE] = broken[COMPLETE].replace("{", "{ lean_object* ignored;", 1)
        reject(check_completion, broken, params, "duplicate-valid-" + callee, "Carrier route multiplicity changed")
    print("REAL_CARRIER_COMPLETION_CODEGEN_OK: four new routes and 28 rejected mutations; native packet/limit shared, owned Steps and both modules consumed; native runtime continuation checked by existing native gate; logical comparisons and callback internals excluded")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print("REAL_CARRIER_COMPLETION_CODEGEN_FAILED: " + str(error), file=sys.stderr)
        raise SystemExit(1)
