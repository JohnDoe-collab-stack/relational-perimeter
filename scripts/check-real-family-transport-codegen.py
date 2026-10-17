#!/usr/bin/env python3
"""Bounded checks of effective-family/limit transport in pinned Lean C.

Proof-only equalities and ownership rewrites are NOT observed in C. Realized
Cauchy additionally reads the two owned stored action codes to align the
returned certificate lifts at its unchanged common scale. Reflected convergence
still erases its Step arguments. Lean audits check those contracts. C checks
direct route A, two fresh Steps only in the advertised observation, and the
distinct canonical numerical readout route. Received callbacks/native
execution/recursion remain boundaries, not universal cost/capture theorems.
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
F = PREFIX + "RelationalRealFamilyTransport_"
C = PREFIX + "RelationalRealCauchy_"
R = PREFIX + "RelationalRealAddition_"
U = PREFIX + "RelationalRealLimitUniqueness_"
PRODUCER = F + "realizeFamily___redArg___lam__2"
REALIZED = F + "realizeFamily___redArg___lam__3"
ALIGN = F + "alignOwnedNear___redArg"
READOUT = PREFIX + "ConstitutiveRuntime_ExecutedRequest_readout___redArg"
SOURCE_PROGRAM = PREFIX + "ProducedCompleteness_sourceProgram"
NUMERICAL = F + "readoutFamily___lam__2"
DIRECT = F + "returnedCandidate___lam__1"
PROJECT = F + "projectLimitNear"
PRESERVE = F + "preserveLimitAt___redArg"
OBSERVE = F + "observeLimit"
GLOBAL = F + "preserveLimit___lam__0"
REFLECT = F + "reflectLimit___redArg___lam__0"
REALIZE = F + "realizeLimit___redArg___lam__0"
NORMALIZE = F + "normalizeCarrierFamily___lam__2"
EXEC, CANONICAL, TERM, ENV = R + "executeAt", R + "executeReal", C + "termReal", R + "environment"
NUM_TERMS, NUM_APPROX, NUM_LAW, LAW, MONO, GIVEN = (
    "l_family_terms", "l_family_approximation", "l_family_numeric_law",
    "l_family_received_cauchy", "l_family_received_monotone", "l_family_candidate_converges")
CARRIER_TERMS, CARRIER_LAW = "l_family_carrier_terms", "l_family_carrier_law"


def require(value, expected, message):
    if value.retained() != frozenset({expected}):
        raise ValueError(message + ": " + expected)


def family():
    return Value(fields={0: tag("producer"), 1: tag("term-coherence"), 2: tag("modulus"),
                         3: Value(function=MONO), 4: Value(function=LAW)})


def candidate(real="candidate-real"):
    return Value(fields={0: tag(real), 1: tag("threshold"), 2: Value(function=GIVEN)})


def raw_archive(side):
    return Value(fields={0: Value(fields={0: tag(side + "-journal")}), 1: tag(side + "-reachability")})


class FamilyAnalysis(Analysis):
    def __init__(self, *args, watched="", mode="", **kwargs):
        super().__init__(*args, target="", capture=True, **kwargs)
        self.watched, self.mode = watched, mode

    def run(self, name, args):
        count = int(name == self.watched)
        if name == "l_family_nat_sub":
            if args[0].number is None or args[1].number is None:
                raise ValueError("Owned coordinate alignment lost numeric scale")
            return Value(tags=args[0].retained() | args[1].retained(),
                         number=max(0, args[0].number - args[1].number)), count, count
        if name == SOURCE_PROGRAM and self.mode != "native-readout":
            require(args[0], "producer", "Realized law changed owned source program")
            return tag("source-program"), count, count
        if name == READOUT and self.mode != "native-readout":
            require(args[0], "source-program", "Realized law lost source readout program")
            side = "left" if args[2].retained() == frozenset({"received-left-execution"}) else "right"
            require(args[2], "received-" + side + "-execution", "Realized law lost owned execution")
            require(args[1].fields.get(0, Value()), side + "-index", "Realized action read changed request")
            require(args[1].fields.get(1, Value()), side + "-precision", "Realized action read changed precision")
            extra = int(self.watched == "read-" + side)
            return Value(fields={2: Value(number=2 if side == "left" else 3,
                                          tags=frozenset({side + "-owned-scale"}))}), count + extra, count + extra
        if name == NUM_TERMS:
            require(args[0], "term-index", "Producer lost requested term")
            return Value(fields={0: Value(function=NUM_APPROX)}), count, count
        if name == NUM_APPROX:
            require(args[0], "term-precision", "Producer lost requested precision")
            return tag("calculated-code"), count, count
        if name == NUM_LAW:
            for slot, expected in enumerate(("accuracy", "left-index", "right-index", "left-precision",
                                             "right-precision", "left-index-extension", "right-index-extension",
                                             "left-precision-extension", "right-precision-extension")):
                require(args[slot], expected, "Realized numerical law lost a received argument")
            return Value(fields={0: Value(fields={0: Value(number=10, tags=frozenset({"numeric-common"})),
                                                 1: Value(number=8), 2: Value(number=7)}),
                                 1: Value(number=4, tags=frozenset({"numeric-precision-slack"}))}), count, count
        if name == GIVEN:
            for slot, expected in enumerate(("accuracy", "term-index", "term-precision", "candidate-precision",
                                             "term-current", "candidate-current", "term-step", "candidate-step",
                                             "index-extension", "term-extension", "candidate-extension")):
                require(args[slot], expected, "Preservation lost received current resources/budget")
            return tag("received-near"), count, count
        if name == MONO:
            for slot, expected in enumerate(("accuracy", "candidate-precision", "candidate-extension")):
                require(args[slot], expected, "Route A lost the diagonal modulus extension")
            return tag("diagonal-extension"), count, count
        if name == LAW:
            for slot, expected in ((0, "accuracy"), (1, "term-journal"), (2, "candidate-journal"),
                                   (4, "diagonal-request"), (5, "index-extension"), (6, "diagonal-extension"),
                                   (7, "term-extension"), (8, "candidate-extension"),
                                   (9, "term-source-execution"), (10, "limit-source-execution")):
                require(args[slot], expected, "Route A lost the exact original Cauchy argument")
            require(args[3].fields.get(0, Value()), "term-index", "Route A changed source term")
            require(args[3].fields.get(1, Value()), "term-precision", "Route A changed source precision")
            return tag("direct-near"), count, count
        if name == TERM:
            index = args[3].retained()
            if index in (frozenset({"left-index"}), frozenset({"right-index"})):
                side = "left" if "left-index" in index else "right"
                return tag(side + "-real"), count, count
            require(args[3], "term-index", "Observation changed term index")
            return tag("term-real"), count, count
        if name == ENV:
            real = args[2]
            for side in ("left", "right"):
                if real.retained() == frozenset({side + "-real"}):
                    return Value(fields={0: tag(side + "-initial")}), count, count
            return Value(fields={0: tag("candidate-current")}), count, count
        if name == C + "termEnvironment":
            if args[3].number != 0:
                raise ValueError("Global preservation changed declared initial term context")
            return Value(fields={0: tag("term-current")}), count, count
        if name == EXEC:
            role = "term" if args[2].retained() == frozenset({"term-real"}) else "candidate"
            require(args[3], role + "-current", "Observation reset current archive")
            require(args[4], role + "-precision", "Observation changed requested precision")
            extra = int(self.watched == "execute-" + role)
            return tag(role + "-step"), count + extra, count + extra
        if name == CANONICAL:
            side = "left" if args[2].retained() == frozenset({"left-real"}) else "right"
            require(args[4-1], side + "-precision", "Numerical family changed canonical response")
            extra = int(self.watched == "canonical-" + side)
            return tag(side + "-canonical-execution"), count + extra, count + extra
        if name == C + "termsCauchy___redArg":
            for slot, expected in ((1, "accuracy"), (2, "left-index"), (3, "right-index"),
                                   (4, "left-precision"), (5, "right-precision"),
                                   (6, "left-initial"), (7, "right-initial"),
                                   (8, "left-canonical-execution"), (9, "right-canonical-execution")):
                require(args[slot], expected, "Readout Cauchy lost its explicitly canonical executions")
            return tag("canonical-near"), count, count
        if name == U + "authoritative":
            # Boundary returns the actual rebuilt family, so its closure can
            # be inspected and invoked separately through termLimitNear.
            return args[2], count, count
        if name == "l_family_numeric_limit":
            for slot, expected in enumerate(("accuracy", "term-index", "term-precision", "candidate-precision",
                                             "index-extension", "term-extension", "candidate-extension")):
                require(args[slot], expected, "Numerical limit lost exact extensions")
            return tag("numeric-limit-near"), count, count
        if name == CARRIER_TERMS:
            side = "left" if args[0].retained() == frozenset({"left-index"}) else "right"
            return Value(fields={1: Value(function="l_family_" + side + "_modulus"),
                                 2: Value(function="l_family_" + side + "_monotone")}), count, count
        for side in ("left", "right"):
            if name == "l_family_" + side + "_modulus":
                require(args[0], side + "-precision", "Carrier normalization changed own modulus input")
                return tag(side + "-own-response"), count, count
            if name == "l_family_" + side + "_monotone":
                for slot, expected in enumerate(("accuracy", side + "-precision", side + "-precision-extension")):
                    require(args[slot], expected, "Carrier normalization changed monotone extension")
                return tag(side + "-own-extension"), count, count
        if name == CARRIER_LAW:
            for slot, expected in enumerate(("accuracy", "left-index", "right-index", "left-own-response",
                                             "right-own-response", "left-index-extension", "right-index-extension",
                                             "left-own-extension", "right-own-extension")):
                require(args[slot], expected, "Carrier law lost normalized own-modulus replies")
            return tag("carrier-near"), count, count
        value, low, high = super().run(name, args)
        return value, low + count, high + count


def run(functions, params, entry, args, target="", expected=0, mode=""):
    value, low, high = FamilyAnalysis(functions, params, base["shared"]["reachable"], watched=target, mode=mode).run(entry, args)
    if (low, high) != (expected, expected):
        raise ValueError(f"Family multiplicity {target}: expected {expected}, found [{low},{high}]")
    return value


def numerical_args():
    return [tag("producer"), Value(function=NUM_LAW)] + [tag(x) for x in
        ("accuracy", "left-journal", "right-journal")] + [
        Value(fields={0: tag("left-index"), 1: tag("left-precision")}),
        Value(fields={0: tag("right-index"), 1: tag("right-precision")})] + [
        tag(x) for x in ("left-index-extension", "right-index-extension", "left-precision-extension",
                        "right-precision-extension", "received-left-execution", "received-right-execution")]


def current_args():
    return [candidate()] + [tag(x) for x in ("accuracy", "term-index", "term-precision", "candidate-precision",
                                            "term-current", "candidate-current", "term-step", "candidate-step",
                                            "index-extension", "term-extension", "candidate-extension")]


def check_realization(functions, params):
    reads = [m.start() for m in re.finditer(re.escape(READOUT) + r'\(', functions[REALIZED])]
    law = functions[REALIZED].find("lean_apply_9(")
    if len(reads) != 2 or not reads[0] < reads[1] < law:
        raise ValueError("Realized action reads must precede numerical law")
    request = Value(fields={0: tag("term-index"), 1: tag("term-precision")})
    for target in (NUM_TERMS, NUM_APPROX):
        require(run(functions, params, PRODUCER, [Value(function=NUM_TERMS), request], target, 1),
                "calculated-code", "Producer did not calculate received term/precision")
    numeric = Value(fields={0: tag("only-terms"), 1: tag("modulus"), 2: tag("monotone"), 3: tag("cauchy")})
    produced = run(functions, params, F + "realizeFamily___redArg", [numeric])
    calculator = produced.fields[0]
    if calculator.fixed != 1 or calculator.retained() != frozenset({"only-terms"}):
        raise ValueError("Realization calculator captures more than declared term function")
    for target, expected in ((NUM_LAW, 1), (READOUT, 2), ("read-left", 1), ("read-right", 1), (ALIGN, 1)):
        aligned = run(functions, params, REALIZED, numerical_args(), target, expected)
        if (aligned.fields[0].fields[0].retained() != frozenset({"numeric-common"}) or
                aligned.fields[1].retained() != frozenset({"numeric-precision-slack"})):
            raise ValueError("Realized alignment padded common scale or precision slack")
        for slot, side in ((1, "left"), (2, "right")):
            lift = aligned.fields[0].fields[slot]
            # Sharing branches join the same coordinate; the shared analyser
            # keeps its origins but intentionally drops concrete numbers.
            # Actual subtraction inputs are checked in the local primitive.
            if lift.retained() != frozenset({"numeric-common", side + "-owned-scale"}):
                raise ValueError("Realized alignment lost owned output coordinate")


def check_native_readout(functions, params):
    program = run(functions, params, SOURCE_PROGRAM, [tag("producer")], mode="native-readout")
    searched = Value(fields={1: tag("search-decoy")})
    acted = Value(fields={0: searched, 1: tag("action-decoy")})
    executed = Value(fields={0: Value(fields={0: Value(fields={0: acted})}),
                             1: tag("owned-stored-code")})
    value = run(functions, params, READOUT, [program, tag("request"), executed], mode="native-readout")
    require(value, "owned-stored-code", "Source readout did not consume exact stored action")


def check_direct(functions, params):
    production = Value(fields={0: Value(fields={0: tag("diagonal-request")}), 1: tag("limit-source-execution")})
    args = [family()] + [tag(x) for x in ("accuracy", "term-index", "term-precision", "candidate-precision")] + [
        raw_archive("term"), raw_archive("candidate"), tag("term-source-execution"), Value(fields={1: production})] + [
        tag(x) for x in ("index-extension", "term-extension", "candidate-extension")]
    for target, expected in ((LAW, 1), (MONO, 1), (EXEC, 0), (CANONICAL, 0)):
        require(run(functions, params, DIRECT, args, target, expected), "direct-near", "Route A lost original law")


def check_preservation(functions, params):
    args = current_args()
    for target, expected in ((GIVEN, 1), (EXEC, 0), (CANONICAL, 0)):
        require(run(functions, params, PRESERVE, args, target, expected),
                "received-near", "Rich preservation reconstructed the Near")
    require(run(functions, params, PROJECT, [Value()] * 12 + [tag("owned-near")]),
            "owned-near", "Endpoint projection did not reuse received Near")
    observed_args = [Value(), Value(), family(), args[0]] + args[1:7] + args[9:]
    for target, expected in (("execute-term", 1), ("execute-candidate", 1), (GIVEN, 1)):
        value = run(functions, params, OBSERVE, observed_args, target, expected)
        for slot, expected_tag in ((1, "term-step"), (2, "candidate-step"), (3, "received-near"), (4, "received-near")):
            require(value.fields[slot], expected_tag, "Observation lost shared stored resource")
        require(value.fields[0].fields[0], "term-current", "Observation lost incoming term archive")
        require(value.fields[0].fields[1], "candidate-current", "Observation lost incoming candidate archive")
    global_args = [Value(), Value(), family(), tag("candidate-real"), candidate()] + args[1:5] + args[9:]
    for target, expected in ((OBSERVE, 1), ("execute-term", 1), ("execute-candidate", 1), (GIVEN, 1)):
        require(run(functions, params, GLOBAL, global_args, target, expected), "received-near", "Global view bypassed shared observation")


def check_reflection(functions, params):
    # Reuse the actual compiled callback for each of the five constructors
    # and a recursive composition. Native Step values are opaque boundaries;
    # currentReadout proof formation is Lean-only, not observable C code.
    for constructor in ("leaf", "certified", "add", "neg", "mul", "recursive"):
        args = [Value(function="l_family_numeric_limit")] + current_args()[1:]
        args[6], args[7] = tag(constructor + "-term-step"), tag(constructor + "-candidate-step")
        for entry in (REFLECT, REALIZE):
            for target, expected in (("l_family_numeric_limit", 1), (EXEC, 0), (CANONICAL, 0)):
                require(run(functions, params, entry, args, target, expected),
                        "numeric-limit-near", "Reflection replaced received Steps by a new execution")


def check_numerical_route(functions, params):
    args = [Value(), Value(), family()] + [tag(x) for x in
        ("accuracy", "left-index", "right-index", "left-precision", "right-precision",
         "left-index-extension", "right-index-extension", "left-precision-extension", "right-precision-extension")]
    for target in ("canonical-left", "canonical-right", C + "termsCauchy___redArg"):
        require(run(functions, params, NUMERICAL, args, target, 1), "canonical-near", "Numerical Cauchy did not execute canonical terms")
    rebuilt = run(functions, params, F + "returnedAuthoritative", [Value(), Value(), family()])
    closure = rebuilt.fields[4]
    if closure.function != REALIZED + "___boxed" or closure.fixed != 2:
        raise ValueError("Returned authoritative law is not the reconstructed Cauchy closure")
    numeric = closure.fields[1]
    if numeric.function != NUMERICAL or numeric.fixed != 3:
        raise ValueError("Returned authoritative law bypassed numerical readout Cauchy")


def check_carrier(functions, params):
    args = [Value(function=CARRIER_TERMS), Value(function=CARRIER_LAW)] + [tag(x) for x in
        ("accuracy", "left-index", "right-index", "left-precision", "right-precision",
         "left-index-extension", "right-index-extension", "left-precision-extension", "right-precision-extension")]
    for target in (CARRIER_LAW, "l_family_left_modulus", "l_family_right_modulus",
                   "l_family_left_monotone", "l_family_right_monotone"):
        require(run(functions, params, NORMALIZE, args, target, 1), "carrier-near", "Carrier lost normalized result")


def mutate(functions, entry, callee, occurrence, slot, replacement):
    copied = dict(functions)
    matches = list(re.finditer(re.escape(callee) + r'\(([^;]+)\)', copied[entry]))
    if occurrence >= len(matches):
        raise ValueError("Family mutation site changed: " + callee)
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
            raise ValueError(f"Wrong rejection for {label}: {error}") from error
        print("REAL_FAMILY_TRANSPORT_MUTATION_REJECTED " + label)
        return
    raise ValueError("Family mutation accepted: " + label)


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    functions = {}
    for text in texts:
        functions.update(base["shared"]["bodies"](text))
        base["add_static_objects"](functions, text)
    functions = {n: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'lean_box(\1)',
                          re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', b)).replace("lean_nat_sub(", "l_family_nat_sub(")
                 for n, b in functions.items()}
    params = base["parameters"](texts)
    for n, arity in ((PRODUCER, 2), (REALIZED, 13), (ALIGN, 3), (DIRECT, 12), (PROJECT, 13),
                     (PRESERVE, 12), (OBSERVE, 13), (GLOBAL, 12), (REFLECT, 12), (REALIZE, 12),
                     (NUMERICAL, 12), (NORMALIZE, 11)):
        if len(params.get(n, [])) != arity:
            raise ValueError("Missing pinned transport definition/arity: " + n)
    checks = (check_realization, check_native_readout, check_direct, check_preservation, check_reflection, check_numerical_route, check_carrier)
    for check in checks:
        check(functions, params)
        print("REAL_FAMILY_TRANSPORT_ROUTE_OK " + check.__name__)
    for occurrence in (0, 1):
        broken = mutate(functions, REALIZED, READOUT, occurrence, 2, "lean_box(0)")
        reject(check_realization, broken, params, "replace-owned-action-" + str(occurrence), "Realized law lost owned execution")
    for slot in (0, 1):
        broken = mutate(functions, REALIZED, ALIGN, 0, slot,
                        re.findall(re.escape(ALIGN) + r'\(([^;]+)\)', functions[REALIZED])[0].split(',')[1 - slot].strip())
        reject(check_realization, broken, params, "swap-owned-coordinate-" + str(slot), "Realized alignment lost")
    for occurrence in (0, 1):
        broken = mutate(functions, ALIGN, "l_family_nat_sub", occurrence, 1, "lean_box(0)")
        reject(check_realization, broken, params, "discard-owned-scale-" + str(occurrence), "Realized alignment lost")
    broken = dict(functions)
    law_line = next(line for line in functions[REALIZED].splitlines() if " = lean_apply_9(" in line)
    body = functions[REALIZED].replace(law_line, "", 1)
    first_read_line = next(line for line in body.splitlines() if " = " + READOUT + "(" in line)
    broken[REALIZED] = body.replace(first_read_line, law_line + "\n" + first_read_line, 1)
    reject(check_realization, broken, params, "numeric-law-before-owned-reads", "Realized action reads")
    broken = mutate(functions, ALIGN, "lean_ctor_get", 1, 1, "0")
    reject(check_realization, broken, params, "replace-precision-slack", "Realized alignment padded")
    for slot in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11):
        broken = mutate(functions, DIRECT, "lean_apply_11", 0, slot, "lean_box(0)")
        reject(check_direct, broken, params, "route-A-lost-" + str(slot), "Route A")
    for occurrence in (0, 1):
        broken = mutate(functions, OBSERVE, EXEC, occurrence, 3, "lean_box(0)")
        reject(check_preservation, broken, params, "reset-observation-" + str(occurrence), "Observation reset")
    for slot in (7, 8):
        broken = mutate(functions, PRESERVE, "lean_apply_11", 0, slot, "lean_box(0)")
        reject(check_preservation, broken, params, "replace-current-Step-" + str(slot), "Preservation lost")
    for entry in (REFLECT, REALIZE):
        broken = mutate(functions, entry, "lean_apply_7", 0, 7, "lean_box(0)")
        reject(check_reflection, broken, params, "discard-convergence-budget-" + entry, "Numerical limit")
    for occurrence in (0, 1):
        broken = mutate(functions, NUMERICAL, CANONICAL, occurrence, 3, "lean_box(0)")
        reject(check_numerical_route, broken, params, "wrong-canonical-response-" + str(occurrence), "Numerical family")
    for occurrence in (0, 1):
        broken = mutate(functions, NORMALIZE, "lean_apply_3", occurrence, 3, "lean_box(0)")
        reject(check_carrier, broken, params, "discard-own-monotone-" + str(occurrence), "Carrier normalization")
    # A second valid execution, even with ignored result, must count twice.
    for entry, check, expected in ((REALIZED, check_realization, "Family multiplicity"),
                                    (OBSERVE, check_preservation, "Family multiplicity"),
                                    (PRESERVE, check_preservation, "Family multiplicity"),
                                    (DIRECT, check_direct, "Family multiplicity")):
        broken, changed = dict(functions), dict(params)
        alias = "l_family_original_" + str(len(changed))
        broken[alias], changed[alias] = functions[entry], params[entry]
        call = "lean_object* ignored; ignored = " + alias + "(" + ",".join(params[entry]) + ");"
        broken[entry] = functions[entry].replace("{", "{" + call, 1)
        reject(check, broken, changed, "duplicate-valid-" + entry, expected)
    # Extra native executions in a proof-erased bridge must also be rejected.
    for entry in (PROJECT, REFLECT, REALIZE):
        broken = dict(functions)
        p = params[entry]
        call = "lean_object* ignored; ignored = " + EXEC + "(lean_box(0),lean_box(0),lean_box(0),lean_box(0),lean_box(0));"
        broken[entry] = functions[entry].replace("{", "{" + call, 1)
        check = check_preservation if entry == PROJECT else check_reflection
        reject(check, broken, params, "extra-execution-" + entry, "Observation reset")
    print("REAL_FAMILY_TRANSPORT_CODEGEN_OK: two owned stored action reads before numeric law; exact unpadded coordinate alignment; Prop endpoint/ownership formation is Lean-only; no compiled replay in current-Step bridges; explicit canonical numerical family route; callbacks/native execution remain boundaries")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError) as error:
        print("REAL_FAMILY_TRANSPORT_CODEGEN_FAILED " + str(error), file=sys.stderr)
        raise SystemExit(1)
