#!/usr/bin/env python3
"""Bounded C argument-flow checks for executable regular-name routes.

Exact defining symbols, callback arguments, shared selected data and producer
multiplicity are checked. Dyadic kernels and the existing comparison/runtime
engines are scope boundaries, covered by their existing gates. No C claim is
made about Nonempty, class existence, erased laws, arbitrary callbacks, global
C semantics, execution cost or physical memory.
"""
from pathlib import Path
import json
import re
import runpy
import sys

sys.dont_write_bytecode = True
from unified_codegen_analysis import Analysis, Value, parameters, add_static_objects

ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))
P = "lp_relational_x2dperimeter_RelationalPerimeter_Constitution_Reals_"
N, R = P + "RegularDyadicName_", P + "RelationalRealCauchyReference_"


def atom(value):
    return Value(tags=frozenset({json.dumps(value, separators=(",", ":"))}))


def expression(value):
    if value.number is not None:
        return value.number
    if len(value.tags) != 1:
        raise ValueError("Lost exact scalar expression")
    return json.loads(next(iter(value.tags)))


def expect(value, wanted):
    if isinstance(wanted, dict):
        for slot, expected in wanted.items():
            if slot not in value.fields:
                raise ValueError("Lost selected result field: " + str(slot))
            expect(value.fields[slot], expected)
        return
    if expression(value) != wanted:
        raise ValueError("Argument/readout changed: " + repr((expression(value), wanted)))


def name(function):
    return Value(fields={0: Value(function=function)})


class Routes(Analysis):
    def __init__(self, functions, params, watched=""):
        super().__init__(functions, params, shared["reachable"], target="", capture=True)
        self.watched = watched

    def run(self, symbol, args):
        count = int(symbol == self.watched)
        if symbol == "l_reference_nat":
            return atom(expression(args[0])), count, count
        if symbol == "l_reference_add":
            a, b = map(expression, args)
            return atom(a + b if isinstance(a, int) and isinstance(b, int) else ["+", a, b]), count, count
        if symbol == "l_reference_direction":
            return args[0].fields[2], count, count
        if symbol in ("l_reference_left", "l_reference_right", "l_reference_source"):
            return atom([symbol.removeprefix("l_reference_"), expression(args[0])]), count, count
        if symbol == "l_reference_module":
            return atom(["module", expression(args[0])]), count, count
        if symbol == "l_reference_term":
            expect(args[0], ["module", "p"])
            return name("l_reference_term_read"), count, count
        if symbol == "l_reference_term_read":
            return atom(["term", ["module", "p"], expression(args[0])]), count, count
        if symbol == P + "probeAmplitude":
            return atom(["probe", expression(args[0])]), count, count
        if symbol in (P + "SignedDyadicCode_add", P + "SignedDyadicCode_mul", P + "SignedDyadicCode_neg"):
            return atom([symbol.rsplit("_", 1)[1], *map(expression, args)]), count, count
        if symbol in (P + "DyadicReciprocal_sourcePrecision", P + "DyadicReciprocal_roundingPrecision"):
            return atom([symbol.rsplit("_", 1)[1], *map(expression, args)]), count, count
        if symbol == P + "DyadicReciprocal_computeReciprocal___redArg":
            return Value(fields={1: atom(["reciprocal", *map(expression, args)])}), count, count
        if symbol == P + "DyadicDensity_bisect___redArg":
            expect(args[0], ["left", "response"])
            expect(args[1], ["right", "response"])
            expect(args[2], "received-separation")
            return Value(fields={0: atom("selected-midpoint"), 1: atom("left-margin"), 2: atom("right-margin")}), count, count
        if symbol == P + "DyadicDensity_naturalBounds":
            expect(args[0], ["source", 2])
            return Value(fields={0: atom("selected-upper"), 1: atom("selected-lower"),
                                 2: atom("upper-margin"), 3: atom("lower-margin")}), count, count
        if symbol in (P + "DyadicDensity_naturalCode", P + "DyadicDensity_negativeNaturalCode"):
            return atom([symbol.rsplit("_", 1)[1], expression(args[0])]), count, count
        if symbol == N + "constantName":
            return Value(fields={0: Value(function="l_reference_constant", fixed=1, fields={0: args[0]})}), count, count
        if symbol == "l_reference_constant":
            return atom(["constant", *map(expression, args)]), count, count
        if symbol == P + "strengthenSeparation___redArg":
            return atom(["margin", *map(expression, args)]), count, count
        if symbol == R + "regularCharacterization":
            for argument, expected in zip(args, ("P", "depth")):
                expect(argument, expected)
            return Value(fields={0: name("l_reference_forward"), 1: name("l_reference_backward")}), count, count
        if symbol in ("l_reference_forward", "l_reference_backward"):
            return atom([symbol.removeprefix("l_reference_"), expression(args[0])]), count, count
        if symbol == P + "RelationalRealAddition_ofCarrier":
            for argument, expected in zip(args, ("P", "depth", ["backward", "received-name"])):
                expect(argument, expected)
            return atom("produced-runtime"), count, count
        result, low, high = super().run(symbol, args)
        return result, low + count, high + count


def run_route(functions, params, entry, args, expected, counts):
    for symbol, count in counts.items():
        analysis = Routes(functions, params, symbol)
        result, low, high = analysis.run(entry, args)
        expect(result, expected)
        if (low, high) != (count, count):
            raise ValueError("Producer/callback multiplicity changed: " + symbol + repr((low, high)))


def checks(functions, params):
    a, b, p = name("l_reference_left"), name("l_reference_right"), atom("p")
    add, mul, neg = (P + "SignedDyadicCode_" + operation for operation in ("add", "mul", "neg"))
    run_route(functions, params, N + "negName___lam__0", [a, p], ["neg", ["left", "p"]],
              {neg: 1, "l_reference_left": 1})
    run_route(functions, params, N + "addName___lam__0", [a, b, p],
              ["add", ["left", ["+", "p", 1]], ["right", ["+", "p", 1]]],
              {add: 1, "l_reference_left": 1, "l_reference_right": 1})
    run_route(functions, params, N + "mulName___lam__0", [a, b, p],
              ["mul", ["left", ["+", ["+", "p", 1], ["probe", ["right", 0]]]],
               ["right", ["+", ["+", "p", 1], ["probe", ["left", 0]]]]],
              {mul: 1, "l_reference_left": 2, "l_reference_right": 2, P + "probeAmplitude": 2})
    family = Value(fields={0: Value(function="l_reference_term"), 1: Value(function="l_reference_module")})
    run_route(functions, params, N + "diagonalName___lam__0", [family, p],
              ["term", ["module", "p"], "p"],
              {"l_reference_module": 1, "l_reference_term": 1, "l_reference_term_read": 1})
    domain = Value(fields={0: atom("away"), 2: atom("direction")})
    run_route(functions, params, N + "reciprocalName___lam__0", [domain, name("l_reference_source"), p],
              ["reciprocal", "direction", ["source", ["sourcePrecision", "away", "p"]],
               ["roundingPrecision", "p"]],
              {"l_reference_source": 1, P + "DyadicReciprocal_computeReciprocal___redArg": 1,
               P + "DyadicReciprocal_sourcePrecision": 1, P + "DyadicReciprocal_roundingPrecision": 1})
    run_route(functions, params, R + "carrierToReferenceName", [atom("P"), atom("depth"), atom("received-carrier")],
              ["forward", "received-carrier"], {R + "regularCharacterization": 1, "l_reference_forward": 1})
    run_route(functions, params, R + "runtimeOfReferenceName", [atom("P"), atom("depth"), atom("received-name")],
              "produced-runtime", {R + "referenceNameToCarrier": 1, R + "regularCharacterization": 1,
              "l_reference_backward": 1, P + "RelationalRealAddition_ofCarrier": 1})
    accuracy, response = ["+", "accuracy", 3], ["+", "accuracy", 6]
    left, right, middle = ["left", response], ["right", response], ["constant", "selected-midpoint", response]
    origin = Value(fields={0: atom("accuracy"), 1: atom("response"), 2: atom("beyond"), 3: atom("received-separation")})
    run_route(functions, params, N + "nameDensity", [a, b, origin],
              {0: "selected-midpoint", 1: {0: accuracy, 1: response, 3: ["margin", ["+", "accuracy", 1], left, middle]},
               2: {0: accuracy, 1: response, 3: ["margin", ["+", "accuracy", 1], middle, right]}},
              {P + "DyadicDensity_bisect___redArg": 1, "l_reference_left": 2, "l_reference_right": 2,
               N + "constantName": 1, "l_reference_constant": 1, P + "strengthenSeparation___redArg": 2})
    lower = ["constant", ["negativeNaturalCode", "selected-lower"], 5]
    upper = ["constant", ["naturalCode", "selected-upper"], 5]
    run_route(functions, params, N + "nameNaturalBounds", [name("l_reference_source")],
              {0: "selected-lower", 1: "selected-upper", 2: {0: 2, 1: 5, 3: ["margin", 0, lower, ["source", 5]]},
               3: {0: 2, 1: 5, 3: ["margin", 0, ["source", 5], upper]}},
              {P + "DyadicDensity_naturalBounds": 1, "l_reference_source": 2,
               N + "constantName": 2, "l_reference_constant": 2, P + "strengthenSeparation___redArg": 2})


def decode(functions):
    # Instrument the three exact C primitives while preserving their arguments.
    # Constructor indices are untouched. No source or generated file is edited.
    result = {}
    for symbol, body in functions.items():
        body = re.sub(r"lean_unsigned_to_nat\((\d+)u\)", r"l_reference_nat(\1)", body)
        body = body.replace("lean_nat_add(", "l_reference_add(")
        body = re.sub(r"lean_ctor_get_uint8\((\w+), sizeof\(void\*\)\*2\)", r"l_reference_direction(\1)", body)
        result[symbol] = body
    return result


def reject(check, functions, params, entry, old, new):
    if old not in functions[entry]:
        raise ValueError("Mutation site changed: " + entry)
    altered = dict(functions)
    altered[entry] = altered[entry].replace(old, new, 1)
    try:
        check(altered, params)
    except ValueError as error:
        if str(error).startswith(("Argument/readout changed:", "Producer/callback multiplicity changed:")):
            return
        raise ValueError("Mutation failed for an unrelated reason: " + str(error)) from error
    raise ValueError("Compiled mutation was accepted: " + entry)


def main():
    directory = ROOT / ".lake/build/ir/RelationalPerimeter/Constitution/Reals"
    functions, owners, texts = {}, {}, []
    for path in directory.glob("*.c"):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        definitions = shared["bodies"](text)
        for symbol in definitions:
            owners.setdefault(symbol, set()).add(path.stem)
        functions.update(definitions)
        add_static_objects(functions, text)
    params = parameters(texts)
    for symbol, module in [(N + op + "___lam__0", "RegularDyadicName")
                           for op in ("negName", "addName", "mulName", "diagonalName")] + [
                               (N + "reciprocalName___lam__0", "RegularDyadicNameOrderedField"),
                               (N + "nameDensity", "RegularDyadicNameOrderedField"),
                               (N + "nameNaturalBounds", "RegularDyadicNameOrderedField"),
                               (R + "carrierToReferenceName", "RelationalRealCauchyReference"),
                               (R + "runtimeOfReferenceName", "RelationalRealCauchyReference")]:
        if owners.get(symbol) != {module} or symbol not in params:
            raise ValueError("Missing or foreign compiled definition: " + symbol)
    decoded = decode(functions)
    checks(decoded, params)
    for operation in ("negName", "addName", "mulName", "diagonalName", "reciprocalName"):
        entry = N + operation + "___lam__0"
        shared["absent"](functions, entry, ("RelationalRealAddition_", "carrierToReferenceName", "ofCarrier"))
    mutations = 0
    # Every readout schedule is checked exactly, including crossed probe owners.
    for entry, old, new in (
        (N + "addName___lam__0", "l_reference_nat(1)", "l_reference_nat(2)"),
        (N + "mulName___lam__0", "l_reference_nat(1)", "l_reference_nat(2)"),
        (N + "mulName___lam__0", P + "SignedDyadicCode_mul", P + "SignedDyadicCode_add"),
        (N + "reciprocalName___lam__0", P + "DyadicReciprocal_sourcePrecision", P + "DyadicReciprocal_roundingPrecision"),
        (N + "nameDensity", "l_reference_nat(3)", "l_reference_nat(4)"),
        (N + "nameDensity", "l_reference_nat(6)", "l_reference_nat(7)"),
        (N + "nameNaturalBounds", "l_reference_nat(2)", "l_reference_nat(3)"),
        (N + "nameNaturalBounds", "l_reference_nat(5)", "l_reference_nat(6)"),
    ):
        reject(checks, decoded, params, entry, old, new)
        mutations += 1
    for entry in (N + "negName___lam__0", N + "addName___lam__0", N + "mulName___lam__0",
                  N + "diagonalName___lam__0", N + "reciprocalName___lam__0",
                  R + "carrierToReferenceName", R + "runtimeOfReferenceName"):
        body = decoded[entry]
        call = re.search(r"return (\w+);", body)
        if call is None:
            raise ValueError("Return mutation site changed")
        reject(checks, decoded, params, entry, call.group(0), "return lean_box(0);")
        mutations += 1
    for entry, producer in (
        (N + "addName___lam__0", P + "SignedDyadicCode_add"),
        (N + "mulName___lam__0", P + "SignedDyadicCode_mul"),
        (N + "reciprocalName___lam__0", P + "DyadicReciprocal_computeReciprocal___redArg"),
        (N + "nameDensity", P + "DyadicDensity_bisect___redArg"),
        (N + "nameNaturalBounds", P + "DyadicDensity_naturalBounds"),
        (R + "runtimeOfReferenceName", P + "RelationalRealAddition_ofCarrier"),
    ):
        call = re.search(re.escape(producer) + r"\([^;\n]*\)", decoded[entry])
        if call is None:
            raise ValueError("Duplicate-producer mutation site changed")
        reject(checks, decoded, params, entry, call.group(0), call.group(0) + "; " + call.group(0))
        mutations += 1
    print(f"REGULAR_CAUCHY_REFERENCE_CODEGEN_OK: nine executable argument routes, exact schedules and shared density/bound selections, single numeric/runtime producers; {mutations} rejected mutations; Nonempty/classes/laws excluded")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError) as error:
        print("REGULAR_CAUCHY_REFERENCE_CODEGEN_FAILED: " + str(error), file=sys.stderr)
        raise SystemExit(1)
