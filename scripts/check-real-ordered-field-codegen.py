#!/usr/bin/env python3
"""Bounded pinned-C checks of the finite ordered-field proof producers.

Native arithmetic/comparison execution, coherence and dyadic proofs are exact
named analysis boundaries, checked separately by Lean and the existing runtime
codegen gates. This checks their applications and def-use on the new routes,
not arbitrary callback bodies, physical costs, heap bounds or a C semantics.
No persistent service or new live closure is introduced by these routes.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
base = runpy.run_path(str(ROOT / "scripts/check-real-addition-codegen.py"))
Value, Analysis, PREFIX = base["Value"], base["Analysis"], base["PREFIX"]
tagged = base["tagged"]
FIELD = PREFIX + "RelationalRealOrderedField_"
TRANSLATE, PRODUCT = FIELD + "translateRight", FIELD + "positiveProduct"
MULTIPLY, DIFFERENCE = FIELD + "multiplyRight", FIELD + "positiveDifference"
ACCURACY = FIELD + "positiveProductAccuracy___redArg"
COMPARE = PREFIX + "RelationalRealOrder_produceComparison___redArg"
ENV = PREFIX + "RelationalRealAddition_environment"
COHERENT = PREFIX + "RelationalRealAddition_coherent"
CODE = PREFIX + "HeterogeneousRealRuntime_Step_code___redArg"
NEXT = PREFIX + "HeterogeneousRealRuntime_Step_next___redArg"
NONZERO = PREFIX + "ReciprocalDomain_nonzero___redArg"
BUDGET = PREFIX + "RelationalRealMultiplication_productBudget"
MARGIN = PREFIX + "DyadicReciprocal_NonzeroCode_mulPositive"
STRENGTHEN = PREFIX + "strengthenSeparation___redArg"
ADD_MARGIN = PREFIX + "StrictSeparation_addRight___redArg"
FORWARD = PREFIX + "RelationalRealOrder_ComparisonAttempt_forward___redArg"
TRANSPORT = PREFIX + "RelationalRealOrder_transportOrder"


def require(value, expected, label):
    if value.tags != frozenset({expected}):
        raise ValueError(label + ": " + str(value.tags))


def step(name, **fields):
    return Value(tags=frozenset({name}), fields={int(k): v for k, v in fields.items()})


def order(name, accuracy):
    return Value(tags=frozenset({name}), fields={
        0: tagged(name + "-left-archive"), 1: tagged(name + "-right-archive"),
        2: Value(number=accuracy), 3: Value(number=accuracy + 3), 4: Value(number=0),
        5: Value(fields={0: tagged(name + "-left-step"), 1: tagged(name + "-right-step")})})


def archive(name):
    return Value(tags=frozenset({name}), fields={0: tagged(name + "-left"), 1: tagged(name + "-right")})


def arguments(route):
    if route == TRANSLATE:
        return [Value(), Value(), tagged("a"), tagged("b"), order("origin", 7), tagged("shift"),
                archive("current-left"), archive("current-right")]
    if route == MULTIPLY:
        return [Value(), Value(), tagged("a"), tagged("b"), tagged("c"), order("origin", 7),
                order("factor", 11), tagged("current-negation"), tagged("current-zero"), archive("current-ac")]
    return [Value(), Value(), tagged("a"), tagged("b"), order("positive-left", 7),
            order("positive-right", 11), tagged("current-zero"), archive("current-product")]


class FieldAnalysis(Analysis):
    def __init__(self, *args, route, **kwargs):
        super().__init__(*args, **kwargs)
        self.route = route

    def run(self, name, args):
        count = int(name == self.target)
        if self.route == MULTIPLY:
            result = self.multiply_boundary(name, args)
            if result is not None:
                return result, count, count
        number = re.fullmatch(r'l_field_number_(\d+)', name)
        if number:
            return Value(number=int(number[1])), 0, 0
        if name == "l_field_add":
            if any(v.number is None for v in args):
                raise ValueError("Ordered-field budget ceased to be a resolved natural expression")
            return Value(number=args[0].number + args[1].number), 0, 0
        if name == ENV:
            return args[2], 0, 0
        if name == PREFIX + "RelationalRealAddition_zero":
            return tagged("zero"), 0, 0
        if name == COMPARE:
            if self.route == TRANSLATE:
                require(args[2], "current-left", "Translation resets its left archive")
                require(args[3], "current-right", "Translation resets its right archive")
                for environment, role in ((args[0], "a"), (args[1], "b")):
                    require(environment.fields[0], role, "Translation lost its arithmetic role")
                    require(environment.fields[1], "shift", "Translation lost its shift")
                if (args[4].number, args[5].number) != (9, 12):
                    raise ValueError("Translation lost its exact p+2/p+5 budget")
                left = step("sum-left-step", **{"0": tagged("fine-a"), "1": tagged("shift-left")})
                right = step("sum-right-step", **{"0": tagged("fine-b"), "1": tagged("shift-right")})
            else:
                require(args[2], "current-zero", "Positive product resets its zero archive")
                require(args[3], "current-product", "Positive product resets its product archive")
                require(args[0], "zero", "Positive product lost its oriented zero role")
                for slot, role in ((0, "a"), (1, "b")):
                    require(args[1].fields[slot], role, "Positive product lost its arithmetic role")
                if (args[4].number, args[5].number) != (23, 26):
                    raise ValueError("Positive product lost its two-witness margin/response budget")
                left = tagged("zero-step")
                right = step("product-step", **{
                    "0": tagged("left-probe"), "1": tagged("right-probe"),
                    "2": tagged("left-refinement"), "3": tagged("right-refinement")})
            return Value(tags=frozenset({"one-attempt"}), fields={
                0: args[6], 1: Value(fields={0: left, 1: right}), 2: tagged("actual-classification")}), count, count
        if name == COHERENT:
            role = next(iter(args[2].tags), "")
            if role not in ("a", "b"):
                raise ValueError("Translation coherence lost its received real")
            return Value(function="l_field_coherent_" + role), 0, 0
        if name in ("l_field_coherent_a", "l_field_coherent_b"):
            a = name.endswith("_a")
            require(args[5], "origin-left-step" if a else "origin-right-step",
                    "Translation coherence discarded its received source Step")
            require(args[6], "fine-a" if a else "fine-b",
                    "Translation coherence discarded its actual sum child Step")
            return tagged("left-near" if a else "right-near"), count, count
        if name == CODE:
            return args[-1], 0, 0
        if name == NEXT:
            role = next(iter(args[-1].tags), "")
            return tagged("next-" + role), 0, 0
        if name == STRENGTHEN:
            require(args[1], "fine-a", "Translation margin lost its actual left reply")
            require(args[2], "fine-b", "Translation margin lost its actual right reply")
            return tagged("translated-margin"), 0, 0
        if name == ADD_MARGIN:
            require(args[0], "translated-margin", "Translation did not consume its transported margin")
            require(args[1], "shift-left", "Translation did not consume its actual shift reply")
            return tagged("sum-margin"), 0, 0
        if name == BUDGET:
            require(args[0], "left-probe", "Product budget lost its actual left probe")
            require(args[1], "right-probe", "Product budget lost its actual right probe")
            if args[2].number != 26:
                raise ValueError("Product refinement lost its computed response precision")
            return Value(fields={2: tagged("left-precision"), 3: tagged("right-precision")}), 0, 0
        if name == NONZERO:
            left = args[2].tags == frozenset({"a"})
            role = "left" if left else "right"
            require(args[3].fields.get(0, Value()), "positive-" + role, "Product discarded its directed positive witness")
            require(args[4], "next-" + role + "-probe", "Product certificate resets its probe successor")
            require(args[5], role + "-precision", "Product certificate lost its actual refinement budget")
            require(args[6], role + "-refinement", "Product certificate lost its actual refinement Step")
            return tagged(role + "-certificate"), count, count
        if name == PREFIX + "ReciprocalDomain_away___redArg":
            return Value(number=9), 0, 0
        if name == PREFIX + "ReciprocalDomain_zeroStepSameValue___redArg":
            return tagged("actual-zero-exact"), 0, 0
        if name == MARGIN:
            for slot, expected in ((0, "left-refinement"), (1, "right-refinement"),
                                   (4, "left-certificate"), (5, "right-certificate")):
                require(args[slot], expected, "Product margin does not consume its exact refinements/certificates")
            return tagged("positive-product-margin"), count, count
        if name == PREFIX + "StrictSeparation_ofSameLeft___redArg":
            return args[1], 0, 0
        if name == FORWARD:
            require(args[-1], "one-attempt", "Ordered-field result reclassified another attempt")
            return args[-1], count, count
        return super().run(name, args)

    def multiply_boundary(self, name, args):
        # Compositional scope: the two routes checked above and existing native
        # order transport are boundaries here. Check the new orchestration's
        # exact successor flow, sharing and chronological retained subpackets.
        if name == DIFFERENCE:
            for slot, tag in ((4, "origin"), (5, "current-negation"), (6, "current-zero")):
                require(args[slot], tag, "Monotonicity lost its current difference inputs")
            return tagged("difference-packet")
        if name == FIELD + "PositiveDifference_positive":
            require(args[-1], "difference-packet", "Monotonicity rebuilt its difference")
            return order("difference", 17)
        if name == PRODUCT:
            require(args[4], "difference", "Monotonicity lost its produced positive difference")
            require(args[5], "factor", "Monotonicity discarded its positive factor")
            require(args[6], "next-difference-left-step", "Monotonicity reset the zero successor")
            require(args[7].fields.get(0, Value()), "next-difference-right-step", "Monotonicity reset the difference successor")
            require(args[7].fields.get(1, Value()), "next-factor-right-step", "Monotonicity reset the factor successor")
            return Value(tags=frozenset({"positive-product-packet"}), fields={2: Value(fields={1: Value(fields={
                0: tagged("positive-zero-step"), 1: tagged("positive-product-step")})})})
        if name == FIELD + "PositiveProduct_positive___redArg":
            require(args[-1], "positive-product-packet", "Monotonicity rebuilt its positive product")
            return order("positive-product", 23)
        if name == TRANSLATE:
            require(args[4], "positive-product", "Monotonicity lost its positive-product witness")
            for slot, first in ((6, "next-positive-zero-step"), (7, "next-positive-product-step")):
                require(args[slot].fields.get(0, Value()), first, "Monotonicity reset a translated child")
                require(args[slot].fields.get(1, Value()), "current-ac", "Monotonicity reset the received ac archive")
            product = step("final-product-step", **{
                "0": tagged("final-difference-probe"), "1": tagged("final-factor-probe"),
                "2": step("final-difference-refinement", **{"0": tagged("final-b-refinement")}),
                "3": tagged("final-c-refinement")})
            return Value(tags=frozenset({"translated-packet"}), fields={1: Value(fields={1: Value(fields={
                0: step("translated-left", **{"1": tagged("final-ac-step")}),
                1: step("translated-right", **{"0": product})})})})
        if name == FIELD + "TranslatedOrder_order___redArg":
            require(args[-1], "translated-packet", "Monotonicity rebuilt its translation")
            return tagged("translated-order")
        if name in (FIELD + "differenceProductCancellation", PREFIX + "RelationalRealAddition_zero__add"):
            return tagged("numerical-equivalence")
        if name == NEXT and args[-1].tags == frozenset({"final-difference-probe"}):
            return Value(fields={0: tagged("b-probe-successor"), 1: tagged("negation-probe-successor")})
        if name == BUDGET:
            require(args[0], "final-difference-probe", "Final transport lost its exact difference probe")
            require(args[1], "final-factor-probe", "Final transport lost its exact factor probe")
            return Value(fields={2: Value(number=40), 3: Value(number=50)})
        if name == TRANSPORT:
            require(args[6], "translated-order", "Final transport lost its exact oriented witness")
            require(args[9], "next-final-ac-step", "Final transport reset its exact ac successor")
            require(args[10].fields.get(0, Value()), "next-final-b-refinement", "Final transport reset its exact b successor")
            require(args[10].fields.get(1, Value()), "next-final-c-refinement", "Final transport reset its exact c successor")
            return tagged("transported-packet")
        return None


def run(functions, params, route, target="", expected=0, entry=None, args=None):
    value, low, high = FieldAnalysis(functions, params, base["shared"]["reachable"],
        target=target, capture=True, route=route).run(entry or route, args or arguments(route))
    if (low, high) != (expected, expected):
        raise ValueError(f"Ordered-field multiplicity {target}: expected {expected}, found [{low},{high}]")
    return value


def check(functions, params, route):
    value = run(functions, params, route, COMPARE, 1)
    expected = ((0, "origin"), (1, "one-attempt"), (2, "left-near"), (3, "right-near"), (4, "sum-margin")) \
        if route == TRANSLATE else ((0, "positive-left"), (1, "positive-right"), (2, "one-attempt"),
                                   (3, "left-certificate"), (4, "right-certificate"), (5, "positive-product-margin"))
    for slot, tag in expected:
        require(value.fields.get(slot, Value()), tag, "Ordered-field packet lost a received/produced resource")
    return value


def check_monotonicity(functions, params):
    for target in (DIFFERENCE, PRODUCT, TRANSLATE, TRANSPORT):
        value = run(functions, params, MULTIPLY, target, 1)
        for slot, tag in enumerate(("difference-packet", "positive-product-packet", "translated-packet", "transported-packet")):
            require(value.fields.get(slot, Value()), tag, "Monotonicity lost its chronological subpacket")


def mutate_call(functions, symbol, callee, index, replacement):
    result = dict(functions)
    pattern = re.escape(callee) + r'\(([^;]+)\)'
    def edit(match):
        args = match[1].split(", ")
        args[index] = replacement
        return callee + "(" + ", ".join(args) + ")"
    result[symbol], count = re.subn(pattern, edit, result[symbol])
    if count != 1:
        raise ValueError("Ordered-field mutation site changed: " + callee)
    return result


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    functions = {}
    for source in texts:
        functions.update(base["shared"]["bodies"](source))
        base["add_static_objects"](functions, source)
    params = base["parameters"](texts)
    functions = {name: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'l_field_number_\1()',
                            body.replace("lean_nat_add(", "l_field_add(")) for name, body in functions.items()}
    for name, arity in ((TRANSLATE, 8), (PRODUCT, 8), (MULTIPLY, 10), (ACCURACY, 2), (COMPARE, 7), (NONZERO, 7)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact ordered-field C definition/arity: " + name)
    for route in (TRANSLATE, PRODUCT):
        check(functions, params, route)
    for target in ("l_field_coherent_a", "l_field_coherent_b"):
        run(functions, params, TRANSLATE, target, 1)
    run(functions, params, PRODUCT, NONZERO, 2)
    run(functions, params, PRODUCT, MARGIN, 1)
    check_monotonicity(functions, params)
    # The extraction routes must consume the stored attempt, not run it again.
    for route, entry, args in (
        (TRANSLATE, FIELD + "TranslatedOrder_order___redArg",
         [arguments(TRANSLATE)[4], arguments(TRANSLATE)[6], arguments(TRANSLATE)[7], check(functions, params, TRANSLATE)]),
        (PRODUCT, FIELD + "PositiveProduct_positive___redArg",
         arguments(PRODUCT)[4:] + [check(functions, params, PRODUCT)])):
        run(functions, params, route, FORWARD, 1, entry=entry, args=args)
        run(functions, params, route, COMPARE, 0, entry=entry, args=args)
    mutations = []
    for route, slots in ((TRANSLATE, (2, 3)), (PRODUCT, (2, 3))):
        for slot in slots:
            prefix = "Translation resets" if route == TRANSLATE else "Positive product resets"
            mutations.append((route, mutate_call(functions, route, COMPARE, slot, "lean_box(0)"), "reset-archive", prefix))
    for route, literal in ((TRANSLATE, "2"), (TRANSLATE, "5"), (PRODUCT, "3"), (ACCURACY, "2"), (ACCURACY, "1")):
        broken = dict(functions)
        broken[route] = broken[route].replace("l_field_number_" + literal + "()", "l_field_number_0()")
        prefix = "Translation lost its exact" if route == TRANSLATE else "Positive product lost its two-witness"
        mutations.append((TRANSLATE if route == TRANSLATE else PRODUCT, broken, "underbudget-" + literal, prefix))
    for slot in (3, 4, 5, 6):
        # There are exactly two Nonzero calls: mutate the first received resource.
        broken = dict(functions)
        match = re.search(re.escape(NONZERO) + r'\(([^;]+)\)', broken[PRODUCT])
        if match is None:
            raise ValueError("Missing positive witness mutation site")
        args = match[1].split(", ")
        args[slot] = "lean_box(0)"
        broken[PRODUCT] = broken[PRODUCT].replace(match[0], NONZERO + "(" + ", ".join(args) + ")", 1)
        prefix = {3: "Product discarded its directed", 4: "Product certificate resets",
                  5: "Product certificate lost its actual refinement budget", 6: "Product certificate lost its actual refinement Step"}[slot]
        mutations.append((PRODUCT, broken, "discard-positive-resource-" + str(slot), prefix))
    for route, slot in ((TRANSLATE, 0), (TRANSLATE, 1), (TRANSLATE, 2), (TRANSLATE, 3), (TRANSLATE, 4),
                        (PRODUCT, 0), (PRODUCT, 1), (PRODUCT, 2), (PRODUCT, 3), (PRODUCT, 4), (PRODUCT, 5)):
        broken = dict(functions)
        # Only mutate the final result constructors (both reuse/allocation
        # branches), not an earlier Real AST or positivity wrapper constructor.
        final_slot = 4 if route == TRANSLATE else 5
        packets = re.findall(r'lean_ctor_set\((\w+),\s*' + str(final_slot) + r',\s*\w+\);', broken[route])
        if len(packets) != (2 if route == TRANSLATE else 1):
            raise ValueError("Ordered-field final packet constructor shape changed")
        broken[route], count = re.subn(r'(lean_ctor_set\((?:' + '|'.join(map(re.escape, packets)) + r'),\s*' + str(slot) + r',\s*)\w+(\);)',
                                      r'\g<1>lean_box(0)\2', broken[route])
        if count != len(packets):
            raise ValueError("Missing ordered-field retention mutation site")
        mutations.append((route, broken, "discard-packet-slot-" + str(slot), "Ordered-field packet lost"))
    for index, (route, broken, label, prefix) in enumerate(mutations, 1):
        try:
            check(broken, params, route)
        except ValueError as error:
            if not str(error).startswith(prefix):
                raise ValueError(f"Wrong rejection for {label}: {error}") from error
            print(f"REAL_ORDERED_FIELD_MUTATION_REJECTED {index}:{label}: {error}")
        else:
            raise ValueError("Ordered-field mutation accepted: " + label)
    # Independently mutate the final transport's three current-child inputs.
    monotone_mutations = []
    monotone_mutations.append(mutate_call(functions, MULTIPLY, TRANSPORT, 9, "lean_box(0)"))
    # Mutate only the last fresh-product anchor, not the earlier difference*c.
    anchor = FIELD + "startProductAt___redArg"
    matches = list(re.finditer(re.escape(anchor) + r'\(([^;]+)\)', functions[MULTIPLY]))
    if len(matches) != 2:
        raise ValueError("Monotonicity product-anchor shape changed")
    match = matches[-1]
    for slot in (2, 3):
        args = match[1].split(", ")
        args[slot] = "lean_box(0)"
        broken = dict(functions)
        broken[MULTIPLY] = broken[MULTIPLY].replace(match[0], anchor + "(" + ", ".join(args) + ")", 1)
        monotone_mutations.append(broken)
    for index, broken in enumerate(monotone_mutations, 1):
        try:
            check_monotonicity(broken, params)
        except ValueError as error:
            if not str(error).startswith("Final transport reset its exact"):
                raise ValueError("Wrong monotonicity mutation rejection: " + str(error)) from error
            print(f"REAL_ORDERED_FIELD_MUTATION_REJECTED monotonicity-{index}: {error}")
        else:
            raise ValueError("Monotonicity reset mutation accepted")
    duplicate = "l_field_duplicate"
    broken = dict(functions)
    p = params[TRANSLATE]
    call = TRANSLATE + "(" + ",".join(p) + ")"
    broken[duplicate] = "{ lean_object* ignored; ignored = " + call + "; return " + call + "; }"
    ps = dict(params, **{duplicate: p})
    run(broken, ps, TRANSLATE, COMPARE, 2, entry=duplicate)
    print(f"REAL_ORDERED_FIELD_CODEGEN_OK: two current arithmetic output Steps, received witness/owned refinement certificates, computed two-witness budgets, one shared attempt and downstream extraction without reexecution; monotonicity subpackets shared with exact ac/b/c successors; {len(mutations) + len(monotone_mutations)} rejected mutations plus duplicated-producer multiplicity sensitivity; finite nonpersistent route only")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"REAL_ORDERED_FIELD_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
