#!/usr/bin/env python3
"""Bounded pinned-C checks of finite density/Archimedean production.

Native comparisons, coherence and numerical margin proofs are named boundaries.
The executor boundary invokes all actual concrete phase callbacks, so a second
selection in preservation/storage is counted. No physical-cost/heap theorem or
universal C/callback verification is claimed. No persistent selector is added.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
field = runpy.run_path(str(ROOT / "scripts/check-real-ordered-field-codegen.py"))
base, Value, PREFIX = field["base"], field["Value"], field["PREFIX"]
tag, require = field["tagged"], field["require"]
D = PREFIX + "RelationalRealDensity_"
ENTRY, BOUND = D + "produceDensity", D + "produceNaturalBound"
BISECT, BOUNDS = PREFIX + "DyadicDensity_bisect___redArg", PREFIX + "DyadicDensity_naturalBounds"
EXECUTOR = PREFIX + "ConstitutiveRuntime_execute___redArg"
PHASE = PREFIX + "ConstitutiveRuntime_executePhase"
ENV, CODE, NEXT, COMPARE = field["ENV"], field["CODE"], field["NEXT"], field["COMPARE"]
EXECUTE = PREFIX + "RelationalRealAddition_executeAt"
COHERENT, STRENGTHEN = field["COHERENT"], field["STRENGTHEN"]
CONSTANT, DYADIC = PREFIX + "RuntimeCorrespondence_constantRuntime", D + "dyadic"


def arguments(route):
    if route == ENTRY:
        origin = field["order"]("origin", 7)
        origin.fields[0], origin.fields[1] = tag("origin-a-archive"), tag("origin-b-archive")
        origin.fields[5] = Value(fields={0: tag("origin-a"), 1: tag("origin-b")})
        origin.fields[6] = tag("origin-margin")
        return [Value(), Value(), tag("a"), tag("b"), origin, tag("current-journal")]
    return [Value(), Value(), tag("source"), tag("current-source"), tag("current-journal")]


class DensityAnalysis(field["FieldAnalysis"]):
    def __init__(self, *args, unfold_dyadic=False, **kwargs):
        super().__init__(*args, **kwargs)
        self.unfold_dyadic = unfold_dyadic

    def global_value(self, name):
        # Exact pinned RequestStamp.limit 2 scalar, reached while the existing
        # stored projection builds its provenance package. It is not a budget
        # or producer boundary; validate its literal before interpreting it.
        stamp = D + "boundProgram___lam__0___closed__0"
        if name in (stamp, stamp + "_value"):
            body = self.functions[name]
            if "((size_t)(2) << 1) | 1" not in body:
                if stamp + "_value" not in body:
                    raise ValueError("Bound request-stamp static shape changed")
                body = self.functions[stamp + "_value"]
                if "((size_t)(2) << 1) | 1" not in body:
                    raise ValueError("Bound request-stamp literal changed")
            return Value(fields={0: Value(number=2)})
        return super().global_value(name)

    def invoke(self, closure, args):
        if closure.function is None:
            raise ValueError("Density phase callback is unresolved")
        return self.run(closure.function, [closure.fields[i] for i in range(closure.fixed)] + args)

    def run(self, name, args):
        count = int(name == self.target)
        if name == ENV:
            role = next(iter(args[2].tags), "")
            return Value(tags=frozenset({role}), fields={0: tag("initial-" + role)}), 0, 0
        if name == CODE:
            return tag("code-" + next(iter(args[-1].tags), "missing")), 0, 0
        if name == NEXT:
            role = next(iter(args[-1].tags), "missing")
            expected = {"origin-a": "origin-a-archive", "origin-b": "origin-b-archive",
                        "left-q": "initial-q", "probe": "current-source", "lower-source": "next-probe"}
            if role not in expected:
                raise ValueError("Density successor lost its owned Step: " + role)
            require(args[1], expected[role], "Density successor resets its current archive")
            return tag("next-" + role), 0, 0
        if name == EXECUTE:
            require(args[2], "source", "Bound probe lost its received source")
            require(args[3], "current-source", "Bound probe resets the current archive")
            if args[4].number != 2:
                raise ValueError("Bound probe lost its two-bit precision")
            return tag("probe"), count, count
        if name == BISECT:
            for slot, expected in ((0, "code-origin-a"), (1, "code-origin-b"), (2, "origin-margin")):
                require(args[slot], expected, "Bisection lost its received Steps/margin")
            return Value(fields={0: tag("midpoint-code"), 1: tag("half-left"), 2: tag("half-right")}), count, count
        if name == BOUNDS:
            require(args[0], "code-probe", "Natural bounds do not read the owned probe")
            return Value(fields={0: tag("upper-natural"), 1: tag("lower-natural"),
                                 2: tag("coarse-upper"), 3: tag("coarse-lower")}), count, count
        if name == EXECUTOR:
            require(args[3], "current-journal", "Selector resets its received journal")
            program, request = args[0], Value(number=0)
            received, lo, hi = self.invoke(program.fields[1], [request])
            searched, a, b = self.invoke(program.fields[2], [request, received]); lo += a; hi += b
            acted, a, b = self.invoke(program.fields[3], [request, searched]); lo += a; hi += b
            accepted, a, b = self.invoke(program.fields[4], [request, searched, acted]); lo += a; hi += b
            authorized, a, b = self.invoke(program.fields[5], [request, searched, acted, accepted]); lo += a; hi += b
            decomposed, a, b = self.invoke(program.fields[6], [request, searched, acted, accepted, authorized]); lo += a; hi += b
            continued, a, b = self.invoke(program.fields[7], [request, searched, acted, accepted, authorized, decomposed]); lo += a; hi += b
            stored, a, b = self.invoke(program.fields[8], [request, searched, acted, accepted, authorized, decomposed, continued]); lo += a; hi += b
            # ExecutedRequest/Memory erase their single-field wrappers. These
            # are the exact projected slots used by stored/readout/margins.
            result = Value(tags=frozenset({"selector-action"}), fields={
                0: Value(fields={0: Value(fields={1: accepted})}), 1: stored})
            return result, lo + count, hi + count
        if name in (PREFIX + "DyadicDensity_naturalCode", PREFIX + "DyadicDensity_negativeNaturalCode"):
            positive = name.endswith("_naturalCode")
            require(args[0], "upper-natural" if positive else "lower-natural", "Bound target ignores the stored natural")
            return tag("upper-code" if positive else "lower-code"), 0, 0
        if name == DYADIC and not self.unfold_dyadic:
            role = {"midpoint-code": "q", "lower-code": "lower", "upper-code": "upper"}.get(next(iter(args[2].tags), ""))
            if role is None:
                raise ValueError("Constant target is not the exact stored selection output")
            return tag(role), count, count
        if name == CONSTANT:
            return args[2], 0, 0
        if name == COMPARE:
            roles = tuple(next(iter(v.tags), "") for v in args[:2])
            routes = {("a", "q"): ("next-origin-a", "initial-q", "left-a", "left-q", "density-left"),
                      ("q", "b"): ("next-left-q", "next-origin-b", "right-q", "right-b", "density-right"),
                      ("lower", "source"): ("initial-lower", "next-probe", "lower-constant", "lower-source", "bound-lower"),
                      ("source", "upper"): ("next-lower-source", "initial-upper", "upper-source", "upper-constant", "bound-upper")}
            if roles not in routes:
                raise ValueError("Selection comparison lost its oriented roles")
            la, ra, left, right, label = routes[roles]
            require(args[2], la, "Comparison resets its exact left successor")
            require(args[3], ra, "Comparison resets its exact right successor")
            budget = (10, 13) if self.route == ENTRY else (2, 5)
            if (args[4].number, args[5].number) != budget:
                raise ValueError("Selection comparison lost its proved margin/response budget")
            return Value(tags=frozenset({label}), fields={1: Value(fields={0: tag(left), 1: tag(right)})}), count, count
        if name == COHERENT:
            return Value(function="l_density_near_" + next(iter(args[2].tags), "")), 0, 0
        if name.startswith("l_density_near_"):
            role = name.removeprefix("l_density_near_")
            expected = {"a": ("origin-a", ("left-a",)), "b": ("origin-b", ("right-b",)),
                        "source": ("probe", ("lower-source", "upper-source"))}
            if role not in expected:
                raise ValueError("Unknown density coherence role")
            received, current = expected[role]
            require(args[5], received, "Coherence reconstructs its original Step")
            if args[6].tags not in (frozenset({v}) for v in current):
                raise ValueError("Coherence does not consume its actual comparison Step")
            return tag("near-" + role), 0, 0
        if name == STRENGTHEN:
            roles = tuple(next(iter(v.tags), "") for v in args[1:])
            expected = {("code-left-a", "code-left-q"): "density-left-margin",
                        ("code-right-q", "code-right-b"): "density-right-margin",
                        ("code-lower-constant", "code-lower-source"): "bound-lower-margin",
                        ("code-upper-source", "code-upper-constant"): "bound-upper-margin"}
            if roles not in expected:
                raise ValueError("Margin does not use the exact comparison replies")
            return tag(expected[roles]), 0, 0
        return super().run(name, args)


def run(functions, params, route, target="", entry=None, args=None, unfold_dyadic=False):
    return DensityAnalysis(functions, params, base["shared"]["reachable"], route=route, target=target,
                           capture=True, unfold_dyadic=unfold_dyadic).run(entry or route, args or arguments(route))


def check(functions, params, route):
    targets = ((EXECUTOR, 1), (COMPARE, 2), (DYADIC, 1 if route == ENTRY else 2),
               (BISECT, int(route == ENTRY)), (BOUNDS, int(route == BOUND)), (EXECUTE, int(route == BOUND)))
    for target, expected in targets:
        value, low, high = run(functions, params, route, target)
        if (low, high) != (expected, expected):
            raise ValueError(f"Selection multiplicity {target}: expected {expected}, found [{low},{high}]")
    tags = ("selector-action", "q", "density-left", "density-right", "near-a", "near-b",
            "density-left-margin", "density-right-margin") if route == ENTRY else (
            "probe", "selector-action", "lower", "upper", "bound-lower", "bound-upper", "near-source", "near-source",
            "bound-lower-margin", "bound-upper-margin")
    for slot, expected in enumerate(tags):
        require(value.fields.get(slot, Value()), expected, "Selection packet lost its owned chronological result")


def edit_call(functions, entry, callee, occurrence, slot, replacement):
    result = dict(functions)
    matches = list(re.finditer(re.escape(callee) + r'\(([^;]+)\)', result[entry]))
    if occurrence >= len(matches):
        raise ValueError("Selection mutation site changed: " + callee)
    match = matches[occurrence]
    args = match[1].split(", ")
    args[slot] = replacement
    result[entry] = result[entry][:match.start()] + callee + "(" + ", ".join(args) + ")" + result[entry][match.end():]
    return result


def main():
    texts = [p.read_text(encoding="utf-8") for p in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    functions = {}
    for source in texts:
        functions.update(base["shared"]["bodies"](source))
        base["add_static_objects"](functions, source)
    params = base["parameters"](texts)
    functions = {name: re.sub(r'lean_unsigned_to_nat\((\d+)u\)', r'l_field_number_\1()',
        re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body).replace("lean_nat_add(", "l_field_add("))
        for name, body in functions.items()}
    for name, arity in ((ENTRY, 6), (BOUND, 5), (BISECT, 3), (BOUNDS, 1), (DYADIC, 3)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact density C definition/arity: " + name)
    if len(re.findall(re.escape(PHASE) + r'\(', functions[EXECUTOR])) != 6:
        raise ValueError("Constitutive executor no longer appends its six phases")
    for route in (ENTRY, BOUND):
        check(functions, params, route)
    compact, _, _ = run(functions, params, ENTRY, entry=DYADIC,
                         args=[Value(), Value(), tag("stored-code")], unfold_dyadic=True)
    if compact.retained() != frozenset({"stored-code"}):
        raise ValueError("Concrete constant factory captures rich selection data")
    mutations = []
    for route in (ENTRY, BOUND):
        mutations.append((route, edit_call(functions, route, EXECUTOR, 0, 3, "lean_box(0)"), "reset-journal"))
        for slot in (2, 3):
            for occurrence in (0, 1):
                mutations.append((route, edit_call(functions, route, COMPARE, occurrence, slot, "lean_box(0)"), "reset-comparison-successor"))
    mutations.append((BOUND, edit_call(functions, BOUND, EXECUTE, 0, 3, "lean_box(0)"), "reset-current-probe"))
    # Explicitly reset the three critical next projections: q, probe, lower-source.
    for route, occurrence in ((ENTRY, 1), (BOUND, 0), (BOUND, 1)):
        broken = dict(functions)
        matches = list(re.finditer(r'(\w+)\s*=\s*' + re.escape(NEXT) + r'\([^;]+\);', broken[route]))
        if len(matches) != (3 if route == ENTRY else 2):
            raise ValueError("Critical selection successor shape changed")
        match = matches[occurrence]
        broken[route] = broken[route].replace(match[0], match[1] + " = lean_box(0);", 1)
        mutations.append((route, broken, "reset-critical-next-" + str(occurrence)))
    for route, callee in ((ENTRY, BISECT), (BOUND, BOUNDS)):
        callback = D + ("densityProgram" if route == ENTRY else "boundProgram") + "___lam__3"
        broken = dict(functions)
        match = re.search(r'(\w+)\s*=\s*(' + re.escape(callee) + r'\([^;]+\));', broken[callback])
        if match is None:
            raise ValueError("Selection duplication site changed")
        broken[callback] = broken[callback].replace(match[0], "lean_object* ignored; ignored = " + match[2] + "; " + match[0])
        mutations.append((route, broken, "duplicate-valid-selection"))
        for slot in range(len(params[callee])):
            mutations.append((route, edit_call(functions, callback, callee, 0, slot, "lean_box(0)"), "discard-selection-input"))
    for route, literals in ((ENTRY, ("3", "6")), (BOUND, ("2", "5"))):
        for literal in literals:
            broken = dict(functions)
            broken[route] = broken[route].replace("l_field_number_" + literal + "()", "l_field_number_0()")
            mutations.append((route, broken, "underbudget-" + literal))
    for route in (ENTRY, BOUND):
        for occurrence in range(1 if route == ENTRY else 2):
            mutations.append((route, edit_call(functions, route, DYADIC, occurrence, 2, "lean_box(0)"), "ignore-stored-target"))
    for index, (route, broken, label) in enumerate(mutations, 1):
        try:
            check(broken, params, route)
        except ValueError as error:
            prefixes = {
                "reset-journal": ("Selector resets its received journal",),
                "reset-comparison-successor": ("Comparison resets its exact",),
                "reset-current-probe": ("Bound probe resets the current archive",),
                "duplicate-valid-selection": ("Selection multiplicity",),
                "discard-selection-input": ("Bisection lost its received", "Natural bounds do not read"),
                "ignore-stored-target": ("Constant target is not the exact stored",),
            }
            expected = ("Comparison resets its exact",) if label.startswith("reset-critical-next-") else (
                ("Selection comparison lost its proved", "Bound probe lost its two-bit")
                if label.startswith("underbudget-") else prefixes[label])
            if not str(error).startswith(expected):
                raise ValueError(f"Wrong rejection for {label}: {error}") from error
            print(f"REAL_DENSITY_MUTATION_REJECTED {index}:{label}: {error}")
        else:
            raise ValueError("Selection mutation accepted: " + label)
    print(f"REAL_DENSITY_CODEGEN_OK: one stored bisection/bilateral bound action; all concrete phase callbacks; six journal phases; exact shared target outputs; two comparisons and exact q/probe/lower-source successors; native constant captures only its code; {len(mutations)} rejected mutations; finite nonpersistent scope")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        print(f"REAL_DENSITY_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
