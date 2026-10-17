#!/usr/bin/env python3
"""Bounded C-IR checks for rich and live additive transitions.

Explicit callback boundaries stand for heterogeneous child services. Counts
are applications on the analysed C route, not physical cost or heap bounds.
The separate Lean projection laws connect the rich and live contracts.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
from unified_codegen_analysis import Analysis, Value, parameters, add_static_objects

ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))
PREFIX = "lp_relational_x2dperimeter_RelationalPerimeter_Constitution_Reals_"
LEFT, RIGHT, READ, LIVE_LEFT, LIVE_RIGHT, IDENTITY = (
    "l_additive_probe_left", "l_additive_probe_right", "l_additive_probe_read",
    "l_additive_probe_live_left", "l_additive_probe_live_right", "l_additive_probe_identity")
ENTRY = PREFIX + "RelationalRealAddition_produceAddition"
ACTION = PREFIX + "SignedDyadicCode_add"
EXECUTOR = PREFIX + "ConstitutiveRuntime_execute___redArg"
LIVE = PREFIX + "RelationalRealAddition_additionLiveStep"
LIVE_BOXED = LIVE + "___boxed"
ADD_ENVIRONMENT = PREFIX + "RelationalRealAddition_addEnvironment"
LIVE_ENVIRONMENT = PREFIX + "HeterogeneousRealRuntime_Service_liveEnvironment___redArg"
ARCHIVED_LIVE = PREFIX + "HeterogeneousRealRuntime_ArchivedExecution_live___redArg"
PERFORM_RUNTIME = PREFIX + "HeterogeneousRealRuntime_performRuntime___redArg"
LEAF = PREFIX + "HeterogeneousRealRuntime_leaf"
LEAF_LIVE_STEP = PREFIX + "HeterogeneousRealRuntime_leafLiveStep"
FAMILY_ENVIRONMENT = PREFIX + "CommonRealRuntime_environmentOfFamily___redArg"
COMMON_PERFORM = PREFIX + "CommonRealRuntime_performReal"


def tagged(name):
    return Value(tags=frozenset({name}))


class AdditiveAnalysis(Analysis):
    def __init__(self, *args, validate=False, stop_executor=False, **kwargs):
        super().__init__(*args, **kwargs)
        self.validate, self.stop_executor = validate, stop_executor

    def run(self, name, arguments):
        if name in (LEFT, RIGHT, LIVE_LEFT, LIVE_RIGHT):
            if len(arguments) != 2:
                raise ValueError("Child callback arity changed: " + name)
            if self.validate:
                expected = {LEFT: "current-left", RIGHT: "current-right",
                            LIVE_LEFT: "live-left", LIVE_RIGHT: "live-right"}[name]
                if arguments[0].retained() != frozenset({expected}):
                    raise ValueError("Child callback does not use its current state: " + name)
            count = int(name == self.target)
            result = tagged(name) if self.capture else Value()
            if name in (LIVE_LEFT, LIVE_RIGHT):
                result = Value(fields={0: tagged(name + "-next"), 1: result}) if self.capture else Value()
            return result, count, count
        if name == READ:
            return arguments[-1], 0, 0
        if name == IDENTITY:
            return arguments[0], 0, 0
        if name == EXECUTOR and self.validate:
            if arguments[3].retained() != frozenset({"current-journal"}):
                raise ValueError("Arithmetic action does not use the current journal")
            if self.stop_executor:
                return tagged("executed-action"), int(name == self.target), int(name == self.target)
        return super().run(name, arguments)


def service(callback, live_callback, initial, marked):
    # Type/proof fields erase. These are the exact compiled Service slots.
    return Value(fields={0: tagged(initial) if marked else Value(), 1: Value(function=callback),
                         4: Value(function=READ), 6: Value(function=IDENTITY),
                         7: Value(function=IDENTITY), 8: Value(function=IDENTITY),
                         9: Value(function=live_callback), 10: Value(function=IDENTITY)})


def live_environment(callback):
    # The compact environment contains read, step and answer only.
    return Value(fields={0: Value(function=IDENTITY), 1: Value(function=callback),
                         2: Value(function=IDENTITY)})


def arguments(marked=False):
    return [Value(), Value(), service(LEFT, LIVE_LEFT, "initial-left", marked),
            service(RIGHT, LIVE_RIGHT, "initial-right", marked),
            tagged("current-left") if marked else Value(),
            tagged("current-right") if marked else Value(),
            tagged("current-journal") if marked else Value(), Value()]


def require_count(functions, params, entry, args, target, expected=1):
    _, low, high = AdditiveAnalysis(functions, params, shared["reachable"], target=target).run(entry, args)
    if (low, high) != (expected, expected):
        raise ValueError(f"{entry}: {target}: expected [{expected},{expected}], found [{low},{high}]")


def validate_current(functions, params):
    return AdditiveAnalysis(functions, params, shared["reachable"], target=EXECUTOR,
                            capture=True, validate=True, stop_executor=True).run(ENTRY, arguments(True))[0]


def reject_mutation(functions, params, description, expected):
    try:
        validate_current(functions, params)
    except ValueError as error:
        if not str(error).startswith(expected):
            raise ValueError("Mutation failed for an unexpected reason: " + description + ": " + str(error)) from error
        print("REAL_ADDITION_MUTATION_REJECTED " + description)
        return
    raise ValueError("Persistence mutation was accepted: " + description)


def main():
    texts = [path.read_text(encoding="utf-8") for path in sorted((ROOT / ".lake/build/ir").rglob("*.c"))]
    probes = "\n".join(
        f"LEAN_EXPORT lean_object* {name}(lean_object* a, lean_object* p){{ return a; }}"
        for name in (LEFT, RIGHT, LIVE_LEFT, LIVE_RIGHT))
    probes += (f"\nLEAN_EXPORT lean_object* {READ}(lean_object* a, lean_object* p, lean_object* r){{ return r; }}"
               f"\nLEAN_EXPORT lean_object* {IDENTITY}(lean_object* a){{ return a; }}\n")
    texts.append(probes)
    functions = {}
    for source in texts:
        functions.update(shared["bodies"](source))
        add_static_objects(functions, source)
    functions = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                 for name, body in functions.items()}
    params = parameters(texts)
    for name, arity in ((ENTRY, 8), (LIVE, 4), (ACTION, 2), (EXECUTOR, 5),
                        (ADD_ENVIRONMENT, 4),
                        (LIVE_ENVIRONMENT, 1), (ARCHIVED_LIVE, 1), (PERFORM_RUNTIME, 2),
                        (LEAF, 3), (LEAF_LIVE_STEP, 3), (FAMILY_ENVIRONMENT, 1),
                        (COMMON_PERFORM, 2)):
        if name not in functions or len(params.get(name, [])) != arity:
            raise ValueError("Missing exact additive definition/arity: " + name)
    args = arguments()
    for target in (LEFT, RIGHT, EXECUTOR, ACTION):
        require_count(functions, params, ENTRY, args, target)
        print(f"REAL_ADDITION_APPLICATION_OK {target}=[1,1]")
    # Equal services and states still require two applications in two roles.
    # This checks multiplicity, not inequality of the returned Lean values.
    aliased_args = arguments()
    aliased_args[3], aliased_args[5] = aliased_args[2], aliased_args[4]
    for target, count in ((LEFT, 2), (RIGHT, 0), (EXECUTOR, 1), (ACTION, 1)):
        require_count(functions, params, ENTRY, aliased_args, target, count)
    result = validate_current(functions, params)
    for slot, expected in ((0, LEFT), (1, RIGHT), (2, "executed-action")):
        if result.fields.get(slot, Value()).retained() != frozenset({expected}):
            raise ValueError("Produced packet lost its original child/action at slot " + str(slot))
    observer = PREFIX + "RelationalRealAddition_AdditionProduction_code___redArg"
    if observer not in functions:
        raise ValueError("Missing exact stored-code projection")
    observer_calls = set(re.findall(r'\b(\w+)\s*\(', functions[observer]))
    if any(name != "lean_ctor_get" and not name.startswith(("lean_inc", "lean_dec"))
           for name in observer_calls):
        raise ValueError("Stored-code readout does work beyond projections: " + str(observer_calls))

    # Starting from an initial child instead of the incoming archive must fail.
    perform = PREFIX + "HeterogeneousRealRuntime_perform___redArg"
    original = params[ENTRY]
    for service_slot, archive_slot, label in ((2, 4, "reset-left-archive"), (3, 5, "reset-right-archive")):
        broken = dict(functions)
        pattern = re.escape(perform) + r'\(' + re.escape(original[service_slot]) + r',\s*' + re.escape(original[archive_slot]) + r','
        replacement = perform + "(" + original[service_slot] + ", lean_ctor_get(" + original[service_slot] + ", 0),"
        broken[ENTRY], count = re.subn(pattern, replacement, broken[ENTRY])
        if count != 1:
            raise ValueError("Archive mutation site changed: " + label)
        reject_mutation(broken, params, label, "Child callback does not use its current state")
    broken = dict(functions)
    broken[ENTRY], count = re.subn(r'(\b' + re.escape(EXECUTOR) + r'\([^;]*?,\s*)' +
                                   re.escape(original[6]) + r'(\s*,)', r'\1lean_box(0)\2', broken[ENTRY])
    if count != 1:
        raise ValueError("Journal mutation site changed")
    reject_mutation(broken, params, "reset-arithmetic-journal", "Arithmetic action does not use the current journal")

    # Multiplicity remains sensitive even when only the second result survives.
    alias = "l_additive_probe_double"
    broken = dict(functions)
    broken[alias] = "{ lean_object* a; a = " + ENTRY + "(p,d,l,r,la,ra,j,n); return " + ENTRY + "(p,d,l,r,la,ra,j,n); }"
    mutated_params = dict(params, **{alias: ["p", "d", "l", "r", "la", "ra", "j", "n"]})
    for target in (LEFT, RIGHT, EXECUTOR, ACTION):
        require_count(broken, mutated_params, alias, args, target, 2)
    preserves = PREFIX + "RelationalRealAddition_additionProgram___redArg___lam__4"
    if preserves not in functions:
        raise ValueError("Missing exact preservation callback")
    broken = dict(functions)
    broken[preserves] = broken[preserves].replace("{", "{ lean_object* duplicate; duplicate = " +
                                                 ACTION + "(lean_box(0),lean_box(0));", 1)
    require_count(broken, params, ENTRY, args, ACTION, 2)

    live_args = [live_environment(LIVE_LEFT), live_environment(LIVE_RIGHT),
                 Value(fields={0: Value(), 1: Value(), 2: Value()}), Value()]
    for target in (LIVE_LEFT, LIVE_RIGHT, ACTION):
        require_count(functions, params, LIVE, live_args, target)
    for target in (LEFT, RIGHT, EXECUTOR):
        require_count(functions, params, LIVE, live_args, target, 0)
    aliased_live_args = list(live_args)
    aliased_live_args[1] = aliased_live_args[0]
    for target, count in ((LIVE_LEFT, 2), (LIVE_RIGHT, 0), (ACTION, 1)):
        require_count(functions, params, LIVE, aliased_live_args, target, count)
    print("REAL_ADDITION_ALIASED_ROLES_OK: rich=two applications/one action; live=two applications/one add")
    live_args[2] = Value(fields={0: tagged("live-left"), 1: tagged("live-right"), 2: tagged("last")})
    AdditiveAnalysis(functions, params, shared["reachable"], target=ACTION,
                     capture=True, validate=True).run(LIVE, live_args)

    # The live carrier must not retain the rich service.  Only compiled Service
    # slots 8/9/10 (read/step/answer) may enter its environment.
    marked_service = Value(fields={slot: tagged(f"rich-{slot}") for slot in range(11)})
    marked_service.fields[6] = Value(function=IDENTITY)
    compact, _, _ = AdditiveAnalysis(functions, params, shared["reachable"],
                                     target="", capture=True).run(LIVE_ENVIRONMENT, [marked_service])
    for slot, source in ((0, "rich-8"), (1, "rich-9"), (2, "rich-10")):
        if compact.fields.get(slot, Value()).retained() != frozenset({source}):
            raise ValueError("Compact live environment retained the wrong Service field")
    if compact.retained() != frozenset({"rich-8", "rich-9", "rich-10"}):
        raise ValueError("Compact live environment retained rich archive machinery")
    archived = Value(fields={0: marked_service, 1: tagged("current-archive")})
    live_state, _, _ = AdditiveAnalysis(functions, params, shared["reachable"],
                                        target="", capture=True).run(ARCHIVED_LIVE, [archived])
    if live_state.fields.get(0, Value()).retained() != compact.retained():
        raise ValueError("Runtime did not install the compact live environment")
    if live_state.fields.get(1, Value()).retained() != frozenset({"current-archive"}):
        raise ValueError("Runtime live memory was not projected from the current archive")
    runtime_state = Value(fields={0: live_environment(LIVE_LEFT), 1: tagged("live-left")})
    runtime_args = [runtime_state, Value()]
    require_count(functions, params, PERFORM_RUNTIME, runtime_args, LIVE_LEFT)
    AdditiveAnalysis(functions, params, shared["reachable"], target=LIVE_LEFT,
                     capture=True, validate=True).run(PERFORM_RUNTIME, runtime_args)
    for target in (LEFT, RIGHT, EXECUTOR):
        require_count(functions, params, PERFORM_RUNTIME, runtime_args, target, 0)

    # The additive service's live callback closes over the two compact child
    # environments produced above, not over either rich child Service.
    environment_body = functions[ADD_ENVIRONMENT]
    compact_vars = re.findall(
        r'\b(\w+)\s*=\s*' + re.escape(LIVE_ENVIRONMENT) + r'\([^;]+\);', environment_body)
    if len(compact_vars) != 2 or compact_vars[0] == compact_vars[1]:
        raise ValueError("Additive live callback does not build two compact child environments")
    closure = re.search(
        r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' + re.escape(LIVE_BOXED) +
        r'\),\s*4,\s*2\);', environment_body)
    if closure is None:
        raise ValueError("Additive live callback no longer has exactly two fixed captures")
    for slot, compact_var in enumerate(compact_vars):
        retained = (r'lean_closure_set\(' + re.escape(closure.group(1)) + r',\s*' + str(slot) +
                    r',\s*' + re.escape(compact_var) + r'\);')
        if re.search(retained, environment_body) is None:
            raise ValueError("Additive live callback captures a rich child instead of its compact environment")

    # A leaf callback must capture only CommonRealRuntime.Environment.  That
    # environment is itself exactly producer + modulus, not RuntimeReal or its
    # produced rich completeness object.
    marked_family = Value(fields={slot: tagged(f"family-{slot}") for slot in range(4)})
    leaf_environment, _, _ = AdditiveAnalysis(functions, params, shared["reachable"],
                                               target="", capture=True).run(
                                                   FAMILY_ENVIRONMENT, [marked_family])
    if leaf_environment.retained() != frozenset({"family-0", "family-2"}):
        raise ValueError("Leaf executable environment is not exactly producer + modulus")
    leaf_body = functions[LEAF]
    family_environment = re.search(
        r'\b(\w+)\s*=\s*' + re.escape(FAMILY_ENVIRONMENT) + r'\([^;]+\);', leaf_body)
    leaf_closure = re.search(
        r'\b(\w+)\s*=\s*lean_alloc_closure\(\(void\*\)\(' + re.escape(LEAF_LIVE_STEP) +
        r'\),\s*3,\s*1\);', leaf_body)
    if family_environment is None or leaf_closure is None:
        raise ValueError("Leaf live callback no longer closes over one compact executable environment")
    leaf_capture = (r'lean_closure_set\(' + re.escape(leaf_closure.group(1)) + r',\s*0,\s*' +
                    re.escape(family_environment.group(1)) + r'\);')
    if re.search(leaf_capture, leaf_body) is None:
        raise ValueError("Leaf live callback captures RuntimeReal instead of producer + modulus")
    leaf_step_body = functions[LEAF_LIVE_STEP]
    if len(re.findall(r'\b' + re.escape(COMMON_PERFORM) + r'\s*\(', leaf_step_body)) != 1:
        raise ValueError("Leaf live step does not execute the common runtime exactly once")
    if "AuthoritativeRuntime_perform" in leaf_step_body or "RuntimeCorrespondence_RuntimeReal" in leaf_step_body:
        raise ValueError("Leaf live step recalls rich authoritative runtime data")
    print("REAL_ADDITION_CODEGEN_OK: rich=current archives/current journal, one child application each, one executor/action, retained packet, projection-only code; live=compact read/step/answer environment, runtime transition=one compact step/no rich producer, leaf=producer+modulus only, additive callback=two compact child environments, one child liveStep each/one add/no rich executor")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"REAL_ADDITION_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
