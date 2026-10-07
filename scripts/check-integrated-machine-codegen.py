#!/usr/bin/env python3
"""Named compiled producer boundaries and configured routing dependencies.
Not a whole-chain cost, allocation bound, hardware result or causality proof.
Semantic exactness is checked separately in Lean.
"""
from pathlib import Path
import re
import runpy
import sys
sys.dont_write_bytecode = True
from integrated_machine_analysis import self_test as flow_self_test
from integrated_machine_checks import run_checks, self_test_checks, compiled_fixture_tests

ROOT = Path(__file__).resolve().parent.parent
checks = runpy.run_path(str(ROOT / "scripts/check-variable-master-codegen.py"))
agent, shared = checks["agent"], checks["shared"]


ROUTING_ARTIFACTS = frozenset(
    "RelationalPerimeter/Computation/Machine/" + name + ".c"
    for name in ("FrontierCircuit", "Fabric", "MasterRuntime", "MasterContract"))
ROUTING_EXTERNALS = frozenset({"l_List_lengthTR___redArg"})
ROUTING_FORBIDDEN = (
    "GeneratedStructural", "normalize", "discover", "Assignment",
    "SequentialAssignment", "VariableMaster", "UnifiedMaster", "ConstitutiveExecution")


def check_configured_routing(functions, owners, graph, entries):
    """Check complete configured packet entries, including transitive helpers.

    Finite list length is the explicit imported compiler boundary. Missing
    project bodies and foreign artifacts fail closed; a helper's innocuous
    name does not authorize a SAT-module dependency. This is a static check
    of pinned generated code, not a whole-program cost or hardware theorem.
    """
    for entry in entries:
        if entry not in functions:
            raise ValueError("ROUTING_MISSING_ENTRY: " + entry)
        for name in sorted(graph(functions, entry)):
            defining = owners.get(name, set())
            if len(defining) != 1 or not defining.issubset(ROUTING_ARTIFACTS):
                raise ValueError(f"ROUTING_FORBIDDEN_ARTIFACT: {entry} -> {name}: {sorted(defining)}")
            references = set(shared["TOKEN"].findall(functions[name])) | {name}
            for reference in sorted(references):
                if any(fragment in reference for fragment in ROUTING_FORBIDDEN):
                    raise ValueError(f"ROUTING_FORBIDDEN_SYMBOL: {entry} -> {reference}")
                if reference not in functions and reference not in ROUTING_EXTERNALS:
                    raise ValueError(f"ROUTING_UNRESOLVED_SYMBOL: {entry} -> {reference}")
            if re.search(r"\blean_apply_\w+\s*\(", functions[name]):
                raise ValueError(f"ROUTING_CALLBACK: {entry} -> {name}")
        print(f"MACHINE_ROUTING_ENTRY_OK {entry}: transitive routing boundary checked")


def routing_self_test():
    """An unrelated failure cannot count as rejection of a routing mutation."""
    import contextlib
    import io
    runtime = "RelationalPerimeter/Computation/Machine/MasterRuntime.c"
    contract = "RelationalPerimeter/Computation/Machine/MasterContract.c"
    circuit = "RelationalPerimeter/Computation/Machine/FrontierCircuit.c"
    sat = "RelationalPerimeter/Computation/ConstitutiveSearch/SAT/StructuralGlobalContextRelation.c"
    functions = {"l_route": "{return l_apply();}", "l_apply": "{return l_fire();}",
                 "l_fire": "{}", "l_helper": "{return l_fire();}", "l_other": "{}"}
    owners = {"l_route": {contract}, "l_apply": {runtime}, "l_fire": {circuit},
              "l_helper": {runtime}, "l_other": {sat}}
    entries = ("l_fire", "l_apply", "l_route")
    cases = [("baseline", {}, None),
             ("finite-list", {"l_route": "{l_List_lengthTR___redArg(); return l_apply();}"}, None),
             ("configured-helper", {"l_apply": "{return l_helper();}"}, None),
             ("SAT-at-apply", {"l_apply": "{l_other(); return l_fire();}"}, "ROUTING_FORBIDDEN_ARTIFACT:"),
             ("SAT-at-route", {"l_route": "{l_other(); return l_apply();}"}, "ROUTING_FORBIDDEN_ARTIFACT:"),
             ("SAT-through-helper", {"l_apply": "{return l_helper();}",
                                      "l_helper": "{return l_other();}"}, "ROUTING_FORBIDDEN_ARTIFACT:"),
             ("SAT-closure", {"l_apply": "{return lean_alloc_closure(l_other,1,0);}"}, "ROUTING_FORBIDDEN_ARTIFACT:"),
             ("callback-at-apply", {"l_apply": "{return lean_apply_1(fn,bits);}"}, "ROUTING_CALLBACK:"),
             ("callback-at-route", {"l_route": "{return lean_apply_1(fn,bits);}"}, "ROUTING_CALLBACK:"),
             ("callback-through-helper", {"l_apply": "{return l_helper();}",
                                           "l_helper": "{return lean_apply_1(fn,bits);}"}, "ROUTING_CALLBACK:"),
             ("missing-body", {"l_apply": "{return l_unknown_project_function();}"}, "ROUTING_UNRESOLVED_SYMBOL:")]
    for label, replacements, reason in cases:
        mutant = dict(functions); mutant.update(replacements)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                check_configured_routing(mutant, owners, shared["reachable"], entries)
        except ValueError as error:
            if reason is None or not str(error).startswith(reason):
                raise ValueError(f"Wrong routing self-test rejection ({label}): {error}") from error
        else:
            if reason is not None:
                raise ValueError("Routing self-test incorrectly accepted " + label)
    print("MACHINE_ROUTING_SELFTEST_OK: entries, helpers, closures, callbacks and missing bodies")


def main():
    agent["self_test"]()
    checks["erased_application_self_test"]()
    flow_self_test(agent["bodies_with_objects"], agent["parameters"], shared["reachable"])
    self_test_checks(agent["bodies_with_objects"], agent["parameters"], shared)
    routing_self_test()
    functions, texts, owners = {}, [], {}
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        parsed = agent["bodies_with_objects"](text)
        functions.update(parsed)
        for name in parsed:
            owners.setdefault(name, set()).add(path.relative_to(ROOT / ".lake/build/ir").as_posix())
    params = agent["parameters"](texts)
    prefix = "lp_relational_x2dperimeter_"

    def symbol(name, file, variant="___redArg"):
        return shared["owned_symbol"](functions, params, owners, prefix, name,
            "RelationalPerimeter/Computation/Machine/" + file + ".c", variant)

    entry = symbol("ConstitutiveSearch.MasterMachine.advance", "MasterRuntime")
    problem = symbol("ConstitutiveSearch.MasterMachine.produceProblem", "MasterRuntime")
    produce = symbol("ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce",
                     "ConstitutiveLiveExecution", "")
    opening = shared["select"](functions, "VariableMaster_openFrontier___redArg")
    normalizer = shared["select"](functions, "normalizeGeneratedStructuralFrontierByFlip___redArg")
    lower = symbol("ConstitutiveSearch.ConnectedFabric.lowerFrontier", "FrontierCircuit")
    normalized = {name: re.sub(r"\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)", r"\1", body)
                  for name, body in functions.items()}
    for current, target in ((entry, produce), (entry, problem),
                            (problem, opening), (problem, normalizer), (problem, lower)):
        analysis = checks["LocalAnalysis"](normalized, params, shared["reachable"], target=target)
        _, low, high = analysis.run(current, [agent["Value"]() for _ in params[current]])
        if (low, high) != (1, 1):
            raise ValueError(f"{current}: expected one {target}, found [{low},{high}]")
        print(f"MACHINE_PRODUCER_OK {current}: {target}=[1,1]")

    common = shared["owned_symbol"](functions, params, owners, prefix,
        "ConstitutiveSearch.EndogenousDecomposition.exploreRecordedCandidates",
        "RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/EndogenousDiscovery.c",
        "___redArg")
    analysis = checks["LocalAnalysis"](normalized, params, shared["reachable"], target=common)
    _, low, high = analysis.run(entry, [agent["Value"]() for _ in params[entry]])
    if (low, high) != (1, 1):
        raise ValueError(f"DISCOVERY_MULTIPLICITY: expected one common live discovery, found [{low},{high}]")
    print("MACHINE_COMMON_DISCOVERY_OK: [1,1], including alternate reduced entry paths")
    compiled_fixture_tests(run_checks(normalized, params, owners, shared))

    runner = symbol("ConstitutiveSearch.MasterMachine.run", "MasterContract")
    perform = symbol("ConstitutiveSearch.MasterMachine.perform", "MasterContract")
    agent["applications"](functions, params, runner, perform, 1, unfolds=(runner,))
    agent["recursive_tail_applications"](functions, params, runner)
    shared["absent"](functions, runner, [
        "MasterMachine_contract", "FutureContract_outcome", "MasterMachine_richPerform",
        "MasterMachine_richAdvance"])
    shared["absent"](functions, entry, [
        "MasterMachine_richAdvance", "LiveContinuation_produce",
        "UnifiedMaster_publicInstance", "roleProfileFiniteCarrier", "_imageRegime"])

    fire = symbol("ConstitutiveSearch.ConnectedFabric.FrontierCircuit.fire", "FrontierCircuit", "")
    routing = symbol("ConstitutiveSearch.MasterMachine.Routing.apply", "MasterRuntime", "")
    route_problem = symbol("ConstitutiveSearch.MasterMachine.routeProblem", "MasterContract")
    check_configured_routing(functions, owners, shared["reachable"], (fire, routing, route_problem))
    print("MACHINE_ROUTING_OK: fire/apply/routeProblem and transitive helpers; no SAT search or assignment callback")

    receive = symbol("ConstitutiveSearch.MasterMachine.receive", "MasterRuntime")
    master = shared["select"](functions, "UnifiedMaster_publicInstance")
    agent["applications"](functions, params, receive, master, 1)
    print("INTEGRATED_MACHINE_CODEGEN_OK")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print("INTEGRATED_MACHINE_CODEGEN_FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
