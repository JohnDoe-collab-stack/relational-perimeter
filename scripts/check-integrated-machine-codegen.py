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


def main():
    agent["self_test"]()
    checks["erased_application_self_test"]()
    flow_self_test(agent["bodies_with_objects"], agent["parameters"], shared["reachable"])
    self_test_checks(agent["bodies_with_objects"], agent["parameters"], shared)
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
    shared["absent"](functions, fire, [
        "GeneratedStructural", "normalize", "discover", "Assignment",
        "SequentialAssignment", "VariableMaster", "MasterMachine"])
    for name in shared["reachable"](functions, fire):
        if "lean_apply_" in functions.get(name, ""):
            raise ValueError("Configured packet action applies an unknown callback: " + name)
    print("MACHINE_ROUTING_OK: finite routing/gates; no SAT search or assignment callback")

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
