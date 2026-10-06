"""Verified local producer summaries and paired-runner provenance checks.

The erased formula/proof indices remain Lean obligations. Runtime projections
below are checked against actual C bodies under the pinned compiler ABI.
"""
from integrated_machine_analysis import Flow, FlowError, parameter, path, same, require, unique


class MachineChecks:
    def __init__(self, functions, params, owners, shared):
        self.functions, self.params, self.owners, self.shared = functions, params, owners, shared
        self.names = {}

    def resolve(self, key, suffix, file, arity, variant="___redArg"):
        suffix = suffix.replace(".", "_") + variant
        matches = [n for n in self.params if n.endswith(suffix)
                   and self.owners.get(n) == {file}]
        if len(matches) != 1:
            raise FlowError(f"FORM_UNSUPPORTED: {key}: missing/ambiguous owned symbol {matches}")
        name = matches[0]
        if len(self.params[name]) != arity:
            raise FlowError(f"FORM_UNSUPPORTED: {key}: compiler ABI arity changed")
        self.names[key] = name
        return name

    def machine(self, key, suffix, file, arity, variant="___redArg"):
        return self.resolve(key, suffix, "RelationalPerimeter/Computation/Machine/" + file + ".c", arity, variant)

    def endogenous(self, key, suffix, file, arity, variant="___redArg"):
        return self.resolve(key, suffix,
            "RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/" + file + ".c", arity, variant)

    def analyze(self, key, inline=(), loop=False, expand_unknown_writes=True):
        # Other named functions become boundaries only after their body checks.
        entry = self.names[key]
        flow = Flow(self.functions, self.params, self.shared["reachable"],
                    unfold=(entry, *(self.names[k] for k in inline)),
                    terminals=set(self.names.values()) - {entry} - {self.names[k] for k in inline},
                    cut_backedges=(entry,) if loop else (), owners=self.owners or None,
                    expand_unknown_writes=expand_unknown_writes)
        return flow.inspect(entry)

    def one(self, calls, key):
        return unique(calls, self.names[key])

    def args(self, call, *expected):
        require(len(call.arguments) == len(expected) and
                all(same(a, b) for a, b in zip(call.arguments, expected)),
                call.name + ": wrong argument origin")

    def check(self):
        p = [parameter(i) for i in range(4)]
        for value, calls in self.analyze("runExtracted"):
            filtering = self.one(calls, "filter")
            self.args(filtering, path(p[0], 3), path(p[1], 1, 0))
            search = self.one(calls, "search")
            self.args(search, path(p[1], 0), path(filtering.result, 0))
            require(same(path(value, 3), search.result), "search result ignored in runExtracted")
        for value, calls in self.analyze("discover"):
            extraction, run = self.one(calls, "extraction"), self.one(calls, "runExtracted")
            self.args(extraction, p[0]); self.args(run, p[0], extraction.result)
            require(same(value, run.result), "discover result not the executed run")
        # Validate success and failure shapes of the getter itself. It may
        # return none, but every success reads precisely the discovered fields.
        successes = 0
        for value, _ in self.analyze("discovered"):
            if value.origin == ("literal", 0) and not value.fields:
                continue
            require(same(path(value, 0, 0), path(p[0], 0, 0, 0)) and
                    same(path(value, 0, 1), path(p[0], 0, 0, 1, 0)),
                    "discovered? reconstructs/changes the search result")
            successes += 1
        require(successes > 0, "discovered? has no checked success path")
        for value, _ in self.analyze("candidateEntry"):
            require(same(path(value, 0), p[0]) and same(path(value, 1), path(p[1], 1, 0)) and
                    same(path(value, 2), path(p[1], 2, 0)) and same(path(value, 3), path(p[1], 0)),
                    "candidate entry not from the produced source/target/relation")
        for value, calls in self.analyze("stored"):
            entry = self.one(calls, "candidateEntry")
            self.args(entry, path(p[0], 0, 0, 0), path(p[0], 0, 0, 1))
            require(same(value, entry.result), "stored schedule not from found candidate")
        for value, calls in self.analyze("validate"):
            search = self.one(calls, "validateSearch")
            self.args(search, path(p[0], 0), path(p[0], 1), path(p[0], 2))
            require(same(value, search.result), "validation not from stored schedule")
        for value, calls in self.analyze("execution"):
            indexed = self.one(calls, "indexedExecution")
            self.args(indexed, p[0], p[1])
            require(same(path(value, 0), indexed.result) and
                    same(path(value, 1), path(indexed.result, 0, 0)) and
                    same(path(value, 2), path(p[0], 2)), "executed code not from validated search")
        for value, _ in self.analyze("indexedExecution"):
            if path(value, 0).origin == ("literal", 0):
                continue  # Explicit failed measured search, not a success.
            require(same(path(value, 0, 0, 0), path(p[0], 1)) and
                    same(path(value, 0, 0, 1), path(p[0], 2)) and
                    same(path(value, 0, 0, 2), path(p[1], 0, 0)),
                    "indexed execution replaces the returned relation/code")
        for value, calls in self.analyze("buildAction"):
            run, found = self.one(calls, "discover"), self.one(calls, "discovered")
            self.args(run, p[0]); self.args(found, path(run.result, 3))
            stored, validation, execution = (self.one(calls, k) for k in ("stored", "validate", "execution"))
            self.args(stored, path(run.result, 3)); self.args(validation, stored.result)
            self.args(execution, stored.result, validation.result)
            require(same(path(value, 0), path(found.result, 0)) and same(path(value, 1), execution.result),
                    "buildAction executed discovery but ignored its returned fields")
        for value, _ in self.analyze("selected"):
            require(same(value, path(p[0], 0, 0)), "selected not read from action.discovery.var")
        for value, calls in self.analyze("gates", ("selected",)):
            kernel = self.one(calls, "gateList")
            self.args(kernel, path(p[1], 0, 0), path(p[1], 1, 1), p[2], parameter_literal(0))
            require(same(value, kernel.result), "gates ignore the executed code")
        for value, calls in self.analyze("gateList", loop=True):
            if value.origin[0] != "loop":
                reverse = self.one(calls, "reverse"); self.args(reverse, p[3])
                require(same(value, reverse.result), "empty gate-list iteration not its accumulator")
                continue
            gate = self.one(calls, "codeGate")
            self.args(gate, p[0], path(p[2], 0, 1), p[1])
            require(same(path(value, 0), p[0]) and same(path(value, 1), p[1]) and
                    same(path(value, 2), path(p[2], 1)) and
                    same(path(value, 3, 0), gate.result) and same(path(value, 3, 1), p[3]),
                    "gate-list iteration drops the executed code/query or changes its tail")
        for value, calls in self.analyze("internalOutput", ("selected",)):
            gate, fire = self.one(calls, "codeGate"), self.one(calls, "gateFire")
            self.args(gate, path(p[0], 0, 0), path(p[0], 0, 0), path(p[0], 1, 1))
            self.args(fire, gate.result, parameter_literal(0))
            require(same(value, fire.result), "internal output not from returned code")
        for value, _ in self.analyze("producedSeed"):
            if value.origin[0] == "primitive" and value.origin[2] == "lean_unsigned_to_nat":
                require(value.origin[3] == (("literal", 0),), "nonzero empty-state seed")
            else:
                require(same(value, path(p[0], 1, 2, 0, 1, 0, 0)), "seed not from executed produced state")
        for value, calls in self.analyze("nextFront", ("selected",)):
            provenance, generation, seed = (self.one(calls, k) for k in ("prepend", "nextGeneration", "producedSeed"))
            self.args(provenance, path(p[1], 0, 0), path(p[0], 3))
            self.args(generation, path(p[0], 1)); self.args(seed, p[1])
            require(same(path(value, 1), generation.result) and same(path(value, 2), seed.result) and
                    same(path(value, 3), path(provenance.result, 0)), "successor loses produced seed/provenance")
        for value, calls in self.analyze("fromAction", ("selected",)):
            gates, fire, following = (self.one(calls, k) for k in ("gates", "fire", "nextFront"))
            self.args(gates, path(p[1], 0), p[2], p[0]); self.args(fire, gates.result, path(p[1], 1))
            self.args(following, path(p[1], 0), p[2])
            internal = self.one(calls, "internalOutput"); self.args(internal, p[2])
            require(same(path(value, 0), p[2]) and same(path(value, 1), gates.result) and
                    same(path(value, 2), fire.result) and
                    same(path(value, 3, 0), path(p[2], 0, 0)) and
                    any(same(v, internal.result) for v in path(value, 3).scalars.values()) and
                    same(path(value, 4, 0), following.result) and
                    same(path(value, 4, 1), fire.result), "production fields from unrelated action/output")
        for value, calls in self.analyze("produce"):
            action, production = self.one(calls, "buildAction"), self.one(calls, "fromAction")
            self.args(action, path(p[1], 0)); self.args(production, p[0], p[1], action.result)
            require(same(value, production.result), "produce discards its built action")
        for value, calls in self.analyze("install"):
            bank = self.one(calls, "routeBank"); self.args(bank, path(p[0], 2), path(p[0], 2))
            require(same(path(value, 0, 0), path(p[0], 4)) and
                    same(path(value, 0, 1), path(p[0], 1)) and
                    same(path(value, 0, 2), bank.result), "installation not from shared production")
        for value, calls in self.analyze("problem"):
            opening, reduction, lower = (self.one(calls, k) for k in ("opening", "normalizer", "lower"))
            self.args(opening, p[1], p[2]); self.args(reduction, p[1], path(opening.result, 0))
            self.args(lower, p[0], p[1], path(reduction.result, 1))
            require(all(same(path(value, i), c.result) for i, c in enumerate((opening, reduction, lower))),
                    "SAT production not from opening/reduction/configuration")
        for value, calls in self.analyze("problemNext"):
            lengths = [c for c in calls if c.name == self.names["length"]]
            require(len(lengths) == 1, "routing width ABI/length changed")
            self.args(lengths[0], path(p[0], 0, 0))
            require(same(path(value, 0), path(p[0], 1, 0)) and
                    same(path(value, 1, 0), lengths[0].result) and
                    same(path(value, 1, 1), path(p[0], 2)), "SAT successor/circuit not from reduction")
        # First reject unrelated computed arguments without executing their
        # arbitrary internal representation in the analyzer. This is only a
        # rejection preflight: acceptance ALWAYS requires the second pass,
        # which also expands potential writes through unknown helpers.
        for expand_writes in (False, True):
            for value, calls in self.analyze("advance", ("selected",),
                                             expand_unknown_writes=expand_writes):
                production, installation, problem, following = (
                    self.one(calls, k) for k in ("produce", "install", "problem", "problemNext"))
                self.args(production, p[0], path(p[1], 0, 0)); self.args(installation, production.result)
                self.args(problem, p[0], path(production.result, 0, 0, 0), path(p[1], 1, 0))
                self.args(following, problem.result)
                require(same(path(value, 0), path(installation.result, 0)) and
                        same(path(value, 1), following.result), "integrated successor from a different production")
        print("MACHINE_FLOW_OK: checked search-result/action, selector, shared installation and SAT successor")

    def runner(self, key, performKey, readKey, enabledKey, master=False):
        entry = self.names[key]
        flow = Flow(self.functions, self.params, self.shared["reachable"],
                    unfold=(entry,), terminals=set(self.names.values()), owners=self.owners or None)
        p = [parameter(i) for i in range(4)]
        saw_empty = saw_step = False
        for value, calls in flow.body(entry, p):
            reads = self.one(calls, readKey); self.args(reads, p[1])
            transitions = [c for c in calls if c.name == self.names[performKey]]
            recursions = [c for c in calls if c.name == entry]
            if not transitions:
                require(value.tag == 0 and not recursions and same(path(value, 0), reads.result),
                        key + ": invalid empty frame")
                saw_empty = True; continue
            transition, recurse = self.one(calls, performKey), unique(calls, entry)
            self.args(transition, p[0], p[1], path(p[2], 0))
            self.args(recurse, p[0], path(transition.result, 0), path(p[2], 1))
            enabled = self.one(calls, enabledKey)
            if master:
                self.args(enabled, p[0], path(p[1], 1), path(p[2], 0))
            else:
                self.args(enabled, p[0], path(p[2], 0))
            require(value.tag == 1 and same(path(value, 0), reads.result) and
                    same(path(value, 1), path(transition.result, 1)) and
                    same(path(value, 2), recurse.result) and
                    any(same(v, enabled.result) for v in value.scalars.values()),
                    key + ": observation/event/tail/admission not from the shared transition")
            saw_step = True
        require(saw_empty and saw_step, key + ": missing empty/nonempty path")
        print("MACHINE_RUNNER_FLOW_OK: " + key + ": one pair, same successor/event, actual request tail")


def parameter_literal(value):
    from integrated_machine_analysis import Datum
    return Datum(("literal", value))


def run_checks(functions, params, owners, shared):
    c = MachineChecks(functions, params, owners, shared)
    live = "ConstitutiveSearch.ReconfigurableMachine.LiveReduction."
    ce = live + "ConstitutiveExecution."
    cd = live + "ConstitutiveDiscovery."
    end = "ConstitutiveSearch.EndogenousDecomposition."
    master = "ConstitutiveSearch.MasterMachine."
    c.machine("advance", master + "advance", "MasterRuntime", 2)
    c.machine("produce", ce + "produce", "ConstitutiveLiveExecution", 2, "")
    c.machine("buildAction", ce + "buildAction", "ConstitutiveLiveExecution", 1, "")
    c.machine("fromAction", ce + "productionFromAction", "ConstitutiveLiveExecution", 3, "")
    c.machine("install", ce + "installProduction", "ConstitutiveLiveExecution", 1)
    c.machine("discover", cd + "discover", "ConstitutiveDiscovery", 1, "")
    c.machine("extraction", cd + "extraction", "ConstitutiveDiscovery", 1, "")
    c.machine("runExtracted", cd + "runExtracted", "ConstitutiveDiscovery", 2)
    c.endogenous("filter", end + "filterCandidatesByProvenance", "ConstitutiveFeedback", 2, "")
    c.endogenous("search", end + "exploreRecordedCandidates", "EndogenousDiscovery", 2)
    c.endogenous("discovered", end + "RecordedDiscoveryOutcome.discovered_x3f", "EndogenousDiscovery", 1)
    c.endogenous("stored", end + "RecordedDiscoveryOutcome.produceStoredSchedule", "StoredLocalSchedule", 1)
    c.endogenous("candidateEntry", end + "ProducedFlipCandidate.entry", "MeasuredDiscovery", 2)
    c.endogenous("validate", end + "validateStoredSchedule", "StoredLocalSchedule", 1)
    c.endogenous("validateSearch", end + "searchMeasuredRelation", "MeasuredDiscovery", 3)
    c.endogenous("execution", end + "MeasuredScheduleExecution.execution", "StoredLocalSchedule", 2)
    c.endogenous("indexedExecution", end + "executionFromMeasuredSearch", "StoredLocalSchedule", 2)
    c.machine("selected", live + "LocalAction.selected", "ScopedLiveAction", 1)
    c.machine("gates", live + "LocalAction.gates", "ScopedLiveAction", 3, "")
    c.machine("gateList", "List_mapTR_loop___at___00" + live.replace(".", "_") + "LocalAction_gates_spec__0", "ScopedLiveAction", 4)
    c.machine("internalOutput", live + "LocalAction.internalOutput", "ScopedLiveAction", 1)
    c.machine("codeGate", live + "codeGate", "ScopedLiveAction", 3)
    c.machine("nextFront", live + "nextFront", "ReducedLiveExecution", 2, "")
    c.machine("producedSeed", live + "LocalAction.producedSeed", "ScopedLiveAction", 1)
    c.machine("nextGeneration", live + "Generation.next", "LiveSearchFrontier", 1)
    c.endogenous("prepend", end + "prependProvenanceMeasured", "ConstitutiveFeedback", 2, "")
    c.machine("fire", "ConstitutiveSearch.ConnectedFabric.fire", "Fabric", 2, "")
    c.machine("gateFire", "ConstitutiveSearch.ConnectedFabric.Gate.fire", "Fabric", 2, "")
    c.machine("routeBank", "ConstitutiveSearch.ConnectedFabric.route", "Fabric", 2, "")
    c.machine("problem", master + "produceProblem", "MasterRuntime", 3)
    c.machine("problemNext", master + "ScopedProblemProduction.next", "MasterRuntime", 1)
    c.endogenous("opening", end + "VariableMaster.openFrontier", "VariableMasterExecution", 2)
    c.resolve("normalizer", "ConstitutiveSearch.SAT.normalizeGeneratedStructuralFrontierByFlip",
              "RelationalPerimeter/Computation/ConstitutiveSearch/SAT/StructuralGlobalContextRelation.c", 2)
    c.machine("lower", "ConstitutiveSearch.ConnectedFabric.lowerFrontier", "FrontierCircuit", 3)
    # Imported compiler library kernel, not a repository-owned producer. Its
    # exact external symbol/arity is the pinned Lean 4.33.1 boundary.
    c.names["length"] = "l_List_lengthTR___redArg"
    if c.names["length"] in functions:
        raise FlowError("FORM_UNSUPPORTED: repository shadows compiler list length")
    params = dict(params)
    params[c.names["length"]] = ["list"]
    c.names["reverse"] = "l_List_reverse___redArg"
    if c.names["reverse"] in functions:
        raise FlowError("FORM_UNSUPPORTED: repository shadows compiler list reverse")
    params[c.names["reverse"]] = ["list"]
    c.params = params
    c.machine("masterRun", master + "run", "MasterContract", 3)
    c.machine("masterPerform", master + "perform", "MasterContract", 3)
    c.machine("masterRead", master + "read", "MasterContract", 1)
    c.machine("masterEnabled", master + "enabled", "MasterContract", 3)
    c.machine("reducedRun", live + "runReduced", "ReducedLiveRunner", 3, "")
    c.machine("reducedPerform", live + "performReduced", "ReducedLiveContract", 3, "")
    c.machine("liveRead", live + "readRuntime", "ReducedLiveContract", 1)
    c.machine("liveEnabled", live + "enabledReduced", "ReducedLiveRunner", 2, "")
    c.machine("constitutiveRun", ce + "run", "ConstitutiveLiveExecution", 3, "")
    c.machine("constitutivePerform", ce + "perform", "ConstitutiveLiveExecution", 3, "")
    c.check()
    for args in (("masterRun", "masterPerform", "masterRead", "masterEnabled", True),
                 ("reducedRun", "reducedPerform", "liveRead", "liveEnabled"),
                 ("constitutiveRun", "constitutivePerform", "liveRead", "liveEnabled")):
        c.runner(*args)
    return c


def compiled_fixture_tests(c):
    """Frozen in-memory IR checks, not Lean mutations or benchmark results.

    The normal gate invokes these. Real coherent Lean mutation runs are a
    separate reproduction obligation; no failure of parsing counts here.
    """
    import contextlib
    import io
    import re
    fixtures = []

    def changed(key, pattern, replacement, reason):
        name = c.names[key]
        body, count = re.subn(pattern, replacement, c.functions[name])
        if count != 1:
            raise FlowError("FORM_UNSUPPORTED: compiled fixture no longer matches " + key)
        fixtures.append((name, body, reason))

    changed("advance", re.escape(c.names["selected"]) + r"\([^)]*\)",
            "lean_unsigned_to_nat(12u)", "wrong argument origin")
    changed("buildAction", r"(lean_ctor_set\([^,]+, 0, )\w+(\);)",
            r"\g<1>lean_box(0)\g<2>", "ignored its returned fields")
    changed("execution", r"(lean_ctor_set\([^,]+, 1, )\w+(\);)",
            r"\g<1>lean_box(0)\g<2>", "executed code not from validated search")
    changed("problem", re.escape(c.names["lower"]) + r"\((\w+), (\w+), (\w+)\)",
            c.names["lower"] + r"(\1, \2, lean_box(0))", "wrong argument origin")
    for name, body, reason in fixtures:
        mutant = dict(c.functions); mutant[name] = body
        probe = MachineChecks(mutant, c.params, c.owners, c.shared); probe.names = dict(c.names)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                probe.check()
        except FlowError as error:
            if not str(error).startswith("PROVENANCE_INCORRECT:") or reason not in str(error):
                raise FlowError("Wrong compiled-fixture rejection: " + str(error)) from error
        else:
            raise FlowError("Compiled fixture incorrectly accepted " + name)
    print("MACHINE_COMPILED_FIXTURES_OK: predicted selector, ignored discovery/code, unrelated SAT circuit rejected")

    # Exact compiled runner fixture, with a declaration and ABI entry for the
    # helper. A missing symbol/arity or any unrelated error is not a rejection.
    entry, perform = c.names["masterRun"], c.names["masterPerform"]
    pattern = r"(\b(\w+)\s*=\s*" + re.escape(perform) + r"\([^;]+\);)"
    changed_body, count = re.subn(pattern, r"\1 l_machine_fixture_write(\2);", c.functions[entry])
    if count != 1:
        raise FlowError("FORM_UNSUPPORTED: runner helper fixture no longer matches")
    mutant = dict(c.functions)
    mutant[entry] = changed_body
    mutant["l_machine_fixture_write"] = """
lean_object* alias; alias = pair;
lean_dec(lean_ctor_get(alias, 1));
lean_ctor_set(alias, 1, lean_box(3)); return pair;
"""
    params = dict(c.params); params["l_machine_fixture_write"] = ["pair"]
    owners = dict(c.owners); owners["l_machine_fixture_write"] = {"fixture.c"}
    probe = MachineChecks(mutant, params, owners, c.shared); probe.names = dict(c.names)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            probe.runner("masterRun", "masterPerform", "masterRead", "masterEnabled", True)
    except FlowError as error:
        if str(error) != "FORM_UNSUPPORTED: helper mutates borrowed input lean_ctor_set":
            raise FlowError("Wrong compiled runner-helper rejection: " + str(error)) from error
    else:
        raise FlowError("Compiled runner fixture accepted helper replacing event with refused")
    print("MACHINE_COMPILED_HELPER_FIXTURE_OK: borrowed transition event overwrite rejected")

    # A large writer is invisible to the rejection-only preflight. It MUST be
    # rejected by the mandatory heap-effect pass, even with an ignored return.
    entry, produce = c.names["advance"], c.names["produce"]
    pattern = r"(\b(\w+)\s*=\s*" + re.escape(produce) + r"\([^;]+\);)"
    changed_body, count = re.subn(pattern, r"\1 l_machine_fixture_large_write(\2);", c.functions[entry])
    if count != 1:
        raise FlowError("FORM_UNSUPPORTED: large-helper fixture no longer matches")
    mutant = dict(c.functions); mutant[entry] = changed_body
    mutant["l_machine_fixture_large_write"] = (
        "lean_inc(pair); lean_dec(pair); " * 100 +
        "lean_ctor_set(pair,0,lean_box(3)); return pair;")
    params = dict(c.params); params["l_machine_fixture_large_write"] = ["pair"]
    owners = dict(c.owners); owners["l_machine_fixture_large_write"] = {"fixture.c"}
    probe = MachineChecks(mutant, params, owners, c.shared); probe.names = dict(c.names)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            probe.check()
    except FlowError as error:
        if str(error) != "FORM_UNSUPPORTED: helper mutates borrowed input lean_ctor_set":
            raise FlowError("Wrong large-helper rejection: " + str(error)) from error
    else:
        raise FlowError("Compiled fixture accepted large writer after the provenance preflight")
    print("MACHINE_COMPILED_EFFECT_PASS_OK: provenance preflight cannot replace heap-effect check")


def self_test_checks(parser, parameters, shared):
    """Paired-runner fixtures protect data provenance, not just call counts."""
    declarations = '''LEAN_EXPORT lean_object* l_perform(lean_object* s, lean_object* m, lean_object* q){return m;}
LEAN_EXPORT lean_object* l_read(lean_object* m){return m;}
LEAN_EXPORT uint8_t l_enabled(lean_object* s, lean_object* q){return 1;}
LEAN_EXPORT lean_object* l_helper(lean_object* s, lean_object* m, lean_object* q){return l_perform(s,m,q);}
LEAN_EXPORT lean_object* l_pair_copy(lean_object* p){
lean_object* out; out=lean_alloc_ctor(0,2,0);
lean_ctor_set(out,0,lean_ctor_get(p,0)); lean_ctor_set(out,1,lean_ctor_get(p,1)); return out;
}
'''
    runner = '''LEAN_EXPORT lean_object* l_run(lean_object* s, lean_object* m, lean_object* qs){
lean_object* out; lean_object* view; view = l_read(m);
if (lean_obj_tag(qs) == 0) {
 out = lean_alloc_ctor(0,1,0); lean_ctor_set(out,0,view); return out;
} else {
 lean_object* q; lean_object* rest; lean_object* pair; lean_object* next;
 lean_object* event; lean_object* tail; uint8_t allowed;
 q=lean_ctor_get(qs,0); rest=lean_ctor_get(qs,1);
 allowed=l_enabled(s,q); pair=l_perform(s,m,q);
 next=lean_ctor_get(pair,0); event=lean_ctor_get(pair,1);
 tail=l_run(s,next,rest); out=lean_alloc_ctor(1,3,1);
 lean_ctor_set(out,0,view); lean_ctor_set(out,1,event); lean_ctor_set(out,2,tail);
 lean_ctor_set_uint8(out,sizeof(void*)*3,allowed); return out;
}}
'''
    cases = (
        ("shared", runner, True),
        ("shared-helper", runner.replace("pair=l_perform(s,m,q)", "pair=l_helper(s,m,q)"), True),
        ("fresh-helper-copy", runner.replace("next=lean_ctor_get(pair,0)",
            "pair=l_pair_copy(pair); next=lean_ctor_get(pair,0)"), True),
        ("wrong-successor", runner.replace("tail=l_run(s,next,rest)", "tail=l_run(s,m,rest)"), False),
        ("wrong-tail", runner.replace("tail=l_run(s,next,rest)", "tail=l_run(s,next,qs)"), False),
        ("wrong-request", runner.replace("pair=l_perform(s,m,q)", "pair=l_perform(s,m,qs)"), False),
        ("second-event", runner.replace("event=lean_ctor_get(pair,1)",
            "event=lean_ctor_get(l_perform(s,m,q),1)"), False),
    )
    for label, source, expected in cases:
        text = declarations + source
        c = MachineChecks(parser(text), parameters([text]), {}, shared)
        c.names = dict(run="l_run", perform="l_perform", read="l_read", enabled="l_enabled")
        try:
            c.runner("run", "perform", "read", "enabled")
        except FlowError as error:
            if expected or not str(error).startswith("PROVENANCE_INCORRECT:"):
                raise
        else:
            if not expected:
                raise FlowError("Runner self-test accepted " + label)
    print("MACHINE_RUNNER_SELFTEST_OK: helper sharing and wrong event/successor/request/tail rejected")
