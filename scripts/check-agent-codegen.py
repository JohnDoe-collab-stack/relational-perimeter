#!/usr/bin/env python3
"""Compiled-agent dependency and sharing checks, not a cost/heap theorem.

Reuse the existing local C-IR parser. No runtime scientific dependency is added.
"""
from pathlib import Path
import re
import runpy
import sys
from unified_codegen_analysis import Analysis, Value, parameters, split_arguments

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
shared = runpy.run_path(str(ROOT / "scripts/check-unified-codegen.py"))


class AgentAnalysis(Analysis):
    """One structural unfolding, with explicitly named recursive tails cut.

    This does not bound a whole advance/executeAll. The Lean recursion and
    iteration-count laws are checked separately. New helper cycles fail closed.
    """
    def __init__(self, *args, unfolds=(), boundaries=(), **kwargs):
        super().__init__(*args, **kwargs)
        self.unfolds, self.boundaries = set(unfolds), set(boundaries)

    def run(self, name, arguments):
        if name in self.boundaries:
            return Value(), 0, 0
        if name in self.unfolds and any(frame[0] == name for frame in self.stack):
            return Value(), 0, 0
        return super().run(name, arguments)

    def global_value(self, name):
        body = self.functions.get(name, '')
        fields = re.search(r'\.m_objs\s*=\s*\{(.*?)\}', body, re.S)
        if fields and '.m_fun' not in body:
            result = {}
            for index, item in enumerate(split_arguments(fields[1])):
                symbols = re.findall(r'\b(?:l|lp)_\w+\b', item)
                if len(symbols) == 1 and symbols[0] in self.functions:
                    result[index] = self.global_value(symbols[0])
                elif not symbols and re.fullmatch(r'[()\s\d<>|*a-z_]+', item):
                    # A statically boxed immediate has no closure or callee.
                    if 'lean_object' not in item or 'size_t' not in item or '<< 1' not in item:
                        raise ValueError('Unresolved static immediate: ' + item)
                    result[index] = Value()
                else:
                    raise ValueError('Unresolved static producer field: ' + item)
            return Value(fields=result)
        return super().global_value(name)


def applications(functions, compiled_parameters, entry, target, maximum, *, unfolds=(), boundaries=()):
    # Remove only generated casts around a named static object, preserving its
    # identity and all applications. This is not a producer boundary.
    normalized = {name: re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)', r'\1', body)
                  for name, body in functions.items()}
    analysis = AgentAnalysis(normalized, compiled_parameters, shared['reachable'], target=target,
                             unfolds=unfolds, boundaries=boundaries)
    _, low, high = analysis.run(entry, [Value() for _ in compiled_parameters[entry]])
    if high != maximum:
        raise ValueError(f'{entry}: expected maximum {maximum} applications of {target}, found [{low},{high}]')
    print(f'AGENT_APPLICATIONS_OK {entry}: {target}=[{low},{high}]; explicit unfolding scope')


def recursive_tail_applications(functions, compiled_parameters, entry):
    # Unfold the current node under a fresh analysis-only name, then count
    # applications of the real recursive tail, including through helpers.
    alias = entry + '__one_unfolding_check'
    if alias in functions:
        raise ValueError('Analysis entry alias already exists')
    augmented, params = dict(functions), dict(compiled_parameters)
    augmented[alias], params[alias] = functions[entry], compiled_parameters[entry]
    applications(augmented, params, alias, entry, 1)


def bodies_with_objects(text):
    result = shared["bodies"](text)
    clean = shared["LITERALS"].sub(lambda match: " " * len(match.group()), text)
    # Producers can be static constructor objects containing operation
    # closures. Following only closure objects misses this intervening record.
    for match in re.finditer(
            r"(?:static|LEAN_EXPORT) const lean_(?:closure|ctor)_object "
            r"((?:l|lp)_\w+)_value\s*=\s*(\{.*?\});", clean, re.S):
        result[match[1] + "_value"] = match[2]
        result[match[1]] = match[2]
    for match in re.finditer(
            r"(?:static|LEAN_EXPORT) const lean_object\* ((?:l|lp)_\w+)\s*=\s*([^;]+);", clean):
        result[match[1]] = match[2]
    return result


def self_test():
    """Finite C-IR regressions of this checker, not runtime experiments."""
    base = 'LEAN_EXPORT lean_object* l_target(lean_object* x){ return x; }\n'
    variants = (
        ('shared-result', '''LEAN_EXPORT lean_object* l_entry(lean_object* x){
          lean_object* y; lean_object* pair;
          y = l_target(x); pair = lean_alloc_ctor(0, 2, 0);
          lean_ctor_set(pair, 0, y); lean_ctor_set(pair, 1, y); return pair;
        }''', (1, 1)),
        ('hidden-double-call', '''LEAN_EXPORT lean_object* l_helper(lean_object* x){
          lean_object* first; first = l_target(x); return l_target(first);
        }
        LEAN_EXPORT lean_object* l_entry(lean_object* x){ return l_helper(x); }''', (2, 2)),
        ('same-closure-twice', '''LEAN_EXPORT lean_object* l_helper(lean_object* f, lean_object* x){
          lean_object* first; first = lean_apply_1(f, x); return lean_apply_1(f, first);
        }
        LEAN_EXPORT lean_object* l_entry(lean_object* x){
          lean_object* f; f = lean_alloc_closure((void*)l_target, 1, 0); return l_helper(f, x);
        }''', (2, 2)),
    )
    for name, body, expected in variants:
        text = '\n'.join(line.lstrip() for line in (base + body).splitlines())
        functions, params = bodies_with_objects(text), parameters([text])
        _, low, high = AgentAnalysis(functions, params, shared['reachable'], target='l_target').run(
            'l_entry', [Value()])
        if (low, high) != expected:
            raise ValueError(f'{name}: expected {expected}, found {(low, high)}')
    print('AGENT_ANALYSIS_SELFTEST_OK: sharing, hidden helper and repeated closure application')


def main():
    self_test()
    probe = bodies_with_objects("""
static const lean_closure_object l_operation_value = {.m_fun = (void*)l_bad};
static const lean_ctor_object l_packet_value = {.m_objs = {&l_operation_value}};
LEAN_EXPORT const lean_object* l_producer = (const lean_object*)&l_packet_value;
LEAN_EXPORT lean_object* l_entry(){ return l_producer; }
LEAN_EXPORT lean_object* l_bad(){ return 0; }
""")
    if "l_bad" not in shared["reachable"](probe, "l_entry"):
        raise ValueError("Static producer/constructor/closure reachability self-test failed")
    functions = {}
    texts = []
    for path in sorted((ROOT / ".lake/build/ir").rglob("*.c")):
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        functions.update(bodies_with_objects(text))
    compiled_parameters = parameters(texts)
    select, absent, calls = (shared[name] for name in ("select", "absent", "calls"))
    executor = select(functions, "Agent_executeRequests")
    request = select(functions, "Agent_executeInput")
    produced = select(functions, "Agent_executeProducedInput")
    step = select(functions, "Agent_step")
    worker = select(functions, "Agent_runSteps")
    decision = select(functions, "Agent_decideReply")
    session = select(functions, "Agent_Session_execute")
    session_produce = select(functions, "Agent_Session_produce")
    session_all = select(functions, "Agent_Session_executeAll")
    of_master = select(functions, "Agent_Session_ofMaster")
    initialize = select(functions, "Agent_initializeAgent")
    public_agent = select(functions, "Agent_publicAgent")
    prepared_memory = select(functions, "Agent_Prepared_memory")
    forbidden = ["Agent_source", "Agent_History_", "MasterResources_", "UnifiedMaster_",
                 "Agent_normalizedRegister", "Agent_start", "Agent_prepare", "Agent_encodeSelection",
                 "Agent_decodeSelection", "ProducedContinuation_Source_", "profileFrontier",
                 "roleProfileFrontier", "roleOccurrenceProfileFrontier",
                 "roleProfileFiniteCarrier", "enumerateRoleOccurrenceProfiles"]
    # The unchanged live engine builds a two-source local output-image
    # readout *after* executing the action. It is not the global role-profile
    # frontier and does not select discovery. Check the discovery entry
    # separately, with the stricter image/readout exclusion.
    for entry in (session, session_produce, session_all, executor, request, produced, worker, step, decision):
        absent(functions, entry, forbidden)
    # Scientific interpretation must read the rich support; it may not call
    # the projected responder. This graph check complements formation types,
    # and is not an observational non-equivalence theorem.
    for entry in (select(functions, 'Agent_sourceProduced'), select(functions, 'Agent_sourcePerform')):
        absent(functions, entry, ['Agent_project', 'Agent_executeInput', 'Agent_executeProducedInput',
                                  'Agent_performCertified'])
    support_read = select(functions, 'Resources_Support_read___redArg')
    for entry in (select(functions, 'Agent_MaterialReading_values___redArg'),
                  select(functions, 'Agent_RegisterRealization_materialRegister___redArg')):
        if support_read not in shared['reachable'](functions, entry):
            raise ValueError('Rich reading no longer reaches the actual support read: ' + entry)
        print('AGENT_RICH_READ_OK ' + entry + ': typed support read, not a projected value list')
    calls(functions, executor, "Agent_executeInput", 1)
    calls(functions, request, "Agent_executeProducedInput", 1)
    calls(functions, worker, "Agent_step", 1)
    calls(functions, step, "LiveContinuation_produce", 1)
    calls(functions, worker, "Agent_runSteps", 1)
    discovery = select(functions, "runThreadedNextDiscovery")
    absent(functions, discovery, forbidden + ["_imageRegime", "_outputRegime", "_frontier"])
    operation = select(functions, "Agent_interactionProducer___lam__1")
    calls(functions, operation, "Agent_performCertified", 1)
    shared["producer_routes"](functions, produced,
        select(functions, "Agent_performCertified"), 1)
    # Initialization may construct its master exactly once; resumption above
    # must never call it. Count the route to the established public factory.
    prepare = select(functions, "Agent_prepare")
    master = select(functions, "UnifiedMaster_publicInstance")
    live = select(functions, "LiveContinuation_produce")
    for entry in (prepare, initialize, public_agent):
        applications(functions, compiled_parameters, entry, master, 1)
    for entry in (of_master, prepared_memory):
        absent(functions, entry, [], exact=(master, prepare))
    for entry, target in ((session, request), (session_produce, produced),
                          (session_all, executor), (request, produced),
                          (produced, select(functions, 'Agent_performCertified')), (step, live)):
        applications(functions, compiled_parameters, entry, target, 1)
    for entry, target in ((executor, request), (worker, step)):
        applications(functions, compiled_parameters, entry, target, 1, unfolds=(entry,))
        recursive_tail_applications(functions, compiled_parameters, entry)
    # The one authorized request route is checked above. No live production
    # may be added beside it by a wrapper or a non-inlined helper.
    for entry, boundary in ((session, request), (session_produce, produced), (session_all, executor)):
        applications(functions, compiled_parameters, entry, live, 0, boundaries=(boundary,))
    # L3/F1: each material branch consumes the exact current checked state and
    # its certificate witnesses in one state-indexed reconfiguration/action
    # producer.  That producer executes one ReconfiguredActionEffect, which
    # stores the action result and therefore cannot reconstruct a detached
    # effect.  The raw reconfiguration must itself call `reconfigure`, so the
    # current system and its exact run reach the compiled installation path.
    learned_producer = select(functions, "NeuralAgent_produceLearnedTransitionData___redArg")
    learned_aligned_action = select(functions,
        "NeuralAgent_executeLearnedAlignedReconfigurationFromState")
    learned_extended_action = select(functions,
        "NeuralAgent_executeLearnedExtendedReconfigurationFromState")
    learned_aligned_raw = select(functions,
        "NeuralAgent_learnedAlignedRawReconfigurationForState")
    learned_extended_raw = select(functions,
        "NeuralAgent_learnedExtendedRawReconfigurationForState")
    reconfigured_action = select(functions,
        "NeuralAgent_executeReconfiguredAction___redArg")
    learned_target = select(functions,
        "NeuralAgent_learnedProducedTransitionTarget___redArg")
    calls(functions, learned_producer,
        "NeuralAgent_executeLearnedAlignedReconfigurationFromState", 1)
    calls(functions, learned_producer,
        "NeuralAgent_executeLearnedExtendedReconfigurationFromState", 1)
    calls(functions, learned_aligned_action,
        "NeuralAgent_executeReconfiguredAction___redArg", 1)
    calls(functions, learned_extended_action,
        "NeuralAgent_executeReconfiguredAction___redArg", 1)
    calls(functions, learned_aligned_raw, "NeuralAgent_reconfigure___redArg", 1)
    calls(functions, learned_extended_raw, "NeuralAgent_reconfigure___redArg", 1)
    calls(functions, reconfigured_action, "Agent_executeProducedInput", 1)
    absent(functions, learned_target,
        ["executeLearnedAlignedReconfigurationFromState",
         "executeLearnedExtendedReconfigurationFromState",
         "executeReconfiguredAction", "Agent_executeProducedInput"])
    print("AGENT_LEARNED_SHARING_OK: each material branch consumes its current state in one reconfiguration/action/effect occurrence; the successor only projects that shared occurrence")
    # F2: the successive runtime route must execute the decoder-produced
    # analysis and build the installed checked update from that analysis.  A
    # return of the separately named canonical checked update would recreate
    # the bypass found by the audit even if extensional equality tests passed.
    successive_decoded = select(functions,
        "NeuralAgent_checkDecodedLearnedExtendedSerializedUpdate___redArg")
    successive_serialized = select(functions,
        "NeuralAgent_checkLearnedExtendedSerializedUpdate")
    successive_runtime = select(functions,
        "NeuralAgent_checkDecodedLearnedRuntimeUpdateAtCurrent___redArg")
    calls(functions, successive_decoded,
        "NeuralAgent_analyzeDecodedLearnedSuccessiveUpdate___redArg", 1)
    calls(functions, successive_decoded,
        "NeuralAgent_LearnedSuccessiveEngineAnalysis_target___redArg", 1)
    calls(functions, successive_decoded,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg", 1)
    calls(functions, successive_serialized,
        "NeuralAgent_checkDecodedLearnedExtendedSerializedUpdate___redArg", 1)
    calls(functions, successive_runtime,
        "NeuralAgent_checkDecodedLearnedExtendedSerializedUpdate___redArg", 1)
    absent(functions, successive_decoded, ["learnedExtendedCheckedUpdate"])
    absent(functions, successive_serialized, ["learnedExtendedCheckedUpdate"])
    print("AGENT_SUCCESSIVE_RUNTIME_OK: decoded update -> executed successive analysis -> transported/recomputed target -> installed checked update; no canonical-update bypass")
    # F3: an admitted ordinary continuation must execute the reduced future
    # contract, while a contract change must pass through the post-forgetting
    # analyzer and build the checked successor from that returned analysis.
    # These are distinct compiled routes; neither may substitute a named
    # canonical successor or treat the continuation as a contract update.
    post_continuation = select(functions,
        "NeuralAgent_submitLearnedPostForgettingContinuation")
    post_runtime = select(functions,
        "NeuralAgent_checkLearnedPostForgettingRuntimeUpdate___redArg")
    post_closed_change = select(functions,
        "NeuralAgent_closeLearnedPostForgettingContractChange___redArg")
    calls(functions, post_continuation,
        "NeuralAgent_checkLearnedPostForgettingIncremental", 1)
    calls(functions, post_continuation,
        "NeuralAgent_executePostForgettingContinuation___redArg", 1)
    calls(functions, post_runtime,
        "NeuralAgent_analyzeLearnedPostForgettingIncrementally", 1)
    calls(functions, post_runtime,
        "NeuralAgent_closeLearnedPostForgettingContractChange___redArg", 1)
    calls(functions, post_closed_change,
        "NeuralAgent_JustifiedPostForgettingTransition_transportedPersistent___redArg", 1)
    calls(functions, post_closed_change,
        "NeuralAgent_JustifiedPostForgettingTransition_rechecked___redArg", 1)
    calls(functions, post_closed_change,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg", 1)
    absent(functions, post_runtime,
        ["learnedExtendedCheckedUpdate", "learnedPostForgettingExtendedRuntime"])
    print("AGENT_POST_FORGETTING_RUNTIME_OK: reduced-memory continuation is executed; contract change consumes its persistent transport and authorization recheck before building and installing the returned checked update; no canonical-successor bypass")
    # L6: the installed incremental successor must be assembled through the
    # unique fragment constructor whose structural field is the calculated
    # transport/recompute assembly.  Neither that constructor nor the scaling
    # incremental analyzer may call a complete checker as an oracle.
    incremental_builder = select(functions,
        "NeuralAgent_buildIncrementalCheckedUpdate___redArg")
    fragment_assembly = select(functions,
        "NeuralAgent_IncrementalTargetAnalysis_fragments___redArg")
    calls(functions, incremental_builder,
        "NeuralAgent_IncrementalTargetAnalysis_fragments___redArg", 1)
    absent(functions, fragment_assembly,
        ["checkInitial", "checkFullUpdate", "FullRecheck", "certifyFragments"])
    structural_assembly = select(functions,
        "NeuralAgent_calculateIncrementalStructuralAssembly")
    direct_recomputation = select(functions,
        "NeuralAgent_recomputeAffectedStructuralObservations")
    absent(functions, structural_assembly,
        ["stableStructuralObservationSnapshot", "PreCertificateConstitutiveGraph_targetObservations"])
    absent(functions, direct_recomputation,
        ["stableStructuralObservationSnapshot"])
    scaling_incremental = select(functions,
        "NeuralAgent_analyzeScalingIncrementalUpdate")
    absent(functions, scaling_incremental,
        ["checkInitial", "checkFullUpdate", "FullRecheck", "certifyFragments"])
    print("AGENT_INCREMENTAL_ASSEMBLY_OK: installed certificate consumes direct transport/recomputation; no regenerated target snapshot or complete-check oracle")
    # F4: the successor campaign must produce one action from the exact source,
    # pass that same produced object to the effect constructor, and build the
    # successor from that effect.  Re-executing an extensionally equal action
    # here would hide an occurrence substitution behind value equality.
    causal_producer = select(functions,
        "NeuralAgent_produceCausalScalingTransition")
    causal_action = select(functions,
        "NeuralAgent_causalScalingAction")
    causal_target_analysis = select(functions,
        "NeuralAgent_causalScalingIncrementalTargetAnalysis")
    calls(functions, causal_producer, "NeuralAgent_causalScalingAction", 1)
    calls(functions, causal_action,
        "NeuralAgent_causalScalingTransitionRequest___redArg", 1)
    calls(functions, causal_action,
        "Agent_executeProducedInput", 1)
    calls(functions, causal_producer,
        "NeuralAgent_causalScalingEffectOfAction___redArg", 1)
    absent(functions, causal_producer, [], exact=(
        select(functions, "NeuralAgent_causalScalingEffect"),
        select(functions, "NeuralAgent_produceScalingEffect"),
    ))
    calls(functions, causal_target_analysis,
        "NeuralAgent_ExecutedTransitionProduction_targetState___redArg", 1)
    causal_trace = select(functions,
        "NeuralAgent_CompiledCausalCompletePropertyScaling_runTrace")
    calls(functions, causal_trace,
        "NeuralAgent_checkGenericIncrementalUpdate___redArg", 1)
    calls(functions, causal_trace,
        "NeuralAgent_checkFullUpdate___redArg", 1)
    print("AGENT_CAUSAL_SCALING_OK: one source-indexed action occurrence is consumed by one effect occurrence and the produced successor")
    print("AGENT_CAUSAL_SCALING_PAIRED_OK: the compiled runner executes one incremental check and one independent full recheck on each current state before continuing from the checked successor")
    print("AGENT_CODEGEN_OK: actual live step, one request head, learned sharing and incremental assembly, no rich archive or extensive enumeration")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"AGENT_CODEGEN_FAILED: {error}", file=sys.stderr)
        sys.exit(1)
