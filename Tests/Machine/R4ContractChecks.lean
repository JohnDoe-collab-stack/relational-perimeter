import RelationalPerimeter.Computation.Machine.LiveRoot
import Tests.Machine.ReducedLiveRunnerChecks

/-! Client obligations pin the domains, not just the names of the producer theorems.
This module adds no runtime field or callback. -/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.ReconfigurableMachine.R4Checks
open ConnectedFabric ContinuationSignatures LiveReduction EndogenousDecomposition SAT

theorem exact_all_sources (scope : Scope) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests =
      runReduced (projectMemory scope memory) requests :=
  executed_all_futures_exact scope memory requests

theorem minimal_without_fixed_live (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) :
    projectMemory scope one = projectMemory scope two ↔
      FutureEquivalent (runtimeContract scope) one two :=
  minimal_projection_iff_futures scope first second

theorem any_realization_type_three (scope : Scope) {Other : Type 3}
    (realization : ExactRealization (runtimeContract scope) Other) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : realization.project one = realization.project two) :
    projectMemory scope one = projectMemory scope two :=
  any_exact_realization_retains_projection scope realization first second same

theorem successor_all_sources (scope : Scope) (memory : LiveContinuation.Memory) :
    (produceReduced (projectLive scope memory)).next =
      projectLive scope (LiveContinuation.produce memory).next :=
  produced_next_exact scope memory

theorem decision_all_sources (scope : Scope) (memory : LiveContinuation.Memory) :
    (produceReduced (projectLive scope memory)).decision =
      EndogenousDecomposition.executedBranchDecision (LiveContinuation.produce memory).built.stage :=
  produced_decision_exact scope memory

theorem runner_all_runtime {scope : Scope} (memory : Runtime scope)
    (requests : List (ULift.{3} Request)) :
    runReduced memory requests = (contract scope).outcome memory requests :=
  runReduced_exact_outcome memory requests

theorem refusal_continues {scope : Scope} (memory : Runtime scope)
    (left right : Signals) (wrong : pulseFits scope left right = false)
    (rest : List (ULift.{3} Request)) :
    runReduced memory (⟨.pulse left right⟩ :: rest) =
      .step (readRuntime memory) false .refused (runReduced memory rest) :=
  runReduced_refused memory left right wrong rest

theorem empty_and_repeated (query : Nat) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    ((runtimeContract []).outcome memory requests = runReduced (projectMemory [] memory) requests) ∧
    ((runtimeContract [Channel.singleton query, Channel.singleton query]).outcome memory requests =
      runReduced (projectMemory [Channel.singleton query, Channel.singleton query] memory) requests) :=
  ⟨runReduced_empty_scope memory requests, runReduced_repeated_scope query memory requests⟩

theorem lowering_arbitrary_code {root : Cnf} (scope : Scope) (selected : Var)
    {source target : GeneratedStructuralBranchContext root}
    (code : TransportCode (GeneratedStructuralFlipAtRelation selected) source target)
    (input : GeneratedStructuralBranchContinuation source) :
    fire (scopeCode scope selected code) (sense scope input.1) =
      sense scope ((code.eval (generatedStructuralFlipAtAction root selected)).map input).1 :=
  scopeCode_exact scope selected code input

end ConstitutiveSearch.ReconfigurableMachine.R4Checks
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.exact_all_sources
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.minimal_without_fixed_live
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.any_realization_type_three
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.successor_all_sources
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.decision_all_sources
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.runner_all_runtime
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.refusal_continues
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.empty_and_repeated
#print axioms ConstitutiveSearch.ReconfigurableMachine.R4Checks.lowering_arbitrary_code
/- AXIOM_AUDIT_END -/
