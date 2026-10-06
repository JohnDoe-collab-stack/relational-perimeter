import RelationalPerimeter.Computation.Machine.ScopedLiveAction

/-! Direct live execution. Only the current constituted frontier and finite
interface values persist. No source assignment or measured reader is restored. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open SAT EndogenousDecomposition ConnectedFabric

structure Live (scope : Scope) where
  front : Frontier
  values : Signals
  valuesLength : values.length = scope.length

def projectLive (scope : Scope) (live : LiveContinuation.Memory) : Live scope :=
  ⟨projectFront live, sense scope live.assignment.assignment, sensed_length scope _⟩

theorem frontier_ext (one two : Frontier) (depth : one.depth = two.depth)
    (generation : HEq one.generation two.generation)
    (seed : one.searchSeed = two.searchSeed) (provenance : one.provenance = two.provenance) :
    one = two := by
  cases one; cases two
  cases depth
  have same := eq_of_heq generation
  cases same; cases seed; cases provenance
  rfl

theorem live_ext {scope : Scope} (one two : Live scope)
    (front : one.front = two.front) (values : one.values = two.values) : one = two := by
  cases one; cases two; cases front; cases values; rfl

def nextFront (front : Frontier) (action : LocalAction front) : Frontier :=
  { depth := front.depth + 1
    generation := front.generation.next
    searchSeed := action.producedSeed
    seedExact := by
      rw [action.producedSeed_exact, action.selected_exact]
      exact (stageSelectedVar_eq_nextSearchIndex (front.depth + 1)).trans
        (generatedSearchSeed_exact front.generation.next.full).symm
    provenance := (prependProvenanceMeasured action.selected front.provenance).output
    fresh := by
      intro portVar member
      cases member with
      | head => rw [action.selected_exact]; exact stageSelectedVar_strict (Nat.lt_succ_self _)
      | tail _ member =>
          exact Nat.lt_trans (front.fresh portVar member)
            (stageSelectedVar_strict (Nat.lt_succ_self _)) }

structure Production {scope : Scope} (live : Live scope) where
  action : LocalAction live.front
  connections : List Gate
  connectionsExact : connections = action.gates scope
  output : Signals
  outputExact : output = fire connections live.values
  decision : StructuralBranchDecision
  decisionExact : decision = ⟨action.selected, action.internalOutput⟩
  next : Live scope
  nextFrontExact : next.front = nextFront live.front action
  nextValuesExact : next.values = output

def produceReduced {scope : Scope} (live : Live scope) : Production live :=
  let action := buildAction live.front
  let connections := action.gates scope
  let output := fire connections live.values
  let decision : StructuralBranchDecision := ⟨action.selected, action.internalOutput⟩
  have length : output.length = scope.length := by
    have gateLength : connections.length = scope.length := by
      change (scopeCode scope _ _).length = scope.length
      exact scopeCode_length scope _ _
    exact (fired_length connections live.values (gateLength.trans live.valuesLength.symm)).trans gateLength
  ⟨action, connections, rfl, output, rfl, decision, rfl,
    ⟨nextFront live.front action, output, length⟩, rfl, rfl⟩

theorem action_matches_source (live : LiveContinuation.Memory) :
    (buildAction (projectFront live)).discovery = (LiveContinuation.produce live).built.stage.discovery := by
  rw [LocalAction.discovery_exact]
  exact (Option.some.inj ((LiveContinuation.produce live).built.stage.discoveryExact.symm.trans
    (canonicalStageDiscovery_found _))).symm

theorem produced_connections_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (produceReduced (projectLive scope live)).connections = compile scope (LiveContinuation.produce live) := by
  rw [(produceReduced _).connectionsExact, LocalAction.gates_exact]
  change configure scope (buildAction (projectFront live)).discovery.var = _
  rw [action_matches_source]
  rfl

theorem produced_values_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (produceReduced (projectLive scope live)).output =
      sense scope (LiveContinuation.produce live).built.stage.next.assignment := by
  rw [(produceReduced _).outputExact, produced_connections_exact]
  change fire (configure scope _) (sense scope live.assignment.assignment) = _
  rw [configure_exact, sequentialStage_next_from_input]
  rfl

theorem produced_decision_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (produceReduced (projectLive scope live)).decision =
      executedBranchDecision (LiveContinuation.produce live).built.stage := by
  rw [(produceReduced _).decisionExact, LocalAction.internalOutput_exact,
    LocalAction.selected_exact, executedBranchDecision_eq_selected_true]
  rfl

theorem produced_seed_exact (live : LiveContinuation.Memory) :
    (buildAction (projectFront live)).producedSeed =
      executedProducedSearchSeed (LiveContinuation.produce live).built.stage := by
  rw [LocalAction.producedSeed_exact, LocalAction.selected_exact,
    executedProducedSearchSeed_eq_scheduleEntry, sequentialStage_selected_exact]
  rfl

theorem produced_front_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (produceReduced (projectLive scope live)).next.front =
      projectFront (LiveContinuation.produce live).next := by
  rw [(produceReduced _).nextFrontExact]
  apply frontier_ext
  · rfl
  · exact heq_of_eq (congrArg Generation.ofFull
      (LiveContinuation.produce live).built.run.nextRun.generationFromProducedTarget).symm
  · exact (produced_seed_exact live).trans
      (LiveContinuation.produce live).built.run.nextRun.searchSeedFromProducedState.symm
  · change (buildAction (projectFront live)).selected :: live.state.provenance =
      (LiveContinuation.produce live).built.run.nextRun.next.provenance
    rw [LocalAction.selected_exact,
      (LiveContinuation.produce live).built.run.nextRun.provenanceFromExecution]
    rfl

theorem produced_next_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (produceReduced (projectLive scope live)).next = projectLive scope (LiveContinuation.produce live).next := by
  apply live_ext
  · exact produced_front_exact scope live
  · rw [(produceReduced _).nextValuesExact]
    exact produced_values_exact scope live

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.projectLive
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.nextFront
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produceReduced
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.action_matches_source
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produced_connections_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produced_values_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produced_decision_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produced_seed_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produced_front_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.produced_next_exact
/- AXIOM_AUDIT_END -/
