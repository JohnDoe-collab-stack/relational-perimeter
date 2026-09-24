import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAccounting

/-!
# Endogenous operational decomposition

This module is the public statement layer for the computational construction.
It does not replace or summarize away the executed development below it.  It
exposes the exact properties that jointly establish the phenomenon:

1. opening produces two structurally distinct alternatives;
2. the relation between them is reconstructed by an executed search which can
   fail before producing any stage;
3. the reconstructed map acts on arbitrary continuations, independently of an
   acceptance proof;
4. acceptance preservation is proved separately and licenses frontier
   absorption without identifying the alternatives;
5. the executed result supplies both the seed and the provenance consumed by
   the next discovery.

The construction is instantiated on the explicit generated SAT family used by
the implementation.  No classical complexity-class conclusion is stated here.
-/

namespace RelationalPerimeter.Computation.EndogenousOperationalDecomposition

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition

/-- The complete closed evidence package produced for every input. -/
abbrev Evidence (input : Nat) : Type 3 :=
  ConstitutiveSearch.EndogenousDecomposition.EndogenousOperationalDecompositionPerInputEvidence input

/-- Construct the complete evidence package; no operational premise is open. -/
def evidence (input : Nat) : Evidence input :=
  endogenousOperationalDecompositionPerInputEvidence input

/-- The uniformly indexed, measured family constructed by the implementation. -/
abbrev Family : Type 3 :=
  ConstitutiveSearch.EndogenousDecomposition.EndogenousOperationalDecompositionFamily

/-- Construct the complete family, including its canonical accounting ledger. -/
def family : Family :=
  endogenousOperationalDecompositionFamily

/-- Opening produces alternatives whose constituted decision histories differ. -/
theorem opening_produces_structurally_distinct_alternatives {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    (state.child discovery.var false discovery.fresh).context.decisions ≠
      (state.child discovery.var true discovery.fresh).context.decisions := by
  intro same
  have head :
      (⟨discovery.var, false⟩ : StructuralBranchDecision) =
        ⟨discovery.var, true⟩ :=
    List.head_eq_of_cons_eq same
  exact Bool.noConfusion (congrArg StructuralBranchDecision.value head)

/--
The reconstructed relation supplies a total map on arbitrary continuations.
No acceptance proof is an input to this operation.
-/
def transformContinuation {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation :
      GeneratedStructuralBranchContinuation
        (state.child discovery.var false discovery.fresh)) :
    GeneratedStructuralBranchContinuation
      (state.child discovery.var true discovery.fresh) :=
  discovery.relation.mapContinuation continuation

/-- Acceptance preservation is a theorem separate from the total map. -/
theorem transformContinuation_preserves_acceptance {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation :
      GeneratedStructuralBranchContinuation
        (state.child discovery.var false discovery.fresh))
    (accepted :
      GeneratedStructuralBranchAccept
        (state.child discovery.var false discovery.fresh) continuation) :
    GeneratedStructuralBranchAccept
      (state.child discovery.var true discovery.fresh)
      (transformContinuation discovery continuation) :=
  discovery.relation.mapContinuation_accept continuation accepted

/-- The directed transport makes the first child dispensable for viability. -/
theorem reconstructed_transport_preserves_viability {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    (generatedStructuralBranchSystem root).Viable
        (state.child discovery.var false discovery.fresh) →
      (generatedStructuralBranchSystem root).Viable
        (state.child discovery.var true discovery.fresh) :=
  AcceptingContinuationTransport.preservesViable
    discovery.relation.toAcceptingTransport

/-- Opening and certified absorption preserve frontier viability exactly. -/
theorem opening_then_absorption_preserves_frontier_viability {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    FrontierViable (generatedStructuralBranchSystem root) [state] ↔
      FrontierViable (generatedStructuralBranchSystem root)
        [state.child discovery.var true discovery.fresh] :=
  AcceptedFrontierPreservation.viable_iff
    (EndogenousFlipDiscovery.fullStepPreservation discovery)

/--
The complete step is already defined on arbitrary continuations.  Its output
does not depend on which proof-relevant continuation witness is supplied once
the input assignments agree.
-/
theorem complete_step_precedes_acceptance {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (left right : GeneratedStructuralBranchContinuation state)
    (same : left.1 = right.1) :
    (applyFullConstitutiveStep discovery left).1 =
      (applyFullConstitutiveStep discovery right).1 := by
  rw [applyFullConstitutiveStep_assignment, applyFullConstitutiveStep_assignment,
    same]

/-- A failed relation discovery admits no operational stage or produced next
state.  This statement applies to every threaded state and does not rely on the
freshness invariant of the successful canonical execution. -/
theorem failed_discovery_constructs_no_stage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (built : ConstructedThreadedStageRun state) : False :=
  failedDiscovery_noConstructedStage state failed built

/-- Failure also excludes every positive-length authoritative descendant
history, rather than merely selecting the `none` branch of a builder. -/
theorem failed_discovery_constructs_no_descendant_history {depth count : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (history : ConstitutiveExecutionHistory (count := count + 1) state) : False :=
  failedDiscovery_noPositiveHistory state failed history

/-- Every generated decoy candidate fails to produce the required relation. -/
theorem decoy_relation_candidates_fail
    (input candidate : Nat)
    (member : candidate ∈ distinctDecoyVariables (input + 1)) :
    tryEndogenousFlipCandidate
        (distinctGrowingDiscoveryRoot input) candidate = none :=
  distinctGrowingDiscoveryDecoyCandidate_none input candidate member

/-- Discovery returns a relation only after the exact recorded attempt count. -/
theorem relation_is_reconstructed_after_exact_attempts (depth : Nat) :
    ∃ discovery,
      (stageDiscoveryRun depth).outcome.discovered? = some discovery ∧
      discovery.var =
        growingDiscoverySplitVar (constructStage depth).searchIndex ∧
      (stageDiscoveryRun depth).outcome.attempts =
        (constructStage depth).searchIndex + 2 :=
  stageDiscovery_found_after_exact_attempts depth

/-- The unfiltered stage-local reference effort grows strictly with depth. -/
theorem executed_relation_search_attempts_grow (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.attempts <
      (stageRecordedDiscoveryRun (depth + 1)).outcome.attempts :=
  stageRecordedDiscovery_attempts_strict depth

/-- The total relation-search effort emitted by the authoritative feedback
recursion is exactly the recursively accumulated, provenance-filtered effort. -/
theorem authoritative_relation_search_attempts_exact (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts =
      threadedAttemptTotal (2 * input + 10) (input + 1) :=
  executeConstitutiveResolution_attempts_exact input

/-- The total relation-search effort emitted by the authoritative feedback
recursion grows strictly with successive external inputs.  This is the counter
of the actual provenance-filtered execution, not the unfiltered reference run. -/
theorem authoritative_relation_search_attempts_grow (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts <
      (executeConstitutiveResolution (input + 1)).stats.discoveryAttempts :=
  executeConstitutiveResolution_attempts_strict input

/- The causal execution begins from the endpoint produced by its measured
initialization run, rather than from an independently rebuilt source. -/
theorem initial_state_uses_measured_initialization (input : Nat) :
    let run := executeConstitutiveResolution input
    run.threadedInitialState =
      initialThreadedConstitutiveStateFromInitialization run.initialization := by
  exact (executeConstitutiveResolution input).threadedInitialStateFromInitialization

/--
The seed transmitted to the next stage is read definitionally from the state
produced by the executed application.  It is not a datum of the initial branch.
-/
theorem produced_seed_is_read_from_executed_state {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    executedProducedSearchSeed stage =
      (match stage.execution.producedState.context.decisions with
       | [] => 0
       | decision :: _ => decision.var) :=
  rfl

/-- The next operational state stores exactly that produced-state readout. -/
theorem next_state_stores_produced_seed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
    (realizeNextOperationalState state stage avoid).next.searchSeed =
      executedProducedSearchSeed stage :=
  rfl

/-- The retained branch determination is read from the executed application. -/
theorem retained_decision_reads_executed_output {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    (executedBranchDecision stage).value =
      stage.application.output.1 (stageSelectedVar (depth + 1)) :=
  rfl

/-- Candidate extraction runs on the operational root built from the seed. -/
theorem extraction_uses_seeded_operational_root {depth : Nat}
    (generation : CanonicalStageGeneration depth)
    (searchSeed : Nat)
    (searchSeedExact : searchSeed = generatedSearchSeed generation) :
    (measuredGeneratedExtractionFromSeed generation searchSeed
      searchSeedExact).extraction =
      runCandidateExtraction
        (measuredGeneratedExtractionFromSeed generation searchSeed
          searchSeedExact).operationalRoot :=
  rfl

/-- The next discovery consumes the bundle built from the transmitted seed. -/
theorem next_discovery_bundle_uses_transmitted_seed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    (runThreadedNextDiscovery state).generated =
      measuredGeneratedExtractionFromSeed state.generation state.searchSeed
        state.searchSeedExact :=
  rfl

/-- The state produced by one stage supplies the seed consumed by the next. -/
theorem produced_state_seeds_next_discovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    run.nextRun.next.searchSeed = executedProducedSearchSeed stage ∧
      nextDiscovery.generated =
        measuredGeneratedExtractionFromSeed
          run.nextRun.next.generation
          run.nextRun.next.searchSeed
          run.nextRun.next.searchSeedExact :=
  run.nextDiscoveryConsumesRetainedSearchSeed

/-- The provenance produced by one stage filters the next candidate domain. -/
theorem produced_provenance_filters_next_discovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    nextDiscovery.candidates =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).retained ∧
      nextDiscovery.filtering.visits =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).visits :=
  run.nextDiscoveryConsumesProducedProvenance

/-- The next discovery outcome does not factor through the permitted projection. -/
theorem next_discovery_depends_on_constitution (depth : Nat) :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := depth))
        (nextDiscoveryOutcome (depth := depth)) :=
  nextDiscovery_not_factors depth

/-- Erasing the accumulated history yields a vacuously fresh next state. -/
theorem erased_state_is_fresh_for_next (depth : Nat) :
    ThreadedStateFreshForNext (erasedNextDiscoveryState depth).state := by
  intro decision member
  cases member

/--
The same projected discovery reading can arise from differently constituted
searches: the retained candidate traces still record the distinction.
-/
theorem same_reading_can_have_different_constitution (depth : Nat) :
    (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).outcome.discovered? =
        (runThreadedNextDiscovery (erasedNextDiscoveryState depth).state).outcome.discovered? ∧
      (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).candidates ≠
        (runThreadedNextDiscovery (erasedNextDiscoveryState depth).state).candidates := by
  refine ⟨?_, reachableHistory_candidateTraces_different depth⟩
  rw [runThreadedNextDiscovery_discovered_exact _
      (retainedNextDiscoveryState_fresh depth),
    runThreadedNextDiscovery_discovered_exact _
      (erased_state_is_fresh_for_next depth)]

/-- The separator states agree on every permitted projectable state datum. -/
theorem separator_states_share_projectable_data (depth : Nat) :
    (blockedNextDiscoveryState depth).assignment =
        (retainedNextDiscoveryState depth).assignment ∧
      (blockedNextDiscoveryState depth).state.generation =
        (retainedNextDiscoveryState depth).state.generation ∧
      (blockedNextDiscoveryState depth).state.searchSeed =
        (retainedNextDiscoveryState depth).state.searchSeed :=
  ⟨rfl, rfl, rfl⟩

/--
Despite that agreement, their constituted histories and material discovery
outcomes differ.
-/
theorem separator_states_have_different_constitutions_and_outcomes
    (depth : Nat) :
    (blockedNextDiscoveryState depth).state.decisions ≠
        (retainedNextDiscoveryState depth).state.decisions ∧
      (runThreadedNextDiscovery (blockedNextDiscoveryState depth).state).outcome.discovered? ≠
        (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).outcome.discovered? := by
  refine ⟨?_, ?_⟩
  · intro same
    exact nextDiscovery_histories_distinct depth same.symm
  · intro same
    exact nextDiscovery_outcome_different depth same.symm

end RelationalPerimeter.Computation.EndogenousOperationalDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.opening_produces_structurally_distinct_alternatives
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.transformContinuation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.transformContinuation_preserves_acceptance
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.reconstructed_transport_preserves_viability
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.opening_then_absorption_preserves_frontier_viability
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.complete_step_precedes_acceptance
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.failed_discovery_constructs_no_stage
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.failed_discovery_constructs_no_descendant_history
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.decoy_relation_candidates_fail
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.relation_is_reconstructed_after_exact_attempts
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_relation_search_attempts_grow
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.authoritative_relation_search_attempts_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.authoritative_relation_search_attempts_grow
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.initial_state_uses_measured_initialization
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.produced_seed_is_read_from_executed_state
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.next_state_stores_produced_seed
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_decision_reads_executed_output
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.extraction_uses_seeded_operational_root
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.next_discovery_bundle_uses_transmitted_seed
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.produced_state_seeds_next_discovery
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.produced_provenance_filters_next_discovery
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.next_discovery_depends_on_constitution
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.erased_state_is_fresh_for_next
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.same_reading_can_have_different_constitution
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.separator_states_share_projectable_data
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.separator_states_have_different_constitutions_and_outcomes
/- AXIOM_AUDIT_END -/
