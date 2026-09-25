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
5. a recursive causal certificate pins every absorption to the executed
   discovery and raccords the retained content to the exact dependent tail;
6. the certified causal collapse has an exact singleton image while the
   complete, duplicate-free carrier that keeps every binary choice independent
   has width `2^n`; structurally unequal obligations may receive the same
   operational status without being identified;
7. the unique dependent execution history has the exact operational-width
   trace `1, 2, 1, 2, ..., 1`, uniformly bounded by two;
8. the executed result supplies both the seed and the provenance consumed by
   the next discovery;
9. stabilization availability and its coarse calculable width readout do not
   factor through the permitted projected state, nor through any view of that
   projection.

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

/-- Stability evidence carried by the same authoritative run as the public result. -/
abbrev EndogenousOperationalStabilityEvidence (input : Nat) : Type 2 :=
    OperationalStabilityCertificate
      (evidence input).core.run.constitutiveFeedbackHistory
      (evidence input).core.feedbackRolesFollowThreadedHistory

/-- Construct the endogenous stability certificate of the authoritative run. -/
def endogenousOperationalStability (input : Nat) :
    EndogenousOperationalStabilityEvidence input :=
  (evidence input).core.operationalStability

/-- One structural obligation indexed by the authoritative role history. -/
abbrev StructuralObligation (input : Nat) : Type 2 :=
  IndependentStructuralObligation
    (evidence input).core.feedbackRolesFollowThreadedHistory

/-- All structurally independent obligations constituted by the exact run. -/
def structuralObligationFrontier (input : Nat) :
    List (StructuralObligation input) :=
  (evidence input).core.feedbackRolesFollowThreadedHistory
    |>.independentStructuralObligationFrontier

/-- The unique obligation selected by the executed causal reduction chain. -/
def retainedOperationalObligation (input : Nat) : StructuralObligation input :=
  (endogenousOperationalStability input).causalStability
    |>.retainedOperationalObligation

/-- Classify any structural obligation by the operational status computed by
the authoritative reduction chain.  The result does not change the structural
identity of the source obligation. -/
def collapseOperationalObligation (input : Nat)
    (obligation : StructuralObligation input) : StructuralObligation input :=
  (endogenousOperationalStability input).causalStability
    |>.collapseStructuralObligation obligation

theorem collapse_operational_obligation_exact (input : Nat)
    (obligation : StructuralObligation input) :
    collapseOperationalObligation input obligation =
      retainedOperationalObligation input :=
  (endogenousOperationalStability input).causalStability
    |>.collapseStructuralObligation_exact obligation

/-- Decision path obtained by consuming one structural obligation through the
material output of every reduction in the authoritative run. -/
def materiallyNormalizedDecisionPath (input : Nat)
    (obligation : StructuralObligation input) :
    List StructuralBranchDecision :=
  (evidence input).core.feedbackRolesFollowThreadedHistory
    |>.materiallyNormalizedDecisionPath obligation

/-- Decision path of the unique obligation retained by the authoritative run. -/
def retainedOperationalDecisionPath (input : Nat) :
    List StructuralBranchDecision :=
  (evidence input).core.feedbackRolesFollowThreadedHistory
    |>.retainedOperationalDecisionPath

/-- Every complete structural path is normalized, stage by stage, to the path
read from the materially produced continuations. -/
theorem materially_normalized_decision_path_exact (input : Nat)
    (obligation : StructuralObligation input) :
    materiallyNormalizedDecisionPath input obligation =
      retainedOperationalDecisionPath input :=
  (endogenousOperationalStability input).materialNormalizationExact obligation

/-- The obligation-level collapse follows the material decision-path
normalization; the collapse is not merely a numerical width assertion. -/
theorem collapse_decisions_follow_material_normalization (input : Nat)
    (obligation : StructuralObligation input) :
    (collapseOperationalObligation input obligation).decisions =
      materiallyNormalizedDecisionPath input obligation :=
  (endogenousOperationalStability input).materialCollapseFollowsNormalization
    obligation

theorem collapse_operational_obligation_mem_retained (input : Nat)
    (obligation : StructuralObligation input)
    (member : obligation ∈ structuralObligationFrontier input) :
    collapseOperationalObligation input obligation ∈
      [retainedOperationalObligation input] :=
  (endogenousOperationalStability input).causalStability
    |>.collapseStructuralObligation_mem_retained obligation member

/-- The retained operational obligation belongs to the complete structural
carrier from which it was computed. -/
theorem retained_operational_obligation_is_structural (input : Nat) :
    retainedOperationalObligation input ∈ structuralObligationFrontier input :=
  (endogenousOperationalStability input).causalStability
    |>.retainedOperationalObligation_mem_structural

/-- The operational image is exactly the retained obligation.  This is the
public statement that operational co-classification does not require equality
of the structural obligations. -/
theorem operational_image_iff_eq_retained (input : Nat)
    (target : StructuralObligation input) :
    ((endogenousOperationalStability input).causalStability
        |>.InOperationalImage target) ↔
      target = retainedOperationalObligation input :=
  (endogenousOperationalStability input).causalCollapseImageExact target

/-- Every two structural obligations receive the same carried operational
status from the executed causal chain, without becoming structurally equal. -/
theorem all_structural_obligations_share_operational_status (input : Nat)
    (left right : StructuralObligation input) :
    collapseOperationalObligation input left =
      collapseOperationalObligation input right :=
  (endogenousOperationalStability input).causalStability
    |>.allStructuralObligationsOperationallyIdentified left right

/-- The stronger material statement: the two source paths are actually
consumed by the normalizer and yield the same executed operational path. -/
theorem all_structural_obligations_share_material_status (input : Nat)
    (left right : StructuralObligation input) :
    materiallyNormalizedDecisionPath input left =
      materiallyNormalizedDecisionPath input right :=
  (endogenousOperationalStability input).materialOperationalIdentification
    left right

/-- The exact operational-width trace alternates singleton and binary frontiers. -/
theorem operational_width_trace_exact (input : Nat) :
    (evidence input).core.feedbackRolesFollowThreadedHistory.operationalWidthTrace =
      alternatingOperationalWidthTrace (resolutionLength input) :=
  (endogenousOperationalStability input).widthTraceExact

/-- There are two width readings per executed opening and one terminal reading. -/
theorem operational_width_trace_length_exact (input : Nat) :
    (evidence input).core.feedbackRolesFollowThreadedHistory.operationalWidthTrace.length =
      2 * (input + 1) + 1 :=
  (endogenousOperationalStability input).widthTraceLength

/-- Every width in the authoritative trace is exactly one or two. -/
theorem operational_width_is_one_or_two (input width : Nat)
    (member : width ∈
      (evidence input).core.feedbackRolesFollowThreadedHistory.operationalWidthTrace) :
    width = 1 ∨ width = 2 :=
  (endogenousOperationalStability input).widthValuesAreOneOrTwo width member

/-- Operational width is uniformly bounded by two for every public input. -/
theorem operational_width_uniformly_bounded (input width : Nat)
    (member : width ∈
      (evidence input).core.feedbackRolesFollowThreadedHistory.operationalWidthTrace) :
    width ≤ 2 :=
  (endogenousOperationalStability input).widthUniformlyBounded width member

/-- If every binary alternative were retained as an independent obligation,
the explicit structural carrier would have width `2^(input+1)`. -/
theorem unabsorbed_structural_width_is_exponential (input : Nat) :
    (structuralObligationFrontier input).length =
      2 ^ (resolutionLength input) :=
  (endogenousOperationalStability input).structuralWidthExponential

/-- The exponential structural carrier counts genuinely distinct obligations,
not repeated encodings of the same obligation. -/
theorem unabsorbed_structural_obligations_are_distinct (input : Nat) :
    (structuralObligationFrontier input).Nodup :=
  (endogenousOperationalStability input).structuralObligationsDistinct

/-- The criterion-preserving absorptions reconstructed along the authoritative
run carry exactly one obligation between openings. -/
theorem retained_operational_width_is_one (input : Nat) :
    (CausalOperationalStability.retainedOperationalObligationFrontier
      (endogenousOperationalStability input).causalStability).length = 1 :=
  (endogenousOperationalStability input).retainedOperationalWidthOne

/-- The causal certificate, not a preselected numerical trace, establishes the
strict separation between retained operational width and the unabsorbed
structural carrier on every public run. -/
theorem certified_absorption_prevents_exponential_accumulation (input : Nat) :
    (CausalOperationalStability.retainedOperationalObligationFrontier
      (endogenousOperationalStability input).causalStability).length <
      (structuralObligationFrontier input).length :=
  OperationalStabilityCertificate.preventsExponentialOperationalAccumulation
    (endogenousOperationalStability input)

/-- Constructive boundary evidence attached to the same public input package. -/
abbrev ProjectedStabilizationBoundaryEvidence (input : Nat) : Type 2 :=
  ProjectedStabilizationBoundaryCertificate input

def projectedStabilizationBoundary (input : Nat) :
    ProjectedStabilizationBoundaryEvidence input :=
  (evidence input).core.projectedStabilizationBoundary

/-- The retained state produced by execution has the exact coarse width
readout.  Its full stabilization witness carries the causal evidence. -/
theorem retained_stabilization_profile_exact (input : Nat) :
    operationalStabilizationProfile
        (nextDiscoveryConstitution input .retained) = some [1, 2, 1] :=
  (projectedStabilizationBoundary input).retainedProfileExact

/-- The blocked counterfactual has no stabilization width readout. -/
theorem blocked_stabilization_profile_absent (input : Nat) :
    operationalStabilizationProfile
        (nextDiscoveryConstitution input .blocked) = none :=
  (projectedStabilizationBoundary input).blockedProfileExact

/-- The permitted observation is nondegenerate: it distinguishes the executed
retained state from the canonical reference state. -/
theorem permitted_projection_is_nonconstant (input : Nat) :
    nextDiscoveryProjection (nextDiscoveryConstitution input .retained) ≠
      nextDiscoveryProjection (nextDiscoveryConstitution input .reference) :=
  (projectedStabilizationBoundary input).projectedStateNonconstant

/-- The projected state does not determine stabilization-witness availability. -/
theorem stabilization_availability_not_determined_by_projected_state
    (input : Nat) :
    ¬ PredicateFactorsThrough
      (nextDiscoveryProjection (depth := input))
      (OperationalStabilizationAvailable (depth := input)) :=
  (projectedStabilizationBoundary input).stabilizationAvailabilityNotProjected

/-- The projected state does not determine even the coarse stabilization
width readout. -/
theorem stabilization_profile_not_determined_by_projected_state
    (input : Nat) :
    ¬ ValueFactorsThrough
      (nextDiscoveryProjection (depth := input))
      (operationalStabilizationProfile (depth := input)) :=
  (projectedStabilizationBoundary input).stabilizationProfileNotProjected

/-- No further view computed only from the projection determines availability. -/
theorem stabilization_availability_not_determined_by_projected_view
    (input : Nat) {View : Type}
    (view : NextDiscoveryProjectedState input → View) :
    ¬ PredicateFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (OperationalStabilizationAvailable (depth := input)) :=
  operationalStabilizationAvailability_not_factors_through_view input view

/-- No further view computed only from the projection determines the coarse
width readout. -/
theorem stabilization_profile_not_determined_by_projected_view
    (input : Nat) {View : Type}
    (view : NextDiscoveryProjectedState input → View) :
    ¬ ValueFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (operationalStabilizationProfile (depth := input)) :=
  operationalStabilizationProfile_not_factors_through_view input view

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
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.EndogenousOperationalStabilityEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.endogenousOperationalStability
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.StructuralObligation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.structuralObligationFrontier
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retainedOperationalObligation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.collapseOperationalObligation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.collapse_operational_obligation_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.materiallyNormalizedDecisionPath
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retainedOperationalDecisionPath
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.materially_normalized_decision_path_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.collapse_decisions_follow_material_normalization
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.collapse_operational_obligation_mem_retained
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_operational_obligation_is_structural
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_image_iff_eq_retained
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.all_structural_obligations_share_operational_status
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.all_structural_obligations_share_material_status
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_width_trace_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_width_trace_length_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_width_is_one_or_two
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_width_uniformly_bounded
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.unabsorbed_structural_width_is_exponential
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.unabsorbed_structural_obligations_are_distinct
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_operational_width_is_one
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.certified_absorption_prevents_exponential_accumulation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.ProjectedStabilizationBoundaryEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.projectedStabilizationBoundary
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_stabilization_profile_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.blocked_stabilization_profile_absent
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.permitted_projection_is_nonconstant
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.stabilization_availability_not_determined_by_projected_state
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.stabilization_profile_not_determined_by_projected_state
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.stabilization_availability_not_determined_by_projected_view
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.stabilization_profile_not_determined_by_projected_view
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
