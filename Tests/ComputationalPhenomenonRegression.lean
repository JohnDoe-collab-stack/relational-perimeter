import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveResolution

/-!
# Regression gate for the complete computational phenomenon

These probes preserve the independently audited claims while importing only
the four initial modules and the computation reconstructed above them. They do
not redefine any production object.
-/

namespace RelationalPerimeter.Tests.ComputationalPhenomenon

open ConstitutiveSearch
open ConstitutiveSearch.EndogenousDecomposition
open SAT

/-- The seed is definitionally read from the state produced by execution. -/
theorem seed_is_read_of_producedState {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    executedProducedSearchSeed stage =
      (match stage.execution.producedState.context.decisions with
       | [] => 0
       | decision :: _ => decision.var) :=
  rfl

/-- The transmitted state stores exactly the produced-state readout. -/
theorem next_searchSeed_is_produced_seed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions) :
    (realizeNextOperationalState state stage avoid).next.searchSeed =
      executedProducedSearchSeed stage :=
  rfl

/-- The retained determination is read from the executed application. -/
theorem and_decision_reads_output {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    (executedBranchDecision stage).value =
      stage.application.output.1 (stageSelectedVar (depth + 1)) :=
  rfl

/-- Candidate extraction runs on the root built from the supplied seed. -/
theorem extraction_runs_on_seeded_root {depth : Nat}
    (generation : CanonicalStageGeneration depth)
    (searchSeed : Nat)
    (searchSeedExact : searchSeed = generatedSearchSeed generation) :
    (measuredGeneratedExtractionFromSeed generation searchSeed searchSeedExact).extraction =
      runCandidateExtraction
        (measuredGeneratedExtractionFromSeed generation searchSeed
          searchSeedExact).operationalRoot :=
  rfl

/-- The next discovery consumes the bundle built from the transmitted seed. -/
theorem discovery_bundle_from_transmitted_seed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    (runThreadedNextDiscovery state).generated =
      measuredGeneratedExtractionFromSeed state.generation state.searchSeed
        state.searchSeedExact :=
  rfl

/-- The production seed readout is genuinely nonconstant on executed stages;
this uses the production function itself rather than a test-local replica. -/
theorem production_seed_not_constant_across_stages
    {first : SequentialAssignment 0} {second : SequentialAssignment 1}
    (stage0 : SequentialStageRun 0 first)
    (stage1 : SequentialStageRun 1 second) :
    executedProducedSearchSeed stage0 ≠ executedProducedSearchSeed stage1 := by
  rw [executedProducedSearchSeed_eq_nextSearchIndex,
    executedProducedSearchSeed_eq_nextSearchIndex]
  show constitutedSearchIndex (0 + 1 + 1) ≠ constitutedSearchIndex (1 + 1 + 1)
  rw [constitutedSearchIndex_linear, constitutedSearchIndex_linear]
  decide

/- The public execution threads the actual measured initialization into the
first operational state; it does not rebuild an independent canonical source. -/
theorem execution_initial_state_consumes_initialization (input : Nat) :
    let run := executeConstitutiveResolution input
    run.threadedInitialState =
      initialThreadedConstitutiveStateFromInitialization run.initialization := by
  exact (executeConstitutiveResolution input).threadedInitialStateFromInitialization

/-- Erasing accumulated history yields a vacuously fresh state. -/
theorem erasedNextDiscoveryState_fresh (depth : Nat) :
    ThreadedStateFreshForNext (erasedNextDiscoveryState depth).state := by
  intro decision member
  cases member

/-- Equal projected readings can arise from different constituted searches. -/
theorem same_reading_different_constitution (depth : Nat) :
    (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).outcome.discovered? =
        (runThreadedNextDiscovery (erasedNextDiscoveryState depth).state).outcome.discovered? ∧
      (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).candidates ≠
        (runThreadedNextDiscovery (erasedNextDiscoveryState depth).state).candidates := by
  refine ⟨?_, reachableHistory_candidateTraces_different depth⟩
  rw [runThreadedNextDiscovery_discovered_exact _
      (retainedNextDiscoveryState_fresh depth),
    runThreadedNextDiscovery_discovered_exact _
      (erasedNextDiscoveryState_fresh depth)]

/-- The separator states share every permitted projectable state datum. -/
theorem separator_states_share_projectable_data (depth : Nat) :
    (blockedNextDiscoveryState depth).assignment =
        (retainedNextDiscoveryState depth).assignment ∧
      (blockedNextDiscoveryState depth).state.generation =
        (retainedNextDiscoveryState depth).state.generation ∧
      (blockedNextDiscoveryState depth).state.searchSeed =
        (retainedNextDiscoveryState depth).state.searchSeed :=
  ⟨rfl, rfl, rfl⟩

/-- Their constituted histories and material discovery outcomes still differ. -/
theorem separator_states_differ (depth : Nat) :
    (blockedNextDiscoveryState depth).state.decisions ≠
        (retainedNextDiscoveryState depth).state.decisions ∧
      (runThreadedNextDiscovery (blockedNextDiscoveryState depth).state).outcome.discovered? ≠
        (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).outcome.discovered? := by
  refine ⟨?_, ?_⟩
  · intro same
    exact nextDiscovery_histories_distinct depth same.symm
  · intro same
    exact nextDiscovery_outcome_different depth same.symm

/-- The concrete blocked state genuinely fails and cannot produce a stage. -/
theorem failure_branch_constructs_nothing (depth : Nat)
    (built : ConstructedThreadedStageRun (blockedNextDiscoveryState depth).state) :
    False :=
  failedDiscovery_noConstructedStage _ (nextDiscovery_blocked_none depth) built

/-- Nor can the blocked state seed any positive-length authoritative history. -/
theorem failure_branch_has_no_descendant_history (depth count : Nat)
    (history : ConstitutiveExecutionHistory
      (count := count + 1) (blockedNextDiscoveryState depth).state) : False :=
  failedDiscovery_noPositiveHistory _ (nextDiscovery_blocked_none depth) history

/-- The general growth law concerns the counter emitted by the authoritative
provenance-filtered recursion, not only a finite family of evaluated inputs. -/
theorem authoritative_attempt_counter_grows (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts <
      (executeConstitutiveResolution (input + 1)).stats.discoveryAttempts :=
  executeConstitutiveResolution_attempts_strict input

/-- Opening produces two structurally distinct alternatives. -/
theorem or_children_structurally_distinct {root : Cnf}
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

/-- The reconstructed transport absorbs one alternative for viability only. -/
theorem absorbed_alternative_viability_transported {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    (generatedStructuralBranchSystem root).Viable
        (state.child discovery.var false discovery.fresh) →
      (generatedStructuralBranchSystem root).Viable
        (state.child discovery.var true discovery.fresh) :=
  AcceptingContinuationTransport.preservesViable
    discovery.2.relation.toAcceptingTransport

/-- Opening followed by absorption preserves frontier viability both ways. -/
theorem opening_then_absorption_preserves_frontier_viability {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    FrontierViable (generatedStructuralBranchSystem root) [state] ↔
      FrontierViable (generatedStructuralBranchSystem root)
        [state.child discovery.var true discovery.fresh] :=
  AcceptedFrontierPreservation.viable_iff
    (EndogenousFlipDiscovery.fullStepPreservation discovery)

/-- The action is fixed before any acceptance information is inspected. -/
theorem full_step_output_independent_of_acceptance {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (left right : GeneratedStructuralBranchContinuation state)
    (same : left.1 = right.1) :
    (applyFullConstitutiveStep discovery left).1 =
      (applyFullConstitutiveStep discovery right).1 := by
  rw [applyFullConstitutiveStep_assignment, applyFullConstitutiveStep_assignment,
    same]

/-- Every role stage carries the exact certified absorption from its opened
binary frontier to its retained singleton frontier. -/
def operational_absorption_has_exact_frontiers {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    {run : ThreadedConstitutiveStageRun state stage}
    (roles : ThreadedConstitutiveRoleStage run) :
    AcceptedFrontierPreservation
      (generatedStructuralBranchSystem
        (distinctGrowingDiscoveryFormula
          (constructStage (depth + 1)).searchIndex))
      roles.openedFrontier roles.retainedFrontier :=
  roles.operationalAbsorption

/-- The retained width is exactly the width of the next dependent condition. -/
theorem retained_width_raccords_with_next_condition
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {head : SequentialStageRun depth assignment}
    {headRun : ThreadedConstitutiveStageRun state head}
    {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
    (headRole : ThreadedConstitutiveRoleStage headRun)
    (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
    headRole.retainedFrontier.length = tailRoles.initialOperationalWidth :=
  retainedWidth_eq_nextInitialWidth headRole tailRoles

/-- The authoritative public run has the exact alternating width trace. -/
theorem authoritative_operational_width_trace_exact (input : Nat) :
    let evidence := endogenousOperationalDecompositionEvidence input
    evidence.feedbackRolesFollowThreadedHistory.operationalWidthTrace =
      alternatingOperationalWidthTrace (resolutionLength input) :=
  (endogenousOperationalDecompositionEvidence input).operationalStability.widthTraceExact

/-- The operational width of the authoritative public run is uniformly two. -/
theorem authoritative_operational_width_bounded (input width : Nat)
    (member : width ∈
      ThreadedConstitutiveRoleHistory.operationalWidthTrace
        (endogenousOperationalDecompositionEvidence input).feedbackRolesFollowThreadedHistory) :
    width ≤ 2 :=
  OperationalStabilityCertificate.widthUniformlyBounded
    (endogenousOperationalDecompositionEvidence input).operationalStability
    width member

/-- The retained state constructs a complete one-step stabilization witness. -/
def retained_stabilization_witness_regression (depth : Nat) :
    OperationalStabilizationWitness
      (nextDiscoveryConstitution depth .retained) :=
  retainedOperationalStabilizationWitness depth

/-- The blocked counterfactual cannot construct such a witness. -/
theorem blocked_stabilization_unavailable_regression (depth : Nat) :
    ¬ OperationalStabilizationAvailable
      (nextDiscoveryConstitution depth .blocked) :=
  blocked_operationalStabilizationUnavailable depth

/-- The separator has equal projected state but exact different profiles. -/
theorem projected_stabilization_separator_regression (depth : Nat) :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) =
        nextDiscoveryProjection (nextDiscoveryConstitution depth .blocked) ∧
      operationalStabilizationProfile
          (nextDiscoveryConstitution depth .retained) = some [1, 2, 1] ∧
      operationalStabilizationProfile
          (nextDiscoveryConstitution depth .blocked) = none :=
  ⟨nextDiscovery_projection_equal depth,
    retained_operationalStabilizationProfile depth,
    blocked_operationalStabilizationProfile depth⟩

/-- The permitted projection is not globally constant; its equality on the
separator is caused by the specifically omitted history and provenance. -/
theorem permitted_projection_nonconstant_regression (depth : Nat) :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) ≠
      nextDiscoveryProjection (nextDiscoveryConstitution depth .reference) :=
  nextDiscovery_projection_nonconstant depth

/-- No arbitrary view of the permitted projection determines availability. -/
theorem projected_view_cannot_determine_stabilization_availability
    (depth : Nat) {View : Type}
    (view : NextDiscoveryProjectedState depth → View) :
    ¬ PredicateFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (OperationalStabilizationAvailable (depth := depth)) :=
  operationalStabilizationAvailability_not_factors_through_view depth view

/-- No arbitrary view of the permitted projection determines the profile. -/
theorem projected_view_cannot_determine_stabilization_profile
    (depth : Nat) {View : Type}
    (view : NextDiscoveryProjectedState depth → View) :
    ¬ ValueFactorsThrough
      (fun constitution => view (nextDiscoveryProjection constitution))
      (operationalStabilizationProfile (depth := depth)) :=
  operationalStabilizationProfile_not_factors_through_view depth view

end RelationalPerimeter.Tests.ComputationalPhenomenon

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.seed_is_read_of_producedState
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.next_searchSeed_is_produced_seed
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.and_decision_reads_output
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.extraction_runs_on_seeded_root
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.discovery_bundle_from_transmitted_seed
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.production_seed_not_constant_across_stages
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.execution_initial_state_consumes_initialization
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.same_reading_different_constitution
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.separator_states_share_projectable_data
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.separator_states_differ
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.failure_branch_constructs_nothing
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.failure_branch_has_no_descendant_history
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.authoritative_attempt_counter_grows
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.or_children_structurally_distinct
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.absorbed_alternative_viability_transported
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.opening_then_absorption_preserves_frontier_viability
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.full_step_output_independent_of_acceptance
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.operational_absorption_has_exact_frontiers
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.retained_width_raccords_with_next_condition
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.authoritative_operational_width_trace_exact
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.authoritative_operational_width_bounded
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.retained_stabilization_witness_regression
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.blocked_stabilization_unavailable_regression
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.projected_stabilization_separator_regression
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.permitted_projection_nonconstant_regression
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.projected_view_cannot_determine_stabilization_availability
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.projected_view_cannot_determine_stabilization_profile
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_not_factors
/- AXIOM_AUDIT_END -/
