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

/-- The produced-state read is genuinely sensitive to the produced state. -/
def observedSeed : List StructuralBranchDecision → Var
  | [] => 0
  | decision :: _ => decision.var

theorem observedSeed_not_constant :
    observedSeed [⟨3, true⟩] ≠ observedSeed [⟨5, true⟩] := by
  decide

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

/-- A failed discovery constructs no operational stage or descendant artifact. -/
theorem failure_branch_constructs_nothing {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none) :
    executeThreadedConstitutiveStage state fresh = none := by
  unfold executeThreadedConstitutiveStage
  dsimp only
  split
  · rfl
  · next discovery found =>
      cases Eq.trans found.symm failed

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

end RelationalPerimeter.Tests.ComputationalPhenomenon

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.seed_is_read_of_producedState
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.next_searchSeed_is_produced_seed
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.and_decision_reads_output
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.extraction_runs_on_seeded_root
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.discovery_bundle_from_transmitted_seed
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.observedSeed_not_constant
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.same_reading_different_constitution
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.separator_states_share_projectable_data
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.separator_states_differ
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.failure_branch_constructs_nothing
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.or_children_structurally_distinct
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.absorbed_alternative_viability_transported
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.opening_then_absorption_preserves_frontier_viability
#print axioms RelationalPerimeter.Tests.ComputationalPhenomenon.full_step_output_independent_of_acceptance
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution
#print axioms ConstitutiveSearch.EndogenousDecomposition.nextDiscovery_not_factors
/- AXIOM_AUDIT_END -/
