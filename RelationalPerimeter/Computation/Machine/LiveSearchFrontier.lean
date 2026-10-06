import RelationalPerimeter.Computation.Machine.CausalRoot

/-! A constituted frontier without an assignment, reader or historical cursor.
The positive generation witness is retained; diagnostics are not runtime data. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open SAT EndogenousDecomposition ConnectedFabric StrongPerimetralTurning
open StrongPerimetralTurning.Example

structure Generation (depth : Nat) where
  target : PositiveConstitution examplePresentation
  targetExact : target = (constructStage (depth + 1)).history.endpoint
  generated : GeneratedStep (constructStage depth).history.endpoint target

def Generation.ofFull {depth : Nat} (generation : CanonicalStageGeneration depth) :
    Generation depth := ⟨generation.target, generation.targetExact, generation.generated⟩

def Generation.full {depth : Nat} (generation : Generation depth) :
    CanonicalStageGeneration depth :=
  ⟨generation.target, generation.targetExact, generation.generated, 1, 1, 1, 1⟩

def Generation.next {depth : Nat} (generation : Generation depth) : Generation (depth + 1) :=
  .ofFull (generateCanonicalStageFromSource generation.target generation.targetExact)

structure Frontier where
  depth : Nat
  generation : Generation depth
  searchSeed : Nat
  seedExact : searchSeed = generatedSearchSeed generation.full
  provenance : List Var
  fresh : ∀ portVar, portVar ∈ provenance → portVar < stageSelectedVar (depth + 1)

theorem mapped_provenance_fresh {depth : Nat} (decisions : List StructuralBranchDecision)
    (fresh : ∀ decision, decision ∈ decisions → decision.var < stageSelectedVar (depth + 1)) :
    ∀ portVar, portVar ∈ decisions.map (fun decision => decision.var) →
      portVar < stageSelectedVar (depth + 1) := by
  induction decisions with
  | nil => intro portVar member; cases member
  | cons decision rest ih =>
      intro portVar member
      cases member with
      | head => exact fresh decision (.head _)
      | tail _ member => exact ih (fun prior member => fresh prior (.tail _ member)) portVar member

def projectFront (live : LiveContinuation.Memory) : Frontier :=
  { depth := live.depth
    generation := .ofFull live.state.generation
    searchSeed := live.state.searchSeed
    seedExact := live.state.searchSeedExact
    provenance := live.state.provenance
    fresh := by
      rw [live.state.provenanceExact]
      exact mapped_provenance_fresh live.state.decisions live.fresh }

def discover (front : Frontier) :
    FeedbackDiscoveryFromDataRun front.depth front.generation.full front.provenance :=
  runFeedbackDiscoveryFromData front.depth front.generation.full front.provenance
    front.searchSeed front.seedExact

theorem discovery_projection (live : LiveContinuation.Memory) :
    (discover (projectFront live)).outcome = (runThreadedNextDiscovery live.state).outcome := rfl

theorem candidates_projection (live : LiveContinuation.Memory) :
    (discover (projectFront live)).candidates = (runThreadedNextDiscovery live.state).candidates := rfl

theorem generation_projection (live : LiveContinuation.Memory) :
    (projectFront live).generation.target = live.state.generation.target := rfl

theorem provenance_rejection_member (portVar : Var) (provenance : List Var)
    (rejected : provenanceAvoidCheck portVar provenance = false) : portVar ∈ provenance := by
  induction provenance with
  | nil => cases rejected
  | cons prior rest ih =>
      unfold provenanceAvoidCheck at rejected
      split at rejected
      · rename_i same; cases same; exact .head _
      · exact .tail _ (ih rejected)

def proofDecisions (provenance : List Var) : List StructuralBranchDecision :=
  provenance.map (fun portVar => ⟨portVar, true⟩)

theorem proofDecisions_variables (provenance : List Var) :
    (proofDecisions provenance).map (fun decision => decision.var) = provenance := by
  induction provenance with
  | nil => rfl
  | cons portVar rest ih => exact congrArg (List.cons portVar) ih

theorem removed_candidates_fail (front : Frontier) :
    ∀ candidate, candidate ∈ (stageRecordedDiscoveryRun (front.depth + 1)).extraction.candidates →
      provenanceAvoidCheck candidate front.provenance = false →
      (tryMeasuredCandidate (constructStage (front.depth + 1)).operationalRoot candidate).produced? = none := by
  intro candidate member rejected
  have below := front.fresh candidate (provenance_rejection_member candidate _ rejected)
  have decoy := stageExtracted_lt_selected_is_decoy (front.depth + 1) candidate member below
  have failed := distinctGrowingDiscoveryDecoyCandidate_none
    (constructStage (front.depth + 1)).searchIndex candidate decoy
  let measuredRun := tryMeasuredCandidate (constructStage (front.depth + 1)).operationalRoot candidate
  have measured : measuredRun.result = none :=
    Eq.trans (tryMeasuredCandidate_exact _ _) failed
  change measuredRun.produced?.map (fun produced => produced.discovery) = none at measured
  exact optionEqNoneOfMapEqNone (fun produced => produced.discovery) measuredRun.produced? measured

theorem discovered_exact (front : Frontier) :
    (discover front).outcome.discovered? =
      (stageRecordedDiscoveryRun (front.depth + 1)).outcome.discovered? := by
  have failed : ∀ candidate,
      candidate ∈ (stageRecordedDiscoveryRun (front.depth + 1)).extraction.candidates →
      structuralDecisionsAvoidCheck candidate (proofDecisions front.provenance) = false →
      (tryMeasuredCandidate (constructStage (front.depth + 1)).operationalRoot candidate).produced? = none := by
    intro candidate member rejected
    apply removed_candidates_fail front candidate member
    rw [← proofDecisions_variables front.provenance,
      provenanceAvoidCheck_decisions]
    exact rejected
  have kept := exploreRecordedCandidates_filter_failed
    (constructStage (front.depth + 1)).operationalRoot (proofDecisions front.provenance)
    (stageRecordedDiscoveryRun (front.depth + 1)).extraction.candidates failed
  rw [(discover front).outcomeExact, (discover front).candidatesExact,
    (discover front).filteringExact, (discover front).generatedExact,
    (measuredGeneratedExtraction front.generation.full).extractionExact]
  rw [← proofDecisions_variables front.provenance, filterCandidatesByProvenance_retained_decisions]
  exact kept

theorem discovery_success (front : Frontier) : (discover front).outcome.discovered? ≠ none := by
  rw [discovered_exact]
  exact stageRecordedDiscovery_ne_none (front.depth + 1)

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Generation.ofFull
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Generation.full
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Generation.next
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.projectFront
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.discovery_projection
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.candidates_projection
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.generation_projection
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.provenance_rejection_member
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.proofDecisions_variables
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.removed_candidates_fail
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.discovered_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.discovery_success
/- AXIOM_AUDIT_END -/
