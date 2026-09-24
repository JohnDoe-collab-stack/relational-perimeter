import RelationalPerimeter.Computation.Feedback
import RelationalPerimeter.Computation.NonFactorization
import RelationalPerimeter.Instances.GrowingReconstruction

/-!
# Causal feedback for the growing reconstruction

The successful relation produces a decision which is retained in the next
state. The following extraction executes a stable filter driven by the list of
those decisions. Candidate provenance and operational decisions are distinct
types and distinct data: forgetting the decisions does not leave a duplicate
of them in the projection.
-/

namespace RelationalPerimeter.Instances.GrowingFeedback

open RelationalPerimeter.Computation
open RelationalPerimeter.Instances.GrowingReconstruction

/-- Candidate provenance and relation-produced decisions remain distinct. -/
abbrev GrowingFeedbackState :=
  ProducedOperationalState Nat GrowingCandidate GrowingDecision Nat

/-- Initial operational state for an arbitrary stage. -/
def feedbackInitialState (stage : Nat) : GrowingFeedbackState :=
  { output := stage
    provenance := []
    retainedTrace := []
    nextSeed := stage }

/-- Distinguished stage-zero initial state. -/
def initialState : GrowingFeedbackState := feedbackInitialState 0

/-- The next stage is carried by the produced seed. -/
def reconstructionIndex (state : GrowingFeedbackState) : Nat :=
  state.nextSeed

/-- Candidate extraction after filtering by retained relational decisions. -/
def extractedCandidatesFromState
    (state : GrowingFeedbackState) : List GrowingCandidate :=
  filterCandidatesByDecisions state.retainedTrace
    (candidates (reconstructionIndex state))

/-- Reconstruction executed under the complete conditions carried by a state. -/
def reconstructionFromState (state : GrowingFeedbackState) :=
  growingRunFrom (reconstructionIndex state)
    (extractedCandidatesFromState state)

/-- Every filtered extraction remains a decoy prefix followed by `useful`. -/
theorem extractedCandidates_shape (state : GrowingFeedbackState) :
    ∃ indices : List Nat,
      extractedCandidatesFromState state =
        indices.map GrowingCandidate.decoy ++ [.useful] := by
  unfold extractedCandidatesFromState candidates decoys
  exact filterCandidatesByDecisions_preserves_shape
    state.retainedTrace (decoyIndices (reconstructionIndex state + 1))

/-- Every transmitted state still reconstructs the relation indexed by its seed. -/
theorem reconstructionFromState_relation_exact
    (state : GrowingFeedbackState) :
    (reconstructionFromState state).relation? =
      some (.absorb (reconstructionIndex state)) := by
  obtain ⟨indices, exactShape⟩ := extractedCandidates_shape state
  unfold reconstructionFromState
  rw [exactShape]
  exact growingRunFrom_decoys_relation_exact
    (reconstructionIndex state) indices

/-- Decision produced only when the run has reconstructed a relation. -/
def decisionsProducedByRun
    {state : GrowingFeedbackState}
    (run : ReconstructionRun
      (growingReconstructionFrom (reconstructionIndex state)
        (extractedCandidatesFromState state))) : List GrowingDecision :=
  match run.relation? with
  | none => []
  | some relation => [relation.toDecision]

/-- Seed computed from the relation returned by the run. -/
def seedProducedByRun
    (state : GrowingFeedbackState)
    (run : ReconstructionRun
      (growingReconstructionFrom (reconstructionIndex state)
        (extractedCandidatesFromState state))) : Nat :=
  match run.relation? with
  | none => state.nextSeed
  | some (.absorb relationStage) => relationStage + 1

/--
The producer separates the complete tested-candidate provenance from the
relation-produced decisions which filter the next extraction.
-/
def growingStateProducer (state : GrowingFeedbackState) :
    OperationalStateProducer
      (ReconstructionRun
        (growingReconstructionFrom (reconstructionIndex state)
          (extractedCandidatesFromState state)))
      Nat GrowingCandidate GrowingDecision Nat where
  outputOf := fun _run => state.output + 1
  provenanceOf := fun run => run.testedCandidates
  retainedTraceOf := fun run =>
    state.retainedTrace ++ decisionsProducedByRun run
  nextSeedOf := fun run => seedProducedByRun state run

/-- Canonical state produced from one specified reconstruction run. -/
def produceNextState
    (state : GrowingFeedbackState)
    (run : ReconstructionRun
      (growingReconstructionFrom (reconstructionIndex state)
        (extractedCandidatesFromState state))) :
    GrowingFeedbackState :=
  (growingStateProducer state).produce run

/-- Reconstruction and decision-producing feedback form one causal step. -/
def growingFeedbackStep : FeedbackStep GrowingFeedbackState where
  Reconstruction := fun state =>
    ReconstructionRun
      (growingReconstructionFrom (reconstructionIndex state)
        (extractedCandidatesFromState state))
  reconstruct := reconstructionFromState
  produceNext := produceNextState

/-- The canonical next state is produced from the run executed at this state. -/
theorem nextState_produced_exact (state : GrowingFeedbackState) :
    growingFeedbackStep.next state =
      produceNextState state (reconstructionFromState state) :=
  rfl

/-- All fields of the canonical next state carry their exact run origin. -/
theorem nextState_has_exact_origin (state : GrowingFeedbackState) :
    ProducedFrom
      (growingStateProducer state)
      (reconstructionFromState state)
      (growingFeedbackStep.next state) :=
  OperationalStateProducer.produce_exact
    (growingStateProducer state)
    (reconstructionFromState state)

/-- A fresh state performs the unfiltered reconstruction at its supplied stage. -/
theorem feedbackInitial_run_exact (stage : Nat) :
    reconstructionFromState (feedbackInitialState stage) = growingRun stage :=
  rfl

/-- Its successful relation is the output of that exact executed run. -/
theorem feedbackInitial_relation_exact (stage : Nat) :
    (reconstructionFromState (feedbackInitialState stage)).relation? =
      some (.absorb stage) := by
  rw [feedbackInitial_run_exact]
  exact growingRun_relation_exact stage

/-- The relation output produces the decision retained by the next state. -/
theorem feedbackInitial_decision_exact (stage : Nat) :
    decisionsProducedByRun
      (state := feedbackInitialState stage)
      (reconstructionFromState (feedbackInitialState stage)) =
        [⟨stage⟩] := by
  unfold decisionsProducedByRun
  rw [feedbackInitial_relation_exact]
  rfl

/-- The relation output, rather than a trace length, produces the next seed. -/
theorem feedbackInitial_seed_exact (stage : Nat) :
    seedProducedByRun
      (feedbackInitialState stage)
      (reconstructionFromState (feedbackInitialState stage)) = stage + 1 := by
  unfold seedProducedByRun
  rw [feedbackInitial_relation_exact]

/-- The first relation-produced decision is stored as operational history. -/
theorem nextState_decision_exact (stage : Nat) :
    (growingFeedbackStep.next (feedbackInitialState stage)).retainedTrace =
      [⟨stage⟩] := by
  change [] ++ decisionsProducedByRun
    (state := feedbackInitialState stage)
    (reconstructionFromState (feedbackInitialState stage)) = [⟨stage⟩]
  exact feedbackInitial_decision_exact stage

/-- The next seed is read directly from the reconstructed relation. -/
theorem nextState_seed_exact (stage : Nat) :
    (growingFeedbackStep.next (feedbackInitialState stage)).nextSeed =
      stage + 1 :=
  feedbackInitial_seed_exact stage

/-- For every reachable or supplied state, the reconstructed relation advances the seed. -/
theorem nextState_seed_succ (state : GrowingFeedbackState) :
    (growingFeedbackStep.next state).nextSeed = state.nextSeed + 1 := by
  change
    seedProducedByRun state (reconstructionFromState state) =
      state.nextSeed + 1
  unfold seedProducedByRun
  rw [reconstructionFromState_relation_exact]
  rfl

/-- The following extraction consumes the relation-produced decision. -/
theorem secondExtraction_consumes_producedDecision (stage : Nat) :
    extractedCandidatesFromState
      (growingFeedbackStep.next (feedbackInitialState stage)) =
        filterCandidatesByDecisions [⟨stage⟩]
          (candidates (stage + 1)) := by
  unfold extractedCandidatesFromState reconstructionIndex
  rw [nextState_decision_exact, nextState_seed_exact]

/-- Two organizations compared after one shared executed run. -/
inductive DecisionRetention where
  | retained
  | forgotten
  deriving DecidableEq

/-- State canonically produced by the common stage-indexed run. -/
def retainedState (stage : Nat) : GrowingFeedbackState :=
  growingFeedbackStep.next (feedbackInitialState stage)

/--
Erase only the relation-produced decisions. Candidate provenance, output and
the relation-produced seed remain exactly those of the reachable state.
-/
def forgottenState (stage : Nat) : GrowingFeedbackState :=
  let retained := retainedState stage
  { output := retained.output
    provenance := retained.provenance
    retainedTrace := []
    nextSeed := retained.nextSeed }

/-- Select one of the two organizations after the same common run. -/
def stateUnderRetention
    (stage : Nat)
    (retention : DecisionRetention) : GrowingFeedbackState :=
  match retention with
  | .retained => retainedState stage
  | .forgotten => forgottenState stage

/-- Projection which deliberately forgets the relation-produced decisions. -/
def visibleProjection
    (stage : Nat)
    (retention : DecisionRetention) :
    Nat × List GrowingCandidate × Nat :=
  let state := stateUnderRetention stage retention
  (state.output, state.provenance, state.nextSeed)

/-- Observable executed work following the selected state. -/
def nextAttemptCount
    (stage : Nat)
    (retention : DecisionRetention) : Nat :=
  (reconstructionFromState (stateUnderRetention stage retention)).attempts

/-- Both organizations have the same decision-forgetting projection. -/
theorem retention_projection_equal (stage : Nat) :
    visibleProjection stage .retained =
      visibleProjection stage .forgotten :=
  rfl

/-- Retaining the relation-produced decision removes one next obligation. -/
theorem retained_nextAttemptCount_exact (stage : Nat) :
    nextAttemptCount stage .retained = stage + 2 := by
  unfold nextAttemptCount
  change
    (reconstructionFromState
      (growingFeedbackStep.next (feedbackInitialState stage))).attempts =
        stage + 2
  unfold reconstructionFromState extractedCandidatesFromState
    reconstructionIndex
  rw [nextState_decision_exact, nextState_seed_exact]
  rw [singleDecision_filters_nextCandidates]
  have tested := growingRunFrom_decoys_tested_exact (stage + 1)
    ((stage + 1) :: decoyIndices stage)
  change
    (growingRunFrom (stage + 1)
      (((stage + 1) :: decoyIndices stage).map GrowingCandidate.decoy ++
        [.useful])).testedCandidates.length = stage + 2
  rw [tested, appendUseful_length, mappedDecoys_length]
  change (decoyIndices stage).length + 2 = stage + 2
  rw [decoyIndices_length]

/-- Erasing the decision leaves the additional obligation in the next run. -/
theorem forgotten_nextAttemptCount_exact (stage : Nat) :
    nextAttemptCount stage .forgotten = stage + 3 := by
  unfold nextAttemptCount
  change
    (reconstructionFromState
      { output := (retainedState stage).output
        provenance := (retainedState stage).provenance
        retainedTrace := []
        nextSeed := (retainedState stage).nextSeed }).attempts = stage + 3
  unfold retainedState
  rw [nextState_seed_exact]
  change (growingRun (stage + 1)).attempts = stage + 3
  exact growingRun_attempts_exact (stage + 1)

/-- The decision-retaining and decision-forgetting outcomes are distinct. -/
theorem retention_outcome_different (stage : Nat) :
    nextAttemptCount stage .retained ≠
      nextAttemptCount stage .forgotten := by
  rw [retained_nextAttemptCount_exact, forgotten_nextAttemptCount_exact]
  exact Nat.ne_of_lt (Nat.lt_add_one (stage + 2))

/-- The next reconstruction does not factor through the decision-forgetting projection. -/
theorem nextReconstruction_notFactors (stage : Nat) :
    ¬ ValueFactorsThrough (visibleProjection stage) (nextAttemptCount stage) :=
  value_not_factors_of_same_projection
    (visibleProjection stage) (nextAttemptCount stage)
    .retained .forgotten
    (retention_projection_equal stage)
    (retention_outcome_different stage)

end RelationalPerimeter.Instances.GrowingFeedback

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Instances.GrowingFeedback.GrowingFeedbackState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.feedbackInitialState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.initialState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.reconstructionIndex
#print axioms RelationalPerimeter.Instances.GrowingFeedback.extractedCandidatesFromState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.reconstructionFromState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.extractedCandidates_shape
#print axioms RelationalPerimeter.Instances.GrowingFeedback.reconstructionFromState_relation_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.decisionsProducedByRun
#print axioms RelationalPerimeter.Instances.GrowingFeedback.seedProducedByRun
#print axioms RelationalPerimeter.Instances.GrowingFeedback.growingStateProducer
#print axioms RelationalPerimeter.Instances.GrowingFeedback.produceNextState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.growingFeedbackStep
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextState_produced_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextState_has_exact_origin
#print axioms RelationalPerimeter.Instances.GrowingFeedback.feedbackInitial_run_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.feedbackInitial_relation_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.feedbackInitial_decision_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.feedbackInitial_seed_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextState_decision_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextState_seed_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextState_seed_succ
#print axioms RelationalPerimeter.Instances.GrowingFeedback.secondExtraction_consumes_producedDecision
#print axioms RelationalPerimeter.Instances.GrowingFeedback.DecisionRetention
#print axioms RelationalPerimeter.Instances.GrowingFeedback.retainedState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.forgottenState
#print axioms RelationalPerimeter.Instances.GrowingFeedback.stateUnderRetention
#print axioms RelationalPerimeter.Instances.GrowingFeedback.visibleProjection
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextAttemptCount
#print axioms RelationalPerimeter.Instances.GrowingFeedback.retention_projection_equal
#print axioms RelationalPerimeter.Instances.GrowingFeedback.retained_nextAttemptCount_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.forgotten_nextAttemptCount_exact
#print axioms RelationalPerimeter.Instances.GrowingFeedback.retention_outcome_different
#print axioms RelationalPerimeter.Instances.GrowingFeedback.nextReconstruction_notFactors
/- AXIOM_AUDIT_END -/
