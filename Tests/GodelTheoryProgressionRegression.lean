import RelationalPerimeter.Instances.HeytingArithmetic.GodelTheoryProgression

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxRecDepth 1000000

namespace GodelTheoryProgressionRegression

open StrongPerimetralTurning
open ConstitutiveSearch.ContinuationSignatures
open RelationalPerimeter.HeytingArithmetic

def rootStep : ExecutedGodelTheoryProgression rootSoundTheoryHistory :=
  executeGodelTheoryProgression rootSoundTheoryHistory

theorem step_reuses_master_source_execution :
    rootStep.sourceExecution =
      soundHistoryGodelExecution rootSoundTheoryHistory :=
  rootStep.sourceExecution_is_master

def source_nonprovability :
    HistoryCheckedProof .root rootStep.sourceExecution.witness.production.sentence →
      Empty :=
  rootStep.sourceUnprovable

def target_proof_of_source_sentence :
    HistoryCheckedProof rootStep.targetHistory
      rootStep.sourceExecution.witness.production.sentence :=
  rootStep.oldSentenceProofAtTarget

def source_truth_to_target_proof :
    historyTruth rootStep.sourceExecution.witness.production.sentence →
      HistoryCheckedProof rootStep.targetHistory
        rootStep.sourceExecution.witness.production.sentence :=
  rootStep.oldTruthToTargetProof

def target_truth :
    historyTruth rootStep.targetExecution.witness.production.sentence :=
  rootStep.targetTrue

def target_nonprovability :
    HistoryCheckedProof rootStep.targetHistory
        rootStep.targetExecution.witness.production.sentence → Empty :=
  rootStep.targetUnprovable

def source_boundary_changes_at_target :
    (HistoryCheckedProof .root
        rootStep.sourceExecution.witness.production.sentence → Empty) ×
      HistoryCheckedProof rootStep.targetHistory
        rootStep.sourceExecution.witness.production.sentence :=
  rootStep.oldUnprovableAndTargetProof

theorem successive_sentences_are_distinct
    {history : TheoryHistory}
    {sound : SoundTheoryHistory history}
    (step : ExecutedGodelTheoryProgression sound) :
    step.sourceExecution.witness.production.sentence ≠
      step.targetExecution.witness.production.sentence :=
  step.successiveGodelSentences_ne

def reverse_translation_is_rejected
    (reverse : ∀ sentence : Sentence,
      HistoryCheckedProof rootStep.targetHistory sentence →
        HistoryCheckedProof .root sentence) : Empty :=
  rootStep.rejectUniformReverseProofTransport reverse

def source_positive_grouping :=
  rootStep.sourceOperationalGroupingWithoutRead

def target_positive_grouping :=
  rootStep.targetOperationalGroupingWithoutRead

theorem source_separator_is_terminal :
    rootStep.sourceTerminalSeparator.requests = [] :=
  rfl

theorem target_separator_is_terminal :
    rootStep.targetTerminalSeparator.requests = [] :=
  rfl

def threeStages : SoundGodelTheoryStage :=
  SoundGodelTheoryStage.tower 3

def threeStepTrace :
    SoundGodelTheoryStage.ExecutedGodelTheoryRun
      SoundGodelTheoryStage.initial 3 :=
  SoundGodelTheoryStage.executedTrace SoundGodelTheoryStage.initial 3

theorem successor_progression_consumes_produced_execution
    (stage : SoundGodelTheoryStage) :
    let step := stage.progression
    (SoundGodelTheoryStage.progressionTarget step).progression.sourceExecution =
      step.targetExecution := by
  rfl

theorem zero_step_trace_produces_initial :
    (SoundGodelTheoryStage.executedTrace
      SoundGodelTheoryStage.initial 0).fst =
        SoundGodelTheoryStage.tower 0 :=
  SoundGodelTheoryStage.executedTrace_target_eq_advance
    SoundGodelTheoryStage.initial 0

theorem one_step_trace_produces_stage_one :
    (SoundGodelTheoryStage.executedTrace
      SoundGodelTheoryStage.initial 1).fst =
        SoundGodelTheoryStage.tower 1 :=
  SoundGodelTheoryStage.executedTrace_target_eq_advance
    SoundGodelTheoryStage.initial 1

theorem two_step_trace_produces_stage_two :
    (SoundGodelTheoryStage.executedTrace
      SoundGodelTheoryStage.initial 2).fst =
        SoundGodelTheoryStage.tower 2 :=
  SoundGodelTheoryStage.executedTrace_target_eq_advance
    SoundGodelTheoryStage.initial 2

theorem three_step_trace_produces_three_stages :
    threeStepTrace.fst = threeStages :=
  SoundGodelTheoryStage.executedTrace_target_eq_advance
    SoundGodelTheoryStage.initial 3

def root_proof_survives_exact_three_step_trace
    {sentence : Sentence}
    (proof : HistoryCheckedProof .root sentence) :
    HistoryCheckedProof threeStepTrace.fst.history sentence :=
  threeStepTrace.snd.preserveProof proof

def root_proof_survives_three_extensions
    {sentence : Sentence}
    (proof : HistoryCheckedProof .root sentence) :
    HistoryCheckedProof threeStages.history sentence :=
  SoundGodelTheoryStage.preserveProof SoundGodelTheoryStage.initial 3 proof

def stage_two_sentence_is_proved_at_stage_three :
    HistoryCheckedProof
      (SoundGodelTheoryStage.tower 2).next.history
      (SoundGodelTheoryStage.tower 2).execution.witness.production.sentence :=
  (SoundGodelTheoryStage.tower 2).currentSentenceProvedAtNext

theorem every_stage_produces_a_fresh_next_sentence
    (height : Nat) :
    (SoundGodelTheoryStage.tower height).execution.witness.production.sentence ≠
      (SoundGodelTheoryStage.tower height).next.execution.witness.production.sentence :=
  (SoundGodelTheoryStage.tower height).currentAndNextSentences_ne

end GodelTheoryProgressionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms GodelTheoryProgressionRegression.rootStep
#print axioms GodelTheoryProgressionRegression.step_reuses_master_source_execution
#print axioms GodelTheoryProgressionRegression.source_nonprovability
#print axioms GodelTheoryProgressionRegression.target_proof_of_source_sentence
#print axioms GodelTheoryProgressionRegression.source_truth_to_target_proof
#print axioms GodelTheoryProgressionRegression.target_truth
#print axioms GodelTheoryProgressionRegression.target_nonprovability
#print axioms GodelTheoryProgressionRegression.source_boundary_changes_at_target
#print axioms GodelTheoryProgressionRegression.successive_sentences_are_distinct
#print axioms GodelTheoryProgressionRegression.reverse_translation_is_rejected
#print axioms GodelTheoryProgressionRegression.source_positive_grouping
#print axioms GodelTheoryProgressionRegression.target_positive_grouping
#print axioms GodelTheoryProgressionRegression.source_separator_is_terminal
#print axioms GodelTheoryProgressionRegression.target_separator_is_terminal
#print axioms GodelTheoryProgressionRegression.threeStages
#print axioms GodelTheoryProgressionRegression.threeStepTrace
#print axioms GodelTheoryProgressionRegression.successor_progression_consumes_produced_execution
#print axioms GodelTheoryProgressionRegression.zero_step_trace_produces_initial
#print axioms GodelTheoryProgressionRegression.one_step_trace_produces_stage_one
#print axioms GodelTheoryProgressionRegression.two_step_trace_produces_stage_two
#print axioms GodelTheoryProgressionRegression.three_step_trace_produces_three_stages
#print axioms GodelTheoryProgressionRegression.root_proof_survives_exact_three_step_trace
#print axioms GodelTheoryProgressionRegression.root_proof_survives_three_extensions
#print axioms GodelTheoryProgressionRegression.stage_two_sentence_is_proved_at_stage_three
#print axioms GodelTheoryProgressionRegression.every_stage_produces_a_fresh_next_sentence
/- AXIOM_AUDIT_END -/
