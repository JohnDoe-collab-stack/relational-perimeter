import RelationalPerimeter.Instances.HeytingArithmetic.HistoryGodel
import RelationalPerimeter.Constitution.Godel.OperationalClosure

/-!
# Executed progression of positively sound Gödel theories

One step consumes the exact sentence and truth witness produced at its source
stage.  It stores that sentence as the newest occurrence of the target history,
constructs its checked proof there, and executes a fresh Gödel production for
the target proof regime.  No projection changes the theory implicitly.
-/

set_option autoImplicit false
set_option linter.defProp false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning
open ConstitutiveSearch.ContinuationSignatures

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

abbrev HistoryCheckedProof
    (history : TheoryHistory)
    (sentence : Sentence) : Type :=
  CheckedSentenceProof Sentence.quote (historyProofCheck history) sentence

abbrev HistoryGodelExecution
    {history : TheoryHistory}
    (sound : SoundTheoryHistory history) :=
  ExecutedGodelProduction
    (soundHistoryEffectiveGodelSystem sound).toGodelSyntax
    (soundHistoryEffectiveGodelSystem sound).unprovabilityFormula
    (soundHistoryEffectiveGodelSystem sound).toGodelInterpretation

abbrev godelSuccessorHistory
    {history : TheoryHistory}
    {sound : SoundTheoryHistory history}
    (sourceExecution : HistoryGodelExecution sound) : TheoryHistory :=
  .extend history sourceExecution.witness.production.sentence

/-- The semantic certificate of the successor consumes the truth witness of
    the exact canonical source production. -/
def soundGodelSuccessor
    {history : TheoryHistory}
    (sourceSound : SoundTheoryHistory history)
    (sourceExecution : HistoryGodelExecution sourceSound) :
    SoundTheoryHistory (godelSuccessorHistory sourceExecution) :=
  .extend sourceSound sourceExecution.witness.trueWitness

/-- The source sentence is proved at the successor by its newest positive
    postulate occurrence. -/
def historyGodelSentenceProofAtSuccessor
    {history : TheoryHistory}
    {sourceSound : SoundTheoryHistory history}
    (sourceExecution : HistoryGodelExecution sourceSound) :
    HistoryCheckedProof (godelSuccessorHistory sourceExecution)
      sourceExecution.witness.production.sentence :=
  newestHistoryCheckedProof history sourceExecution.witness.production.sentence

/-- One exact source production followed by its positive theory extension and
    the freshly executed production of the extended theory. -/
structure ExecutedGodelTheoryProgression
    {history : TheoryHistory}
    (sourceSound : SoundTheoryHistory history) where
  sourceExecution : HistoryGodelExecution sourceSound
  sourceExecutionExact : sourceExecution = soundHistoryGodelExecution sourceSound
  targetSound :
    SoundTheoryHistory
      (.extend history sourceExecution.witness.production.sentence)
  targetSoundExact :
    targetSound =
      SoundTheoryHistory.extend sourceSound sourceExecution.witness.trueWitness
  oldSentenceProofAtTarget :
    HistoryCheckedProof
      (.extend history sourceExecution.witness.production.sentence)
      sourceExecution.witness.production.sentence
  oldSentenceProofAtTargetExact :
    oldSentenceProofAtTarget =
      newestHistoryCheckedProof history
        sourceExecution.witness.production.sentence
  targetExecution : HistoryGodelExecution targetSound
  targetExecutionExact :
    targetExecution = soundHistoryGodelExecution targetSound

/-- Execute a progression step from the retained master execution of the
    source stage.  The equality records that this retained value is the
    canonical execution without replacing it by a fresh computation. -/
def executeGodelTheoryProgressionFrom
    {history : TheoryHistory}
    (sourceSound : SoundTheoryHistory history)
    (sourceExecution : HistoryGodelExecution sourceSound)
    (sourceExecutionExact :
      sourceExecution = soundHistoryGodelExecution sourceSound) :
    ExecutedGodelTheoryProgression sourceSound :=
  let targetSound :
      SoundTheoryHistory
        (.extend history sourceExecution.witness.production.sentence) :=
    soundGodelSuccessor sourceSound sourceExecution
  { sourceExecution := sourceExecution
    sourceExecutionExact := sourceExecutionExact
    targetSound := targetSound
    targetSoundExact := rfl
    oldSentenceProofAtTarget :=
      historyGodelSentenceProofAtSuccessor sourceExecution
    oldSentenceProofAtTargetExact := rfl
    targetExecution := soundHistoryGodelExecution targetSound
    targetExecutionExact := rfl }

/-- The retained-execution constructor stores its received source execution
    itself, rather than an extensionally equal reconstruction. -/
theorem executeGodelTheoryProgressionFrom_sourceExecution
    {history : TheoryHistory}
    (sourceSound : SoundTheoryHistory history)
    (sourceExecution : HistoryGodelExecution sourceSound)
    (sourceExecutionExact :
      sourceExecution = soundHistoryGodelExecution sourceSound) :
    (executeGodelTheoryProgressionFrom sourceSound sourceExecution
      sourceExecutionExact).sourceExecution = sourceExecution :=
  rfl

/-- Execute the canonical first step determined by a sound history. -/
def executeGodelTheoryProgression
    {history : TheoryHistory}
    (sourceSound : SoundTheoryHistory history) :
    ExecutedGodelTheoryProgression sourceSound :=
  executeGodelTheoryProgressionFrom sourceSound
    (soundHistoryGodelExecution sourceSound) rfl

namespace ExecutedGodelTheoryProgression

variable {history : TheoryHistory}
  {sourceSound : SoundTheoryHistory history}
  (progression : ExecutedGodelTheoryProgression sourceSound)

abbrev targetHistory : TheoryHistory :=
  .extend history progression.sourceExecution.witness.production.sentence

theorem sourceExecution_is_master :
    progression.sourceExecution = soundHistoryGodelExecution sourceSound :=
  progression.sourceExecutionExact

theorem targetSound_reuses_source_truth :
    progression.targetSound =
      SoundTheoryHistory.extend sourceSound
        progression.sourceExecution.witness.trueWitness :=
  progression.targetSoundExact

theorem oldSentenceProof_is_newest_axiom :
    progression.oldSentenceProofAtTarget =
      newestHistoryCheckedProof history
        progression.sourceExecution.witness.production.sentence :=
  progression.oldSentenceProofAtTargetExact

theorem targetExecution_is_master :
    progression.targetExecution =
      soundHistoryGodelExecution progression.targetSound :=
  progression.targetExecutionExact

def sourceUnprovable :
    HistoryCheckedProof history
        progression.sourceExecution.witness.production.sentence → Empty :=
  progression.sourceExecution.witness.unprovable

def preserveOldProof
    {sentence : Sentence}
    (proof : HistoryCheckedProof history sentence) :
    HistoryCheckedProof progression.targetHistory sentence :=
  historyCheckedProofPreserved proof

def oldTruthToTargetProof :
    historyTruth progression.sourceExecution.witness.production.sentence →
      HistoryCheckedProof progression.targetHistory
        progression.sourceExecution.witness.production.sentence :=
  fun _truth => progression.oldSentenceProofAtTarget

def targetTrue :
    historyTruth progression.targetExecution.witness.production.sentence :=
  progression.targetExecution.witness.trueWitness

def targetUnprovable :
    HistoryCheckedProof progression.targetHistory
        progression.targetExecution.witness.production.sentence → Empty :=
  progression.targetExecution.witness.unprovable

def oldUnprovableAndTargetProof :
    (HistoryCheckedProof history
        progression.sourceExecution.witness.production.sentence → Empty) ×
      HistoryCheckedProof progression.targetHistory
        progression.sourceExecution.witness.production.sentence :=
  ⟨progression.sourceUnprovable, progression.oldSentenceProofAtTarget⟩

theorem successiveGodelSentences_ne :
    progression.sourceExecution.witness.production.sentence ≠
      progression.targetExecution.witness.production.sentence := by
  intro sameSentence
  have targetProof :
      HistoryCheckedProof progression.targetHistory
        progression.targetExecution.witness.production.sentence :=
    Eq.mp
      (congrArg (HistoryCheckedProof progression.targetHistory) sameSentence)
      progression.oldSentenceProofAtTarget
  exact nomatch progression.targetUnprovable targetProof

def rejectUniformReverseProofTransport
    (reverse : ∀ sentence : Sentence,
      HistoryCheckedProof progression.targetHistory sentence →
        HistoryCheckedProof history sentence) : Empty :=
  progression.sourceUnprovable
    (reverse progression.sourceExecution.witness.production.sentence
      progression.oldSentenceProofAtTarget)

/-! ## Representation-level constructions at the source stage -/

abbrev sourceOperationalGroupingWithoutRead :=
  godelOperationalGroupingWithoutRead progression.sourceExecution

def sourceComputedGroupingToProducedCompleteness
    (preservation : DirectedTerminalReadoutPreservation
      (godelOperationalRealization progression.sourceExecution)
      progression.sourceOperationalGroupingWithoutRead.leftTerminal
      progression.sourceOperationalGroupingWithoutRead.rightTerminal) :
    ExecutedGodelProducedCompleteness progression.sourceExecution.witness :=
  godelComputedGroupingToProducedCompleteness
    progression.sourceExecution preservation

def rejectSourceComputedGrouping
    (preservation : DirectedTerminalReadoutPreservation
      (godelOperationalRealization progression.sourceExecution)
      progression.sourceOperationalGroupingWithoutRead.leftTerminal
      progression.sourceOperationalGroupingWithoutRead.rightTerminal) : Empty :=
  rejectGodelComputedGroupingToEmpty progression.sourceExecution preservation

abbrev sourceTerminalSeparator :=
  godelTerminalSeparator progression.sourceExecution

theorem sourceExactRealizationSeparatesTerminals
    {Memory : Type}
    (realization : ExactRealization
      (godelClosureContract progression.sourceExecution) Memory) :
    realization.project
        progression.sourceOperationalGroupingWithoutRead.leftTerminal ≠
      realization.project
        progression.sourceOperationalGroupingWithoutRead.rightTerminal :=
  godelEveryExactRealizationSeparatesTerminals
    progression.sourceExecution realization

/-! ## The same constructions for the freshly produced target witness -/

abbrev targetOperationalGroupingWithoutRead :=
  godelOperationalGroupingWithoutRead progression.targetExecution

def targetComputedGroupingToProducedCompleteness
    (preservation : DirectedTerminalReadoutPreservation
      (godelOperationalRealization progression.targetExecution)
      progression.targetOperationalGroupingWithoutRead.leftTerminal
      progression.targetOperationalGroupingWithoutRead.rightTerminal) :
    ExecutedGodelProducedCompleteness progression.targetExecution.witness :=
  godelComputedGroupingToProducedCompleteness
    progression.targetExecution preservation

def rejectTargetComputedGrouping
    (preservation : DirectedTerminalReadoutPreservation
      (godelOperationalRealization progression.targetExecution)
      progression.targetOperationalGroupingWithoutRead.leftTerminal
      progression.targetOperationalGroupingWithoutRead.rightTerminal) : Empty :=
  rejectGodelComputedGroupingToEmpty progression.targetExecution preservation

abbrev targetTerminalSeparator :=
  godelTerminalSeparator progression.targetExecution

theorem targetExactRealizationSeparatesTerminals
    {Memory : Type}
    (realization : ExactRealization
      (godelClosureContract progression.targetExecution) Memory) :
    realization.project
        progression.targetOperationalGroupingWithoutRead.leftTerminal ≠
      realization.project
        progression.targetOperationalGroupingWithoutRead.rightTerminal :=
  godelEveryExactRealizationSeparatesTerminals
    progression.targetExecution realization

end ExecutedGodelTheoryProgression

/-! ## Compilable finite iteration -/

structure SoundGodelTheoryStage where
  history : TheoryHistory
  sound : SoundTheoryHistory history
  execution : HistoryGodelExecution sound
  executionExact : execution = soundHistoryGodelExecution sound

namespace SoundGodelTheoryStage

def initial : SoundGodelTheoryStage :=
  { history := .root
    sound := rootSoundTheoryHistory
    execution := soundHistoryGodelExecution rootSoundTheoryHistory
    executionExact := rfl }

def progression (stage : SoundGodelTheoryStage) :
    ExecutedGodelTheoryProgression stage.sound :=
  executeGodelTheoryProgressionFrom stage.sound stage.execution
    stage.executionExact

/-- A stage progression consumes the execution retained by that stage. -/
theorem progression_sourceExecution_eq (stage : SoundGodelTheoryStage) :
    stage.progression.sourceExecution = stage.execution :=
  rfl

/-- The target stage is formed from the exact outputs retained by one executed
    progression step. -/
def progressionTarget
    {stage : SoundGodelTheoryStage}
    (step : ExecutedGodelTheoryProgression stage.sound) :
    SoundGodelTheoryStage :=
  { history := step.targetHistory
    sound := step.targetSound
    execution := step.targetExecution
    executionExact := step.targetExecutionExact }

def next (stage : SoundGodelTheoryStage) : SoundGodelTheoryStage :=
  progressionTarget stage.progression

/-- The successor retains the target execution produced by the source step. -/
theorem next_execution_eq_targetExecution (stage : SoundGodelTheoryStage) :
    stage.next.execution = stage.progression.targetExecution :=
  rfl

def advance : SoundGodelTheoryStage → Nat → SoundGodelTheoryStage
  | stage, 0 => stage
  | stage, Nat.succ steps => (advance stage steps).next

def tower (height : Nat) : SoundGodelTheoryStage :=
  advance initial height

/-- A finite trace is indexed by the stage actually produced by its preceding
    step.  Its successor constructor can therefore consume only that produced
    stage, never an independently reconstructed stage with the same intended
    depth. -/
inductive ExecutedGodelTheoryTrace
    (source : SoundGodelTheoryStage) :
    Nat → SoundGodelTheoryStage → Type
  | zero : ExecutedGodelTheoryTrace source 0 source
  | succ {depth : Nat} {current : SoundGodelTheoryStage} :
      ExecutedGodelTheoryTrace source depth current →
      (step : ExecutedGodelTheoryProgression current.sound) →
      ExecutedGodelTheoryTrace source (Nat.succ depth)
        (progressionTarget step)

/-- Transport a source proof through the exact progression steps retained by
    the trace.  The successor case consumes the stored step itself; it does
    not reconstruct a progression from the endpoint history. -/
def ExecutedGodelTheoryTrace.preserveProof
    {source target : SoundGodelTheoryStage}
    {depth : Nat}
    (trace : ExecutedGodelTheoryTrace source depth target)
    {sentence : Sentence}
    (proof : HistoryCheckedProof source.history sentence) :
    HistoryCheckedProof target.history sentence :=
  match trace with
  | .zero => proof
  | .succ previous step =>
      step.preserveOldProof (previous.preserveProof proof)

/-- The result of a finite execution retains both its produced endpoint and
    the exact trace that produced it. -/
abbrev ExecutedGodelTheoryRun
    (source : SoundGodelTheoryStage)
    (depth : Nat) : Type :=
  Sigma fun target : SoundGodelTheoryStage =>
    ExecutedGodelTheoryTrace source depth target

/-- Execute and retain the complete finite chain.  The recursive case obtains
    its next source from the endpoint returned by the recursive execution. -/
def executedTrace
    (source : SoundGodelTheoryStage) :
    (depth : Nat) → ExecutedGodelTheoryRun source depth
  | 0 => ⟨source, .zero⟩
  | Nat.succ depth =>
      let previous := executedTrace source depth
      let step := previous.fst.progression
      ⟨progressionTarget step, .succ previous.snd step⟩

/-- The endpoint produced by the shared trace agrees with the simpler
    endpoint-only iterator.  This theorem compares the two APIs after the
    execution; `executedTrace` itself never calls `advance`. -/
theorem executedTrace_target_eq_advance
    (source : SoundGodelTheoryStage)
    (depth : Nat) :
    (executedTrace source depth).fst = advance source depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change progressionTarget
          ((executedTrace source depth).fst.progression) =
        (advance source depth).next
      rw [inductionHypothesis]
      rfl

def preserveProof
    (stage : SoundGodelTheoryStage)
    (steps : Nat)
    {sentence : Sentence}
    (proof : HistoryCheckedProof stage.history sentence) :
    HistoryCheckedProof (advance stage steps).history sentence :=
  let executed := executedTrace stage steps
  let producedProof : HistoryCheckedProof executed.fst.history sentence :=
    executed.snd.preserveProof proof
  Eq.mp
    (congrArg (fun target : SoundGodelTheoryStage =>
      HistoryCheckedProof target.history sentence)
      (executedTrace_target_eq_advance stage steps))
    producedProof

def currentSentenceProvedAtNext (stage : SoundGodelTheoryStage) :
    HistoryCheckedProof stage.next.history
      stage.execution.witness.production.sentence :=
  stage.progression.oldSentenceProofAtTarget

def currentSentenceUnprovable (stage : SoundGodelTheoryStage) :
    HistoryCheckedProof stage.history
        stage.execution.witness.production.sentence → Empty :=
  stage.execution.witness.unprovable

theorem currentAndNextSentences_ne (stage : SoundGodelTheoryStage) :
    stage.execution.witness.production.sentence ≠
      stage.next.execution.witness.production.sentence :=
  stage.progression.successiveGodelSentences_ne

abbrev currentOperationalGroupingWithoutRead (stage : SoundGodelTheoryStage) :=
  godelOperationalGroupingWithoutRead stage.execution

abbrev currentTerminalSeparator (stage : SoundGodelTheoryStage) :=
  godelTerminalSeparator stage.execution

theorem everyExactRealizationSeparatesCurrentTerminals
    (stage : SoundGodelTheoryStage)
    {Memory : Type}
    (realization : ExactRealization
      (godelClosureContract stage.execution) Memory) :
    realization.project stage.currentOperationalGroupingWithoutRead.leftTerminal ≠
      realization.project stage.currentOperationalGroupingWithoutRead.rightTerminal :=
  godelEveryExactRealizationSeparatesTerminals stage.execution realization

end SoundGodelTheoryStage

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.soundGodelSuccessor
#print axioms RelationalPerimeter.HeytingArithmetic.historyGodelSentenceProofAtSuccessor
#print axioms RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgressionFrom
#print axioms RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgressionFrom_sourceExecution
#print axioms RelationalPerimeter.HeytingArithmetic.executeGodelTheoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceUnprovable
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetSound_reuses_source_truth
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldSentenceProof_is_newest_axiom
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetExecution_is_master
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.preserveOldProof
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldTruthToTargetProof
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetTrue
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetUnprovable
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.oldUnprovableAndTargetProof
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.successiveGodelSentences_ne
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.rejectUniformReverseProofTransport
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceOperationalGroupingWithoutRead
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceComputedGroupingToProducedCompleteness
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.rejectSourceComputedGrouping
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceTerminalSeparator
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.sourceExactRealizationSeparatesTerminals
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetOperationalGroupingWithoutRead
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetComputedGroupingToProducedCompleteness
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.rejectTargetComputedGrouping
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetTerminalSeparator
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedGodelTheoryProgression.targetExactRealizationSeparatesTerminals
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.initial
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.progressionTarget
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.progression_sourceExecution_eq
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.next
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.next_execution_eq_targetExecution
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.advance
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryTrace.preserveProof
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.ExecutedGodelTheoryRun
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.executedTrace_target_eq_advance
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.preserveProof
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.currentSentenceProvedAtNext
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.currentSentenceUnprovable
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.currentAndNextSentences_ne
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.currentTerminalSeparator
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelTheoryStage.everyExactRealizationSeparatesCurrentTerminals
/- AXIOM_AUDIT_END -/
