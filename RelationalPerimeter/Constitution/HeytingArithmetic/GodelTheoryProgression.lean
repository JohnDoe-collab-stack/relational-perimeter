import RelationalPerimeter.Constitution.HeytingArithmetic.HistoryGodelSystem

/-!
# Constitutive Gödel progression for Heyting arithmetic

A stage is a finite sound theory history.  Its Gödel sentence is produced by
the checker and represented provability predicate indexed by that same
history.  Advancing the stage stores this exact sentence as the newest postulate,
using its produced truth witness to close soundness of the extension.  Thus the
old boundary becomes checked while the next stage constructs a new true,
unprovable and provably distinct boundary.
-/

namespace RelationalPerimeter
namespace HeytingArithmetic

open StrongPerimetralTurning

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

/-! ## One sound Gödel stage -/

structure SoundGodelHistoryStage : Type where
  history : TheoryHistory
  sound : SoundTheoryHistory history

def SoundGodelHistoryStage.system
    (stage : SoundGodelHistoryStage) :
    EffectivelyPresentedSoundGodelSystem :=
  soundHistoryEffectiveGodelSystem stage.history stage.sound

def SoundGodelHistoryStage.correspondence
    (stage : SoundGodelHistoryStage) :
    EffectiveGodelPerimetralCorrespondence stage.system :=
  effectiveGodelPerimetralCorrespondence stage.system

def SoundGodelHistoryStage.execution
    (stage : SoundGodelHistoryStage) :=
  stage.correspondence.execution

def SoundGodelHistoryStage.producedWitness
    (stage : SoundGodelHistoryStage) :=
  stage.execution.exit.witness

def SoundGodelHistoryStage.producedSentence
    (stage : SoundGodelHistoryStage) : Sentence :=
  stage.producedWitness.production.sentence

def SoundGodelHistoryStage.producedTruth
    (stage : SoundGodelHistoryStage) :
    haTruth stage.producedSentence :=
  stage.correspondence.producedSentenceIsTrue

def SoundGodelHistoryStage.producedNoProof
    (stage : SoundGodelHistoryStage) :
    CheckedSentenceProof Sentence.quote (historyProofCheck stage.history)
        stage.producedSentence ->
      Empty :=
  stage.correspondence.producedSentenceIsUnprovable

def StagePerimetralParticipation
    (stage : SoundGodelHistoryStage) : Type 1 :=
  ArithmeticExecutedGodelCausalParticipation stage.execution

def SoundGodelHistoryStage.perimetralParticipation
    (stage : SoundGodelHistoryStage) :
    StagePerimetralParticipation stage :=
  stage.execution.arithmeticCausalParticipation

def rootGodelHistoryStage : SoundGodelHistoryStage :=
  { history := TheoryHistory.root
    sound := rootSoundTheoryHistory }

/-! ## The constitutive advance -/

/-- Extend by the exact sentence produced at the source stage.  The truth
witness consumed here is the one carried by the source correspondence. -/
def SoundGodelHistoryStage.advance
    (source : SoundGodelHistoryStage) : SoundGodelHistoryStage :=
  { history := .extend source.history source.producedSentence
    sound := source.sound.extend source.producedTruth }

theorem SoundGodelHistoryStage.advance_history
    (source : SoundGodelHistoryStage) :
    source.advance.history =
      TheoryHistory.extend source.history source.producedSentence :=
  rfl

def SoundGodelHistoryStage.sourceSentenceOccursAtAdvance
    (source : SoundGodelHistoryStage) :
    source.advance.history.Contains source.producedSentence :=
  TheoryHistory.Contains.newest

/-- The extension checker accepts the former boundary because the former
produced sentence is the newest positive postulate occurrence. -/
def SoundGodelHistoryStage.sourceSentenceDerivationAtAdvance
    (source : SoundGodelHistoryStage)
    (occurrence : source.advance.history.Contains source.producedSentence) :
    Derivation LogicMode.intuitionistic source.advance.history.theory
      FormulaContext.nil source.producedSentence.scopedFormula :=
  Derivation.theoryAxiom
    (HistoryAxiom.added occurrence)

def SoundGodelHistoryStage.sourceSentenceProofAtAdvance
    (source : SoundGodelHistoryStage)
    (occurrence : source.advance.history.Contains source.producedSentence) :
    CheckedSentenceProof Sentence.quote
      (historyProofCheck source.advance.history) source.producedSentence :=
  historyCheckedProofOfDerivation
    (source.sourceSentenceDerivationAtAdvance occurrence)

/-- Any earlier checked theorem is separately preserved by the theory
extension.  This transport is not used to manufacture the newest postulate. -/
def SoundGodelHistoryStage.preserveCheckedProofAtAdvance
    (source : SoundGodelHistoryStage)
    {sentence : Sentence}
    (proof : CheckedSentenceProof Sentence.quote
      (historyProofCheck source.history) sentence) :
    CheckedSentenceProof Sentence.quote
      (historyProofCheck source.advance.history) sentence :=
  historyCheckedProofOfDerivation
    (historyDerivationPreserve
      (historyDerivationOfCheckedProof source.history proof))

theorem SoundGodelHistoryStage.producedSentencesDifferAfterAdvance
    (source : SoundGodelHistoryStage) :
    source.producedSentence ≠ source.advance.producedSentence := by
  intro sameSentence
  exact Empty.elim
    (source.advance.producedNoProof
      (sameSentence ▸ source.sourceSentenceProofAtAdvance
        source.sourceSentenceOccursAtAdvance))

/-! ## One complete progression step -/

def SourceSentenceUnprovableAtSource
    (source : SoundGodelHistoryStage) : Type :=
  CheckedSentenceProof Sentence.quote
      (historyProofCheck source.history) source.producedSentence ->
    Empty

def SourceSentenceTruth
    (source : SoundGodelHistoryStage) : Type :=
  haTruth source.producedSentence

def SourceSentenceOccurrenceAtTarget
    (source : SoundGodelHistoryStage) : Type :=
  source.advance.history.Contains source.producedSentence

def SourceSentenceProofAtTarget
    (source : SoundGodelHistoryStage) : Type :=
  CheckedSentenceProof Sentence.quote
    (historyProofCheck source.advance.history) source.producedSentence

def TargetSentenceTruth
    (source : SoundGodelHistoryStage) : Type :=
  haTruth source.advance.producedSentence

def TargetSentenceUnprovableAtTarget
    (source : SoundGodelHistoryStage) : Type :=
  CheckedSentenceProof Sentence.quote
      (historyProofCheck source.advance.history)
      source.advance.producedSentence ->
    Empty

def AdjacentProducedSentencesDiffer
    (source : SoundGodelHistoryStage) : Type :=
  PLift (source.producedSentence ≠ source.advance.producedSentence)

/-- The output package for one step.  No truth or non-provability premise is
accepted here: every component is derived by `godelHistoryProgression` from
the source stage and its executed advance.  The product spelling avoids
duplicating the already large dependent types in generated structure
recursors. -/
def GodelHistoryProgression
    (source : SoundGodelHistoryStage) : Type :=
  SourceSentenceUnprovableAtSource source ×
  SourceSentenceTruth source ×
  SourceSentenceOccurrenceAtTarget source ×
  SourceSentenceProofAtTarget source ×
  TargetSentenceTruth source ×
  TargetSentenceUnprovableAtTarget source ×
  AdjacentProducedSentencesDiffer source

def godelHistoryProgression
    (source : SoundGodelHistoryStage) :
    GodelHistoryProgression source :=
  let occurrence := source.sourceSentenceOccursAtAdvance
  let sourceProof := source.sourceSentenceProofAtAdvance occurrence
  ⟨source.producedNoProof,
    source.producedTruth,
    occurrence,
    sourceProof,
    source.advance.producedTruth,
    source.advance.producedNoProof,
    ⟨source.producedSentencesDifferAfterAdvance⟩⟩

def GodelHistoryProgression.sourceSentenceUnprovableAtSource
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    SourceSentenceUnprovableAtSource source :=
  progression.1

def GodelHistoryProgression.sourceSentenceTrue
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    SourceSentenceTruth source :=
  progression.2.1

def GodelHistoryProgression.sourceSentenceOccursAtTarget
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    SourceSentenceOccurrenceAtTarget source :=
  progression.2.2.1

def GodelHistoryProgression.sourceSentenceProvableAtTarget
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    SourceSentenceProofAtTarget source :=
  progression.2.2.2.1

def GodelHistoryProgression.targetSentenceTrue
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    TargetSentenceTruth source :=
  progression.2.2.2.2.1

def GodelHistoryProgression.targetSentenceUnprovableAtTarget
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    TargetSentenceUnprovableAtTarget source :=
  progression.2.2.2.2.2.1

def GodelHistoryProgression.producedSentencesDiffer
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    AdjacentProducedSentencesDiffer source := by
  rcases progression with ⟨_sourceNoProof, _sourceTruth, _occurrence,
    _sourceProof, _targetTruth, _targetNoProof, different⟩
  exact different

/-- A checker that rejects every target sentence cannot realize this
progression, because the target checker accepts the exact source boundary. -/
def GodelHistoryProgression.rejectsProoflessTarget
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    ((sentence : Sentence) ->
      CheckedSentenceProof Sentence.quote
        (historyProofCheck source.advance.history) sentence -> Empty) ->
      Empty := by
  intro rejectsEverySentence
  exact rejectsEverySentence source.producedSentence
    progression.sourceSentenceProvableAtTarget

/-- Blanket exclusion of the exact family member produced at the source is
incompatible with the progression: that member is a checked target postulate.
This rejects that precise exclusion rule.  By itself it does not distinguish
the progression from an arbitrary stagewise shell allowed to receive a chosen
postulate. -/
def GodelHistoryProgression.rejectsSourceBoundaryExclusion
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    (SourceSentenceProofAtTarget source -> Empty) -> Empty := by
  intro excludesSourceBoundary
  exact excludesSourceBoundary progression.sourceSentenceProvableAtTarget

/-- A stationary boundary is incompatible with the constructed step. -/
def GodelHistoryProgression.rejectsStationaryBoundary
    {source : SoundGodelHistoryStage}
    (progression : GodelHistoryProgression source) :
    source.producedSentence = source.advance.producedSentence -> Empty := by
  intro stationary
  exact False.elim (progression.producedSentencesDiffer.down stationary)

/-! ## Finite constructive tower -/

def godelHistoryStage : Nat -> SoundGodelHistoryStage
  | 0 => rootGodelHistoryStage
  | Nat.succ index => (godelHistoryStage index).advance

@[simp] theorem godelHistoryStage_zero :
    godelHistoryStage 0 = rootGodelHistoryStage :=
  rfl

@[simp] theorem godelHistoryStage_succ (index : Nat) :
    godelHistoryStage (Nat.succ index) =
      (godelHistoryStage index).advance :=
  rfl

def godelHistoryProgressionAt
    (index : Nat) :
    GodelHistoryProgression (godelHistoryStage index) :=
  godelHistoryProgression (godelHistoryStage index)

theorem godelHistoryStage_adjacentSentencesDiffer
    (index : Nat) :
    (godelHistoryStage index).producedSentence ≠
      (godelHistoryStage (Nat.succ index)).producedSentence :=
  (godelHistoryProgressionAt index).producedSentencesDiffer.down

def godelHistoryStage_previousSentenceProof
    (index : Nat) :
    CheckedSentenceProof Sentence.quote
      (historyProofCheck (godelHistoryStage (Nat.succ index)).history)
      (godelHistoryStage index).producedSentence :=
  (godelHistoryProgressionAt index).sourceSentenceProvableAtTarget

def godelHistoryStage_currentSentenceNoProof
    (index : Nat) :
    CheckedSentenceProof Sentence.quote
        (historyProofCheck (godelHistoryStage index).history)
        (godelHistoryStage index).producedSentence ->
      Empty :=
  (godelHistoryStage index).producedNoProof

/-! ## Perimetral reading of the executed progression -/

def ProgressiveGodelPerimetralCorrespondence
    (source : SoundGodelHistoryStage) : Type 1 :=
  GodelHistoryProgression source ×
    StagePerimetralParticipation source ×
      StagePerimetralParticipation source.advance

def progressiveGodelPerimetralCorrespondence
    (source : SoundGodelHistoryStage) :
    ProgressiveGodelPerimetralCorrespondence source :=
  ⟨godelHistoryProgression source,
    source.perimetralParticipation,
    source.advance.perimetralParticipation⟩

/-- In the bundled package, blanket exclusion of the source boundary at the
target is impossible.  This projection uses the progression component only;
the stronger occurrence-sensitive dependency is stated in
`GodelPerimetralHistoryTransition`. -/
def ProgressiveGodelPerimetralCorrespondence.rejectsSourceBoundaryExclusion
    {source : SoundGodelHistoryStage}
    (correspondence : ProgressiveGodelPerimetralCorrespondence source) :
    (SourceSentenceProofAtTarget source -> Empty) -> Empty :=
  correspondence.1.rejectsSourceBoundaryExclusion

def heytingArithmeticProgressiveGodelPerimetralCorrespondence :
    ProgressiveGodelPerimetralCorrespondence rootGodelHistoryStage :=
  progressiveGodelPerimetralCorrespondence rootGodelHistoryStage

end HeytingArithmetic
end RelationalPerimeter

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage.system
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage.correspondence
#print axioms RelationalPerimeter.HeytingArithmetic.rootGodelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage.advance
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage.sourceSentenceProofAtAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage.preserveCheckedProofAtAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.SoundGodelHistoryStage.producedSentencesDifferAfterAdvance
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.godelHistoryProgression
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.sourceSentenceUnprovableAtSource
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.sourceSentenceTrue
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.sourceSentenceOccursAtTarget
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.sourceSentenceProvableAtTarget
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.targetSentenceTrue
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.targetSentenceUnprovableAtTarget
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.rejectsProoflessTarget
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.rejectsSourceBoundaryExclusion
#print axioms RelationalPerimeter.HeytingArithmetic.GodelHistoryProgression.rejectsStationaryBoundary
#print axioms RelationalPerimeter.HeytingArithmetic.godelHistoryStage
#print axioms RelationalPerimeter.HeytingArithmetic.godelHistoryStage_adjacentSentencesDiffer
#print axioms RelationalPerimeter.HeytingArithmetic.godelHistoryStage_previousSentenceProof
#print axioms RelationalPerimeter.HeytingArithmetic.ProgressiveGodelPerimetralCorrespondence
#print axioms RelationalPerimeter.HeytingArithmetic.progressiveGodelPerimetralCorrespondence
#print axioms RelationalPerimeter.HeytingArithmetic.ProgressiveGodelPerimetralCorrespondence.rejectsSourceBoundaryExclusion
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticProgressiveGodelPerimetralCorrespondence
/- AXIOM_AUDIT_END -/
