import RelationalPerimeter.Constitution.HeytingArithmetic.GodelTheoryProgression

/-!
# Gödel theory-progression regression gate

This downstream gate checks the constitutive step that is absent from a
terminal incompleteness witness: the exact sentence rejected by the source
checker is stored as the newest target postulate and accepted there, while the
target checker produces and rejects a distinct next sentence.  Both stages
also retain their arithmetic perimetral participation.
-/

namespace RelationalPerimeter.Tests.GodelTheoryProgressionRegression

open StrongPerimetralTurning
open RelationalPerimeter.HeytingArithmetic

def rootProgression : GodelHistoryProgression rootGodelHistoryStage :=
  godelHistoryProgressionAt 0

theorem rootHistoryCheckerIsTheNamedHAChecker
    (proofCode sentenceCode : Nat) :
    historyProofCheck TheoryHistory.root proofCode sentenceCode =
      haProofCheck proofCode sentenceCode :=
  historyProofCheck_root_eq_haProofCheck proofCode sentenceCode

theorem rootHistoryUnprovabilityFormulaIsTheNamedHAFormula :
    historyUnprovabilityPredicate TheoryHistory.root =
      haUnprovabilityPredicate :=
  historyUnprovabilityPredicate_root_eq_haUnprovabilityPredicate

def rootSentenceNoProofAtRoot :=
  rootProgression.sourceSentenceUnprovableAtSource

def rootSentenceTruth :=
  rootProgression.sourceSentenceTrue

def rootSentenceProofAtFirstExtension :=
  godelHistoryStage_previousSentenceProof 0

def firstExtensionSentenceNoProof :=
  rootProgression.targetSentenceUnprovableAtTarget

def firstExtensionSentenceTruth :=
  rootProgression.targetSentenceTrue

theorem firstExtensionMovesTheBoundary :
    (godelHistoryStage 0).producedSentence ≠
      (godelHistoryStage 1).producedSentence :=
  godelHistoryStage_adjacentSentencesDiffer 0

def rootProgressionRejectsProoflessFirstExtension :
    ((sentence : Sentence) ->
      CheckedSentenceProof Sentence.quote
        (historyProofCheck (godelHistoryStage 1).history) sentence -> Empty) ->
      Empty :=
  rootProgression.rejectsProoflessTarget

def rootProgressionRejectsSourceBoundaryExclusion :
    (CheckedSentenceProof Sentence.quote
        (historyProofCheck (godelHistoryStage 1).history)
        (godelHistoryStage 0).producedSentence -> Empty) ->
      Empty :=
  rootProgression.rejectsSourceBoundaryExclusion

def rootProgressionRejectsStationarity :
    (godelHistoryStage 0).producedSentence =
        (godelHistoryStage 1).producedSentence ->
      Empty :=
  rootProgression.rejectsStationaryBoundary

def falseNewestSentenceCannotEnterSoundProgression
    (history : TheoryHistory) :
    SoundTheoryHistory (.extend history falseSentence) -> Empty :=
  soundTheoryHistoryRejectsNewestFalse history

def rootSentenceIsNewestAtFirstExtension :
    (godelHistoryStage 1).history.Contains
      (godelHistoryStage 0).producedSentence :=
  rootGodelHistoryStage.sourceSentenceOccursAtAdvance

def rootProgressivePerimetralCorrespondence :
    ProgressiveGodelPerimetralCorrespondence rootGodelHistoryStage :=
  heytingArithmeticProgressiveGodelPerimetralCorrespondence

def rootPerimetralPackageRejectsSourceBoundaryExclusion :
    (SourceSentenceProofAtTarget rootGodelHistoryStage -> Empty) -> Empty :=
  rootProgressivePerimetralCorrespondence.rejectsSourceBoundaryExclusion

end RelationalPerimeter.Tests.GodelTheoryProgressionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootProgression
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootHistoryCheckerIsTheNamedHAChecker
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootHistoryUnprovabilityFormulaIsTheNamedHAFormula
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootSentenceNoProofAtRoot
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootSentenceTruth
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootSentenceProofAtFirstExtension
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.firstExtensionSentenceNoProof
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.firstExtensionSentenceTruth
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.firstExtensionMovesTheBoundary
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootProgressionRejectsProoflessFirstExtension
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootProgressionRejectsSourceBoundaryExclusion
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootProgressionRejectsStationarity
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.falseNewestSentenceCannotEnterSoundProgression
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootSentenceIsNewestAtFirstExtension
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootProgressivePerimetralCorrespondence
#print axioms RelationalPerimeter.Tests.GodelTheoryProgressionRegression.rootPerimetralPackageRejectsSourceBoundaryExclusion
/- AXIOM_AUDIT_END -/
