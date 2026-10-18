import RelationalPerimeter.Constitution.Tarski.Readout

/-! Semantic certification and the local Tarski rejection.  Neither the
runtime nor operational grouping is imported here. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.checkUnivs false
namespace StrongPerimetralTurning

universe uC uB uS uK uX uT

structure TarskiDiagonalCertification
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) where
  diagonalForward :
    readout.Truth execution.production.sentence →
      readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) → Empty
  diagonalBackward :
    (readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) → Empty) →
      readout.Truth execution.production.sentence

def tarskiValueToCandidateConsequences
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {readout : TarskiReadout.{uC,uS,uK,uT} coding}
    {execution : ExecutedTarskiProduction refinement candidate}
    (certification : TarskiDiagonalCertification readout execution)
    (valueToCandidate :
      readout.Truth execution.production.sentence →
        readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput)) :
    (readout.Truth execution.production.sentence → Empty) ×
      ((readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput) → Empty) →
        Empty) := by
  let rejectValue : readout.Truth execution.production.sentence → Empty :=
    fun value => certification.diagonalForward value (valueToCandidate value)
  exact ⟨rejectValue, fun rejectCandidate =>
    rejectValue (certification.diagonalBackward rejectCandidate)⟩

def tarskiCandidateToValueConsequences
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {readout : TarskiReadout.{uC,uS,uK,uT} coding}
    {execution : ExecutedTarskiProduction refinement candidate}
    (certification : TarskiDiagonalCertification readout execution)
    (candidateToValue :
      readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput) →
        readout.Truth execution.production.sentence) :
    readout.Truth execution.production.sentence ×
      (readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput) → Empty) := by
  let rejectCandidate :
      readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput) → Empty :=
    fun candidateValue => certification.diagonalForward
      (candidateToValue candidateValue) candidateValue
  exact ⟨certification.diagonalBackward rejectCandidate, rejectCandidate⟩

def rejectTarskiLocalAdequacy
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {readout : TarskiReadout.{uC,uS,uK,uT} coding}
    {execution : ExecutedTarskiProduction refinement candidate}
    (certification : TarskiDiagonalCertification readout execution)
    (adequacy : TarskiLocalAdequacy readout execution) : Empty := by
  let rejectValue : readout.Truth execution.production.sentence → Empty :=
    fun value => certification.diagonalForward value (adequacy.valueToCandidate value)
  let value : readout.Truth execution.production.sentence :=
    certification.diagonalBackward
      (fun candidateValue => rejectValue (adequacy.candidateToValue candidateValue))
  exact rejectValue value

theorem tarskiDiagonalReadouts_ne
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {readout : TarskiReadout.{uC,uS,uK,uT} coding}
    {execution : ExecutedTarskiProduction refinement candidate}
    (certification : TarskiDiagonalCertification readout execution) :
    readout.Truth execution.production.sentence ≠
      readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) := by
  intro same
  exact nomatch rejectTarskiLocalAdequacy certification
    { valueToCandidate := fun value => Eq.mp same value
      candidateToValue := fun candidateValue => Eq.mp same.symm candidateValue }

structure TarskiGlobalAdequacy
    (coding : TarskiDiagonalSyntax.{uC,uS,uK})
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (candidate : coding.Candidate) where
  valueToCandidate : (sentence : coding.Sentence) →
    readout.Truth sentence →
      readout.Truth (coding.applyCandidate candidate (coding.quote sentence))
  candidateToValue : (sentence : coding.Sentence) →
    readout.Truth (coding.applyCandidate candidate (coding.quote sentence)) →
      readout.Truth sentence

def TarskiGlobalAdequacy.atExecutedProduction
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {readout : TarskiReadout.{uC,uS,uK,uT} coding}
    (global : TarskiGlobalAdequacy coding readout candidate)
    (execution : ExecutedTarskiProduction refinement candidate) :
    TarskiLocalAdequacy readout execution where
  valueToCandidate := fun value =>
    Eq.mp
      (congrArg readout.Truth
        (congrArg (coding.applyCandidate candidate)
          execution.production.output_is_sentence_quote).symm)
      (global.valueToCandidate execution.production.sentence value)
  candidateToValue := fun candidateValue =>
    global.candidateToValue execution.production.sentence
      (Eq.mp
        (congrArg readout.Truth
          (congrArg (coding.applyCandidate candidate)
            execution.production.output_is_sentence_quote))
        candidateValue)

def rejectTarskiGlobalAdequacy
    {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
    {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
    {candidate : coding.Candidate}
    {readout : TarskiReadout.{uC,uS,uK,uT} coding}
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    (global : TarskiGlobalAdequacy coding readout candidate) : Empty :=
  rejectTarskiLocalAdequacy certification (global.atExecutedProduction execution)

end StrongPerimetralTurning
/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.TarskiDiagonalCertification
#print axioms StrongPerimetralTurning.tarskiValueToCandidateConsequences
#print axioms StrongPerimetralTurning.tarskiCandidateToValueConsequences
#print axioms StrongPerimetralTurning.rejectTarskiLocalAdequacy
#print axioms StrongPerimetralTurning.tarskiDiagonalReadouts_ne
#print axioms StrongPerimetralTurning.TarskiGlobalAdequacy
#print axioms StrongPerimetralTurning.TarskiGlobalAdequacy.atExecutedProduction
#print axioms StrongPerimetralTurning.rejectTarskiGlobalAdequacy
/- AXIOM_AUDIT_END -/
