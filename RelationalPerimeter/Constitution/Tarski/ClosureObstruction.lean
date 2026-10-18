import RelationalPerimeter.Constitution.Tarski.Diagonal
import RelationalPerimeter.Constitution.Tarski.OperationalClosure
import RelationalPerimeter.Constitution.Continuation.ExactSeparation

/-! Final composition: the operational layer first produces local adequacy;
only then does the independently certified diagonal law reject it. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.checkUnivs false
namespace StrongPerimetralTurning
open ConstitutiveSearch.ContinuationSignatures

universe uC uB uS uK uX uT
variable {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
  {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
  {candidate : coding.Candidate}

def tarskiTerminalSeparator
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution) :
    FutureSeparator (tarskiClosureContract readout execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution) where
  requests := []
  different := by
    intro sameOutcome
    exact tarskiDiagonalReadouts_ne certification
      (congrArg Outcome.read sameOutcome)

theorem tarskiEveryExactRealizationSeparatesTerminals
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    {Memory : Type (max uB uS uK uX)}
    (realization : ExactRealization
      (tarskiClosureContract readout execution) Memory) :
    realization.project (tarskiValueTerminal execution) ≠
      realization.project (tarskiCandidateTerminal execution) :=
  realization.distinct_memory_of_separator
    (tarskiTerminalSeparator readout execution certification)

def tarskiValueToCandidateClosureConsequences
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization leftTerminal rightTerminal) :
    (readout.Truth execution.production.sentence → Empty) ×
      ((readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput) → Empty) →
        Empty) :=
  tarskiValueToCandidateConsequences certification
    (tarskiExecutedGroupingValueToCandidate readout execution realization grouping preservation)

def tarskiCandidateToValueClosureConsequences
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization rightTerminal leftTerminal) :
    readout.Truth execution.production.sentence ×
      (readout.Truth
          (coding.applyCandidate candidate execution.production.computedOutput) → Empty) :=
  tarskiCandidateToValueConsequences certification
    (tarskiExecutedGroupingCandidateToValue readout execution realization grouping preservation)

def tarskiExactClosureRejected
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal) :
    Empty :=
  let adequacy := tarskiExecutedGroupingToLocalAdequacy readout execution realization
    grouping correspondence
  ConstitutiveSearch.ContinuationSignatures.rejectBilateralTransport
    adequacy.valueToCandidate adequacy.candidateToValue
    certification.toBilateralNegationCertificate

def tarskiExactRealizationClosureRejected
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    {Memory : Type (max uB uS uK uX)}
    (realization : ExactRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization.toOperational
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal) : Empty :=
  tarskiExactClosureRejected readout execution certification realization.toOperational grouping
    (realization.terminalReadoutCorrespondence leftTerminal rightTerminal)

def tarskiCanonicalOperationalCorrespondenceRejected
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    (correspondence : TerminalReadoutCorrespondence
      (tarskiOperationalRealization readout execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)) : Empty :=
  tarskiExactClosureRejected readout execution certification
    (tarskiOperationalRealization readout execution)
    (tarskiExecutedOperationalGrouping readout execution) correspondence

def tarskiObservedExactClosureRejected
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (certification : TarskiDiagonalCertification readout execution)
    (observed : TarskiObservedOperationalGrouping readout execution)
    (correspondence : TerminalReadoutCorrespondence
      (tarskiOperationalRealization readout execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)) : Empty :=
  rejectTarskiLocalAdequacy certification
    (tarskiObservedGroupingToLocalAdequacy readout execution observed correspondence)

end StrongPerimetralTurning
/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.tarskiTerminalSeparator
#print axioms StrongPerimetralTurning.tarskiEveryExactRealizationSeparatesTerminals
#print axioms StrongPerimetralTurning.tarskiValueToCandidateClosureConsequences
#print axioms StrongPerimetralTurning.tarskiCandidateToValueClosureConsequences
#print axioms StrongPerimetralTurning.tarskiExactClosureRejected
#print axioms StrongPerimetralTurning.tarskiExactRealizationClosureRejected
#print axioms StrongPerimetralTurning.tarskiCanonicalOperationalCorrespondenceRejected
#print axioms StrongPerimetralTurning.tarskiObservedExactClosureRejected
/- AXIOM_AUDIT_END -/
