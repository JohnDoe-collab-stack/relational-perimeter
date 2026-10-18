import RelationalPerimeter.Instances.HeytingArithmetic.Diagonal
import RelationalPerimeter.Constitution.Tarski.ClosureObstruction

/-! Concrete Heyting-arithmetic realization of the executed Tarski production
and of its operational closure obstruction. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.checkUnivs false
namespace RelationalPerimeter
namespace HeytingArithmetic
open StrongPerimetralTurning
open ConstitutiveSearch.ContinuationSignatures

def heytingArithmeticTarskiSyntax : TarskiDiagonalSyntax where
  Candidate := Predicate
  Sentence := Sentence
  Code := Nat
  quote := Sentence.quote
  applyCandidate := Predicate.applyNumeral
  diagonalize := diagonal

def heytingArithmeticTarskiRefinement :
    TarskiExecutionRefinement heytingArithmeticTarskiSyntax where
  Body := Predicate
  buildBody := diagonalBody
  substituteAtOwnCode := fun body => body.applyNumeral body.raw.code
  SubstitutionExecution := fun body output => PLift
    (PRFunction.Evaluates PRFunction.captureAvoidingDiagonalSubstitution
      (NatVector.cons body.raw.code NatVector.nil) output)
  runSubstitution := fun body =>
    PRFunction.runCore PRFunction.captureAvoidingDiagonalSubstitution
      (NatVector.cons body.raw.code NatVector.nil)
  executeSubstitution := fun _body => ⟨rfl⟩
  substitutionExact := fun body =>
    (PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code body.raw).symm
  diagonalExact := fun _predicate => rfl

abbrev HATarskiExecution (candidate : Predicate) :=
  ExecutedTarskiProduction heytingArithmeticTarskiRefinement candidate

def executeHATarskiProduction (candidate : Predicate) : HATarskiExecution candidate :=
  executeTarskiProduction heytingArithmeticTarskiRefinement candidate

def heytingArithmeticTarskiReadout : TarskiReadout heytingArithmeticTarskiSyntax where
  Truth := fun sentence => PLift sentence.models

theorem haTarskiComputedGraph {candidate : Predicate} (execution : HATarskiExecution candidate) :
    diagonalSubstitutionGraph.Holds
      (NatVector.cons execution.production.body.raw.code NatVector.nil)
      execution.production.computedOutput :=
  (diagonalSubstitutionGraph_iff_evaluates
    execution.production.body.raw.code execution.production.computedOutput).mpr
    execution.production.execution.down

structure ExecutedHATarskiProduction (candidate : Predicate) where
  execution : HATarskiExecution candidate
  graphWitness : diagonalSubstitutionGraph.Holds
    (NatVector.cons execution.production.body.raw.code NatVector.nil)
    execution.production.computedOutput

def executeCertifiedHATarskiProduction (candidate : Predicate) :
    ExecutedHATarskiProduction candidate :=
  let execution := executeHATarskiProduction candidate
  ⟨execution, haTarskiComputedGraph execution⟩

theorem haTarskiComputedOutput_unique {candidate : Predicate}
    (execution : HATarskiExecution candidate) :
    execution.production.computedOutput =
      (execution.production.body.raw.instantiateNumeral
        execution.production.body.raw.code).code :=
  PRFunction.evaluates_unique execution.production.execution.down
    (PRFunction.captureAvoidingDiagonalSubstitution_evaluates_code
      execution.production.body.raw)

theorem haTarskiExecutedDiagonalSpec {candidate : Predicate}
    (execution : HATarskiExecution candidate) :
    execution.production.sentence.models ↔
      ((candidate.applyNumeral execution.production.computedOutput).models → False) := by
  have codeExact : execution.production.computedOutput = (diagonal candidate).quote :=
    execution.production.output_is_sentence_quote.trans
      (congrArg Sentence.quote execution.production.sentence_is_diagonal)
  rw [execution.production.sentence_is_diagonal, codeExact]
  exact diagonal_spec candidate

def certifyHATarskiDiagonal {candidate : Predicate}
    (execution : HATarskiExecution candidate) :
    TarskiDiagonalCertification heytingArithmeticTarskiReadout execution where
  diagonalForward := fun value candidateValue =>
    False.elim ((haTarskiExecutedDiagonalSpec execution).mp value.down candidateValue.down)
  diagonalBackward := fun rejectCandidate =>
    ⟨(haTarskiExecutedDiagonalSpec execution).mpr
      (fun candidateHolds => nomatch rejectCandidate ⟨candidateHolds⟩)⟩

def heytingArithmeticRejectsTarskiLocalAdequacy {candidate : Predicate}
    (execution : HATarskiExecution candidate)
    (adequacy : TarskiLocalAdequacy heytingArithmeticTarskiReadout execution) : Empty :=
  rejectTarskiLocalAdequacy (certifyHATarskiDiagonal execution) adequacy

def heytingArithmeticRejectsTotalTruthCandidate (candidate : Predicate)
    (global : TarskiGlobalAdequacy heytingArithmeticTarskiSyntax
      heytingArithmeticTarskiReadout candidate) : Empty :=
  let execution := executeHATarskiProduction candidate
  rejectTarskiGlobalAdequacy execution (certifyHATarskiDiagonal execution) global

/-- Direct semantic form of Tarski indefinability.  Unlike the runtime-facing
statement, its hypotheses are ordinary implications between `Sentence.models`
propositions.  The conversion to the `PLift` readout is explicit here. -/
def heytingArithmeticRejectsSemanticTruthCandidate (candidate : Predicate)
    (valueToCandidate : (sentence : Sentence) → sentence.models →
      (candidate.applyNumeral sentence.quote).models)
    (candidateToValue : (sentence : Sentence) →
      (candidate.applyNumeral sentence.quote).models → sentence.models) : Empty :=
  heytingArithmeticRejectsTotalTruthCandidate candidate
    { valueToCandidate := fun sentence value =>
        ⟨valueToCandidate sentence value.down⟩
      candidateToValue := fun sentence candidateValue =>
        ⟨candidateToValue sentence candidateValue.down⟩ }

theorem heytingArithmeticEveryExactRealizationSeparatesTarskiTerminals
    {candidate : Predicate}
    (execution : HATarskiExecution candidate)
    {Memory : Type}
    (realization : ExactRealization
      (tarskiClosureContract heytingArithmeticTarskiReadout execution) Memory) :
    realization.project (tarskiValueTerminal execution) ≠
      realization.project (tarskiCandidateTerminal execution) :=
  tarskiEveryExactRealizationSeparatesTerminals
    heytingArithmeticTarskiReadout execution
    (certifyHATarskiDiagonal execution) realization

def heytingArithmeticTarskiGroupingToLocalAdequacy
    {candidate : Predicate} (execution : HATarskiExecution candidate)
    {Memory : Type}
    (realization : OperationalRealization
      (tarskiClosureContract heytingArithmeticTarskiReadout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal) :
    TarskiLocalAdequacy heytingArithmeticTarskiReadout execution :=
  tarskiExecutedGroupingToLocalAdequacy heytingArithmeticTarskiReadout execution
    realization grouping correspondence

def heytingArithmeticTarskiValueToCandidateClosureConsequences
    {candidate : Predicate} (execution : HATarskiExecution candidate)
    {Memory : Type}
    (realization : OperationalRealization
      (tarskiClosureContract heytingArithmeticTarskiReadout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization leftTerminal rightTerminal) :
    (heytingArithmeticTarskiReadout.Truth execution.production.sentence → Empty) ×
      ((heytingArithmeticTarskiReadout.Truth
          (candidate.applyNumeral execution.production.computedOutput) → Empty) → Empty) :=
  tarskiValueToCandidateClosureConsequences heytingArithmeticTarskiReadout execution
    (certifyHATarskiDiagonal execution) realization grouping preservation

def heytingArithmeticTarskiCandidateToValueClosureConsequences
    {candidate : Predicate} (execution : HATarskiExecution candidate)
    {Memory : Type}
    (realization : OperationalRealization
      (tarskiClosureContract heytingArithmeticTarskiReadout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization rightTerminal leftTerminal) :
    heytingArithmeticTarskiReadout.Truth execution.production.sentence ×
      (heytingArithmeticTarskiReadout.Truth
          (candidate.applyNumeral execution.production.computedOutput) → Empty) :=
  tarskiCandidateToValueClosureConsequences heytingArithmeticTarskiReadout execution
    (certifyHATarskiDiagonal execution) realization grouping preservation

def heytingArithmeticTarskiExactClosureRejected
    {candidate : Predicate} (execution : HATarskiExecution candidate)
    {Memory : Type}
    (realization : OperationalRealization
      (tarskiClosureContract heytingArithmeticTarskiReadout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal) :
    Empty :=
  tarskiExactClosureRejected heytingArithmeticTarskiReadout execution
    (certifyHATarskiDiagonal execution) realization grouping correspondence

def heytingArithmeticCanonicalOperationalCorrespondenceRejected
    {candidate : Predicate} (execution : HATarskiExecution candidate)
    (correspondence : TerminalReadoutCorrespondence
      (tarskiOperationalRealization heytingArithmeticTarskiReadout execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)) : Empty :=
  tarskiCanonicalOperationalCorrespondenceRejected heytingArithmeticTarskiReadout execution
    (certifyHATarskiDiagonal execution) correspondence

def heytingArithmeticObservedExactClosureRejected
    {candidate : Predicate} (execution : HATarskiExecution candidate)
    (observed : TarskiObservedOperationalGrouping heytingArithmeticTarskiReadout execution)
    (correspondence : TerminalReadoutCorrespondence
      (tarskiOperationalRealization heytingArithmeticTarskiReadout execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)) : Empty :=
  tarskiObservedExactClosureRejected heytingArithmeticTarskiReadout execution
    (certifyHATarskiDiagonal execution) observed correspondence

def heytingArithmeticPositiveOperationalGrouping {candidate : Predicate}
    (execution : HATarskiExecution candidate) :=
  tarskiExecutedOperationalGrouping heytingArithmeticTarskiReadout execution

def heytingArithmeticPositiveIdentityCorrespondence {candidate : Predicate}
    (execution : HATarskiExecution candidate) :=
  tarskiIdentityTerminalCorrespondence heytingArithmeticTarskiReadout execution

end HeytingArithmetic
end RelationalPerimeter
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiSyntax
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiRefinement
#print axioms RelationalPerimeter.HeytingArithmetic.executeHATarskiProduction
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiReadout
#print axioms RelationalPerimeter.HeytingArithmetic.haTarskiComputedGraph
#print axioms RelationalPerimeter.HeytingArithmetic.ExecutedHATarskiProduction
#print axioms RelationalPerimeter.HeytingArithmetic.executeCertifiedHATarskiProduction
#print axioms RelationalPerimeter.HeytingArithmetic.haTarskiComputedOutput_unique
#print axioms RelationalPerimeter.HeytingArithmetic.haTarskiExecutedDiagonalSpec
#print axioms RelationalPerimeter.HeytingArithmetic.certifyHATarskiDiagonal
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticRejectsTarskiLocalAdequacy
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticRejectsTotalTruthCandidate
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticRejectsSemanticTruthCandidate
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticEveryExactRealizationSeparatesTarskiTerminals
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiGroupingToLocalAdequacy
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiValueToCandidateClosureConsequences
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiCandidateToValueClosureConsequences
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticTarskiExactClosureRejected
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticCanonicalOperationalCorrespondenceRejected
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticObservedExactClosureRejected
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticPositiveOperationalGrouping
#print axioms RelationalPerimeter.HeytingArithmetic.heytingArithmeticPositiveIdentityCorrespondence
/- AXIOM_AUDIT_END -/
