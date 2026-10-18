import RelationalPerimeter.Instances.HeytingArithmetic.Tarski

set_option genInjectivity false
set_option autoImplicit false
namespace TarskiOperationalClosureRegression
open StrongPerimetralTurning
open ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures
open RelationalPerimeter.HeytingArithmetic

variable (candidate : Predicate)

def master := executeCertifiedHATarskiProduction candidate

theorem master_graph_is_same_execution :
    diagonalSubstitutionGraph.Holds
      (NatVector.cons (master candidate).execution.production.body.raw.code NatVector.nil)
      (master candidate).execution.production.computedOutput :=
  (master candidate).graphWitness

theorem master_output_is_the_produced_sentence_quote :
    (master candidate).execution.production.computedOutput =
      (master candidate).execution.production.sentence.quote :=
  (master candidate).execution.production.output_is_sentence_quote

def occurrences := (master candidate).execution.occurrences

theorem production_occurrences_are_successive :
    History.OccurrenceNext (occurrences candidate).buildOccurrence
        (occurrences candidate).substitutionOccurrence ∧
      History.OccurrenceNext (occurrences candidate).substitutionOccurrence
        (occurrences candidate).sentenceOccurrence ∧
      History.OccurrenceNext (occurrences candidate).sentenceOccurrence
        (occurrences candidate).completionOccurrence :=
  ⟨(occurrences candidate).buildNextSubstitution,
    (occurrences candidate).substitutionNextSentence,
    (occurrences candidate).sentenceNextCompletion⟩

def positiveGrouping :=
  heytingArithmeticPositiveOperationalGrouping (master candidate).execution

def positiveObservedGrouping :=
  tarskiObservedOperationalGrouping heytingArithmeticTarskiReadout
    (master candidate).execution

theorem positive_grouping_is_nonempty :
    (positiveGrouping candidate).requests ≠ [] :=
  (positiveGrouping candidate).nonempty

theorem positive_grouping_collision_is_computed :
    (positiveGrouping candidate).terminalCollision = rfl := rfl

theorem positive_grouping_events_are_equal :
    (positiveObservedGrouping candidate).grouping.leftEvents =
      (positiveObservedGrouping candidate).grouping.rightEvents :=
  (positiveObservedGrouping candidate).eventsEqual

theorem close_is_a_real_phase_change :
    (tarskiRuntimeNext
      (tarskiValueSource (master candidate).execution) (.close)).phase = .terminal :=
  tarskiClose_changes_phase (master candidate).execution .value

theorem source_positions_are_preserved :
    (tarskiValueTerminal (master candidate).execution).pole = .value ∧
      (tarskiCandidateTerminal (master candidate).execution).pole = .candidate := ⟨rfl, rfl⟩

theorem terminal_occurrences_are_the_master_occurrences :
    (tarskiValueTerminal (master candidate).execution).occurrences =
        (master candidate).execution.occurrences ∧
      (tarskiCandidateTerminal (master candidate).execution).occurrences =
        (master candidate).execution.occurrences :=
  ⟨tarskiValueTerminal_occurrences (master candidate).execution,
    tarskiCandidateTerminal_occurrences (master candidate).execution⟩

theorem identity_terminals_are_distinct :
    tarskiValueTerminal (master candidate).execution ≠
      tarskiCandidateTerminal (master candidate).execution :=
  tarskiIdentityTerminalsDistinct (master candidate).execution

theorem terminal_separator_is_immediate :
    (tarskiTerminalSeparator heytingArithmeticTarskiReadout
      (master candidate).execution
      (certifyHATarskiDiagonal (master candidate).execution)).requests = [] :=
  rfl

theorem every_exact_realization_separates_terminals
    {Memory : Type}
    (realization : ExactRealization
      (tarskiClosureContract heytingArithmeticTarskiReadout
        (master candidate).execution) Memory) :
    realization.project
        (tarskiValueTerminal (master candidate).execution) ≠
      realization.project
        (tarskiCandidateTerminal (master candidate).execution) :=
  heytingArithmeticEveryExactRealizationSeparatesTarskiTerminals
    (master candidate).execution realization

def positiveIdentityCorrespondence :=
  heytingArithmeticPositiveIdentityCorrespondence (master candidate).execution

namespace PolefulObservation

structure Event where
  runtimeEvent : TarskiRuntimeEvent
  activePole : Option TarskiClosurePole

def sourceEvent {candidate : Predicate} (execution : HATarskiExecution candidate)
    (source : TarskiClosureSource execution) (request : TarskiRuntimeRequest) : Event where
  runtimeEvent := tarskiRuntimeEvent source request
  activePole := match source.phase with
    | .active => some source.pole
    | .terminal => none

def reducedEvent {candidate : Predicate} (execution : HATarskiExecution candidate)
    (memory : TarskiOperationalMemory execution) (request : TarskiRuntimeRequest) : Event where
  runtimeEvent := tarskiOperationalEvent memory request
  activePole := match memory with
    | .active _ pole _ => some pole
    | .grouped _ _ => none

def sourceContract {candidate : Predicate} (execution : HATarskiExecution candidate) :
    FutureContract (TarskiClosureSource execution) TarskiRuntimeRequest
      (ULift.{1} Event) (Type) where
  next := tarskiRuntimeNext
  event := fun source request => ⟨sourceEvent execution source request⟩
  read := fun source =>
    tarskiEndpointAt heytingArithmeticTarskiReadout execution source.pole
  Allow := fun source request => TarskiOperationalAllow source.phase request
  decision := fun source request => tarskiOperationalDecision source.phase request

def reducedContract {candidate : Predicate} (execution : HATarskiExecution candidate) :
    OperationalContract (TarskiOperationalMemory execution) TarskiRuntimeRequest
      (ULift.{1} Event) where
  next := tarskiOperationalNext
  event := fun memory request => ⟨reducedEvent execution memory request⟩
  Allow := fun memory request => TarskiOperationalAllow memory.phase request
  decision := fun memory request => tarskiOperationalDecision memory.phase request

def realization {candidate : Predicate} (execution : HATarskiExecution candidate) :
    OperationalRealization (sourceContract execution) (TarskiOperationalMemory execution) where
  reduced := reducedContract execution
  project := tarskiOperationalProject
  forward := by
    intro source request witness
    cases source with
    | mk occurrences pole history phase => cases phase <;> exact witness
  backward := by
    intro source request witness
    cases source with
    | mk occurrences pole history phase => cases phase <;> exact witness
  backward_forward := by
    intro source request witness
    cases source with
    | mk occurrences pole history phase => cases phase <;> rfl
  forward_backward := by
    intro source request witness
    cases source with
    | mk occurrences pole history phase => cases phase <;> rfl
  next_exact := by
    intro source request
    cases source with
    | mk occurrences pole history phase => cases phase <;> cases request <;> rfl
  event_exact := by
    intro source request
    cases source with
    | mk occurrences pole history phase => cases phase <;> cases request <;> rfl

def closeRun {candidate : Predicate} (execution : HATarskiExecution candidate)
    (pole : TarskiClosurePole) :
    ExecutedRun (sourceContract execution) (tarskiInitialize execution pole) [.close]
      (tarskiRuntimeNext (tarskiInitialize execution pole) .close)
      [(sourceContract execution).event (tarskiInitialize execution pole) .close] :=
  .cons
    (perform (sourceContract execution) _ .close (by
      change TarskiOperationalAllow .active .close
      exact .close))
    (.nil _)

def grouping {candidate : Predicate} (execution : HATarskiExecution candidate) :
    ExecutedOperationalGrouping (realization execution)
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution) where
  trace := ⟨.close, []⟩
  leftEvents := [(sourceContract execution).event (tarskiValueSource execution) .close]
  leftRun := closeRun execution .value
  rightEvents := [(sourceContract execution).event (tarskiCandidateSource execution) .close]
  rightRun := closeRun execution .candidate
  terminalCollision := rfl

theorem event_exact_holds {candidate : Predicate} (execution : HATarskiExecution candidate)
    (source : TarskiClosureSource execution) (request : TarskiRuntimeRequest) :
    (sourceContract execution).event source request =
      (realization execution).reduced.event ((realization execution).project source) request :=
  (realization execution).event_exact source request

theorem terminal_collision_is_computed {candidate : Predicate}
    (execution : HATarskiExecution candidate) :
    (grouping execution).terminalCollision = rfl := rfl

theorem close_traces_are_distinct {candidate : Predicate}
    (execution : HATarskiExecution candidate) :
    (grouping execution).leftEvents ≠ (grouping execution).rightEvents := by
  intro same
  change [ULift.up (sourceEvent execution (tarskiValueSource execution) .close)] =
    [ULift.up (sourceEvent execution (tarskiCandidateSource execution) .close)] at same
  injection same with eventEqual
  have poles := congrArg (fun lifted : ULift Event => lifted.down.activePole) eventEqual
  cases poles

def valueToCandidate {candidate : Predicate} (execution : HATarskiExecution candidate)
    (preservation : DirectedTerminalReadoutPreservation
      (realization execution) (tarskiValueTerminal execution)
      (tarskiCandidateTerminal execution)) :
    heytingArithmeticTarskiReadout.Truth execution.production.sentence →
      heytingArithmeticTarskiReadout.Truth
        (candidate.applyNumeral execution.production.computedOutput) :=
  (grouping execution).directedReadout preservation

def candidateToValue {candidate : Predicate} (execution : HATarskiExecution candidate)
    (preservation : DirectedTerminalReadoutPreservation
      (realization execution) (tarskiCandidateTerminal execution)
      (tarskiValueTerminal execution)) :
    heytingArithmeticTarskiReadout.Truth
        (candidate.applyNumeral execution.production.computedOutput) →
      heytingArithmeticTarskiReadout.Truth execution.production.sentence :=
  (grouping execution).reverseDirectedReadout preservation

def exactClosureRejected {candidate : Predicate} (execution : HATarskiExecution candidate)
    (valuePreservation : DirectedTerminalReadoutPreservation
      (realization execution) (tarskiValueTerminal execution)
      (tarskiCandidateTerminal execution))
    (candidatePreservation : DirectedTerminalReadoutPreservation
      (realization execution) (tarskiCandidateTerminal execution)
      (tarskiValueTerminal execution)) : Empty :=
  heytingArithmeticRejectsTarskiLocalAdequacy execution
    { valueToCandidate := valueToCandidate execution valuePreservation
      candidateToValue := candidateToValue execution candidatePreservation }

end PolefulObservation

#check OperationalContract
#check OperationalRealization
#check ExecutedOperationalGrouping
#check TerminalReadoutCorrespondence
#check DirectedTerminalReadoutPreservation
#check TarskiDiagonalSyntax
#check TarskiExecutionRefinement
#check ExecutedTarskiProduction
#check TarskiReadout
#check TarskiLocalAdequacy
#check TarskiDiagonalCertification
#check TarskiDiagonalCertification.toBilateralNegationCertificate
#check tarskiExecutedGroupingToLocalAdequacy
#check tarskiExecutedGroupingValueToCandidate
#check tarskiExecutedGroupingCandidateToValue
#check tarskiExecutedGroupingToLocalAdequacyDirected
#check tarskiValueToCandidateClosureConsequences
#check tarskiCandidateToValueClosureConsequences
#check TarskiObservedOperationalGrouping
#check tarskiRuntimeEvent_pole_blind
#check tarskiObservedGroupingToLocalAdequacy
#check tarskiExactClosureRejected
#check tarskiObservedExactClosureRejected
#check heytingArithmeticRejectsTotalTruthCandidate
#check heytingArithmeticRejectsSemanticTruthCandidate
#check heytingArithmeticTarskiGroupingToLocalAdequacy
#check heytingArithmeticTarskiValueToCandidateClosureConsequences
#check heytingArithmeticTarskiCandidateToValueClosureConsequences
#check heytingArithmeticTarskiExactClosureRejected

end TarskiOperationalClosureRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms TarskiOperationalClosureRegression.master_graph_is_same_execution
#print axioms TarskiOperationalClosureRegression.master_output_is_the_produced_sentence_quote
#print axioms StrongPerimetralTurning.TarskiDiagonalCertification.toBilateralNegationCertificate
#print axioms TarskiOperationalClosureRegression.production_occurrences_are_successive
#print axioms TarskiOperationalClosureRegression.positiveGrouping
#print axioms TarskiOperationalClosureRegression.positiveObservedGrouping
#print axioms TarskiOperationalClosureRegression.positive_grouping_is_nonempty
#print axioms TarskiOperationalClosureRegression.positive_grouping_collision_is_computed
#print axioms TarskiOperationalClosureRegression.positive_grouping_events_are_equal
#print axioms TarskiOperationalClosureRegression.close_is_a_real_phase_change
#print axioms TarskiOperationalClosureRegression.source_positions_are_preserved
#print axioms TarskiOperationalClosureRegression.terminal_occurrences_are_the_master_occurrences
#print axioms TarskiOperationalClosureRegression.identity_terminals_are_distinct
#print axioms TarskiOperationalClosureRegression.terminal_separator_is_immediate
#print axioms TarskiOperationalClosureRegression.every_exact_realization_separates_terminals
#print axioms TarskiOperationalClosureRegression.positiveIdentityCorrespondence
#print axioms TarskiOperationalClosureRegression.PolefulObservation.Event
#print axioms TarskiOperationalClosureRegression.PolefulObservation.sourceEvent
#print axioms TarskiOperationalClosureRegression.PolefulObservation.reducedEvent
#print axioms TarskiOperationalClosureRegression.PolefulObservation.sourceContract
#print axioms TarskiOperationalClosureRegression.PolefulObservation.reducedContract
#print axioms TarskiOperationalClosureRegression.PolefulObservation.realization
#print axioms TarskiOperationalClosureRegression.PolefulObservation.closeRun
#print axioms TarskiOperationalClosureRegression.PolefulObservation.grouping
#print axioms TarskiOperationalClosureRegression.PolefulObservation.event_exact_holds
#print axioms TarskiOperationalClosureRegression.PolefulObservation.terminal_collision_is_computed
#print axioms TarskiOperationalClosureRegression.PolefulObservation.close_traces_are_distinct
#print axioms TarskiOperationalClosureRegression.PolefulObservation.valueToCandidate
#print axioms TarskiOperationalClosureRegression.PolefulObservation.candidateToValue
#print axioms TarskiOperationalClosureRegression.PolefulObservation.exactClosureRejected
/- AXIOM_AUDIT_END -/
