import RelationalPerimeter.Constitution.Tarski.Readout
import RelationalPerimeter.Constitution.Continuation.ReadoutCorrespondence
import RelationalPerimeter.Constitution.Continuation.CommonMemoryGrouping

/-! A minimal closing runtime for one executed Tarski production.  Operational
projection forgets the pole only after the real active-to-terminal step.  This
module proves the affirmative passage from grouping plus terminal readout
correspondence to local adequacy; it does not import the diagonal rejection. -/
set_option genInjectivity false
set_option autoImplicit false
set_option linter.checkUnivs false
namespace StrongPerimetralTurning
open ConstitutiveSearch ConstitutiveSearch.ContinuationSignatures

universe uC uB uS uK uX uT u
variable {coding : TarskiDiagonalSyntax.{uC,uS,uK}}
  {refinement : TarskiExecutionRefinement.{uC,uB,uS,uK,uX} coding}
  {candidate : coding.Candidate}

inductive TarskiClosurePole where
  | value
  | candidate
  deriving DecidableEq

inductive TarskiRuntimePhase where
  | active
  | terminal
  deriving DecidableEq

inductive TarskiOperationalHistory where
  | root
  | closed
  deriving DecidableEq

structure TarskiClosureSource (execution : ExecutedTarskiProduction refinement candidate) where
  occurrences : ExecutedTarskiProductionOccurrences execution
  pole : TarskiClosurePole
  history : TarskiOperationalHistory
  phase : TarskiRuntimePhase

inductive TarskiRuntimeRequest : Type u where
  | close
  deriving DecidableEq

structure TarskiRuntimeEvent where
  beforePhase : TarskiRuntimePhase
  beforeHistory : TarskiOperationalHistory
  request : TarskiRuntimeRequest.{0}
  afterPhase : TarskiRuntimePhase
  afterHistory : TarskiOperationalHistory
  deriving DecidableEq

def TarskiRuntimeRequest.eraseUniverse : TarskiRuntimeRequest.{u} → TarskiRuntimeRequest.{0}
  | .close => .close

inductive TarskiOperationalAllow : TarskiRuntimePhase → TarskiRuntimeRequest.{u} → Type u
  | close : TarskiOperationalAllow .active .close

def tarskiOperationalDecision (phase : TarskiRuntimePhase)
    (request : TarskiRuntimeRequest.{u}) :
    PSum (TarskiOperationalAllow phase request)
      (TarskiOperationalAllow phase request → False) :=
  match phase, request with
  | .active, .close => .inl .close
  | .terminal, .close => .inr (fun witness => nomatch witness)

def tarskiNextHistory (phase : TarskiRuntimePhase) (_request : TarskiRuntimeRequest.{u}) :
    TarskiOperationalHistory → TarskiOperationalHistory
  | history => match phase with
    | .active => .closed
    | .terminal => history

def tarskiNextPhase (phase : TarskiRuntimePhase) (_request : TarskiRuntimeRequest.{u}) :
    TarskiRuntimePhase := match phase with
  | .active => .terminal
  | .terminal => .terminal

def tarskiRuntimeNext {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) (request : TarskiRuntimeRequest) :
    TarskiClosureSource execution :=
  { source with
    history := tarskiNextHistory source.phase request source.history
    phase := tarskiNextPhase source.phase request }

def tarskiRuntimeEvent {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) (request : TarskiRuntimeRequest) :
    TarskiRuntimeEvent :=
  let target := tarskiRuntimeNext source request
  ⟨source.phase, source.history, request.eraseUniverse, target.phase, target.history⟩

theorem tarskiRuntimeEvent_pole_blind
    {execution : ExecutedTarskiProduction refinement candidate}
    (occurrences : ExecutedTarskiProductionOccurrences execution)
    (history : TarskiOperationalHistory) (phase : TarskiRuntimePhase)
    (request : TarskiRuntimeRequest) :
    tarskiRuntimeEvent
        (⟨occurrences, .value, history, phase⟩ : TarskiClosureSource execution) request =
      tarskiRuntimeEvent
        (⟨occurrences, .candidate, history, phase⟩ : TarskiClosureSource execution) request := rfl

def tarskiEndpointAt
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :
    TarskiClosurePole → Type uT
  | .value => readout.Truth execution.production.sentence
  | .candidate => readout.Truth
      (coding.applyCandidate candidate execution.production.computedOutput)

def tarskiInitialize (execution : ExecutedTarskiProduction refinement candidate)
    (pole : TarskiClosurePole) : TarskiClosureSource execution :=
  ⟨execution.occurrences, pole, .root, .active⟩

def tarskiValueSource (execution : ExecutedTarskiProduction refinement candidate) :=
  tarskiInitialize execution .value

def tarskiCandidateSource (execution : ExecutedTarskiProduction refinement candidate) :=
  tarskiInitialize execution .candidate

theorem tarskiValueSource_ne_candidateSource
    (execution : ExecutedTarskiProduction refinement candidate) :
    tarskiValueSource execution ≠ tarskiCandidateSource execution := by
  intro same
  have poles := congrArg TarskiClosureSource.pole same
  cases poles

def tarskiClosureContract
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :
    FutureContract (TarskiClosureSource execution) TarskiRuntimeRequest
      (ULift.{uT + 1} TarskiRuntimeEvent) (Type uT) where
  next := tarskiRuntimeNext
  event := fun source request => ⟨tarskiRuntimeEvent source request⟩
  read := fun source => tarskiEndpointAt readout execution source.pole
  Allow := fun source request => TarskiOperationalAllow source.phase request
  decision := fun source request => tarskiOperationalDecision source.phase request

def tarskiSearchClose
    (_execution : ExecutedTarskiProduction refinement candidate) : TarskiRuntimeRequest := .close

def tarskiAuthorizeClose
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (pole : TarskiClosurePole) :
    (tarskiClosureContract readout execution).Allow
      (tarskiInitialize execution pole) (tarskiSearchClose execution) := .close

def tarskiDecomposeClose
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (pole : TarskiClosurePole) :=
  perform (tarskiClosureContract readout execution) (tarskiInitialize execution pole)
    (tarskiSearchClose execution) (tarskiAuthorizeClose readout execution pole)

def tarskiExecuteClose
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (pole : TarskiClosurePole) :
    ExecutedRun (tarskiClosureContract readout execution)
      (tarskiInitialize execution pole) [tarskiSearchClose execution]
      (tarskiRuntimeNext (tarskiInitialize execution pole) (tarskiSearchClose execution))
      [(tarskiClosureContract readout execution).event
        (tarskiInitialize execution pole) (tarskiSearchClose execution)] :=
  .cons (tarskiDecomposeClose readout execution pole) (.nil _)

theorem tarskiClose_changes_phase
    (execution : ExecutedTarskiProduction refinement candidate) (pole : TarskiClosurePole) :
    (tarskiRuntimeNext (tarskiInitialize execution pole) (.close)).phase = .terminal := rfl

theorem tarskiRuntimeNext_pole
    {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) (request : TarskiRuntimeRequest) :
    (tarskiRuntimeNext source request).pole = source.pole := rfl

theorem tarskiRuntimeNext_occurrences
    {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) (request : TarskiRuntimeRequest) :
    (tarskiRuntimeNext source request).occurrences = source.occurrences := rfl

theorem tarskiRuntimeRun_pole
    {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) (requests : List TarskiRuntimeRequest) :
    (Grouping.Continuation.run tarskiRuntimeNext source requests).pole = source.pole := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
      exact (ih (tarskiRuntimeNext source request)).trans
        (tarskiRuntimeNext_pole source request)

theorem tarskiRuntimeRun_occurrences
    {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) (requests : List TarskiRuntimeRequest) :
    (Grouping.Continuation.run tarskiRuntimeNext source requests).occurrences =
      source.occurrences := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
      exact (ih (tarskiRuntimeNext source request)).trans
        (tarskiRuntimeNext_occurrences source request)

inductive TarskiOperationalMemory
    (execution : ExecutedTarskiProduction refinement candidate) where
  | active (occurrences : ExecutedTarskiProductionOccurrences execution)
      (pole : TarskiClosurePole) (history : TarskiOperationalHistory)
  | grouped (occurrences : ExecutedTarskiProductionOccurrences execution)
      (history : TarskiOperationalHistory)

namespace TarskiOperationalMemory
variable {execution : ExecutedTarskiProduction refinement candidate}

def phase : TarskiOperationalMemory execution → TarskiRuntimePhase
  | .active _ _ _ => .active
  | .grouped _ _ => .terminal

def history : TarskiOperationalMemory execution → TarskiOperationalHistory
  | .active _ _ history => history
  | .grouped _ history => history

end TarskiOperationalMemory

def tarskiOperationalProject {execution : ExecutedTarskiProduction refinement candidate}
    (source : TarskiClosureSource execution) : TarskiOperationalMemory execution :=
  match source.phase with
  | .active => .active source.occurrences source.pole source.history
  | .terminal => .grouped source.occurrences source.history

def tarskiOperationalNext {execution : ExecutedTarskiProduction refinement candidate} :
    TarskiOperationalMemory execution → TarskiRuntimeRequest →
      TarskiOperationalMemory execution
  | .active occurrences _ _, .close => .grouped occurrences .closed
  | memory@(.grouped _ _), .close => memory

def tarskiOperationalEvent {execution : ExecutedTarskiProduction refinement candidate}
    (memory : TarskiOperationalMemory execution) (request : TarskiRuntimeRequest) :
    TarskiRuntimeEvent :=
  let target := tarskiOperationalNext memory request
  ⟨memory.phase, memory.history, request.eraseUniverse, target.phase, target.history⟩

def tarskiOperationalContract (execution : ExecutedTarskiProduction refinement candidate) :
    OperationalContract (TarskiOperationalMemory execution) TarskiRuntimeRequest
      (ULift.{uT + 1} TarskiRuntimeEvent) where
  next := tarskiOperationalNext
  event := fun memory request => ⟨tarskiOperationalEvent memory request⟩
  Allow := fun memory request => TarskiOperationalAllow memory.phase request
  decision := fun memory request => tarskiOperationalDecision memory.phase request

def tarskiOperationalRealization
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :
    OperationalRealization (tarskiClosureContract readout execution)
      (TarskiOperationalMemory execution) where
  reduced := tarskiOperationalContract execution
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

def tarskiValueTerminal (execution : ExecutedTarskiProduction refinement candidate) :=
  tarskiRuntimeNext (tarskiValueSource execution)
    (TarskiRuntimeRequest.close : TarskiRuntimeRequest.{max uB uS uK uX})

def tarskiCandidateTerminal (execution : ExecutedTarskiProduction refinement candidate) :=
  tarskiRuntimeNext (tarskiCandidateSource execution)
    (TarskiRuntimeRequest.close : TarskiRuntimeRequest.{max uB uS uK uX})

theorem tarskiValueTerminal_occurrences
    (execution : ExecutedTarskiProduction refinement candidate) :
    (tarskiValueTerminal execution).occurrences = execution.occurrences := rfl

theorem tarskiCandidateTerminal_occurrences
    (execution : ExecutedTarskiProduction refinement candidate) :
    (tarskiCandidateTerminal execution).occurrences = execution.occurrences := rfl

def tarskiExecutedOperationalGrouping
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :
    ExecutedOperationalGrouping (tarskiOperationalRealization readout execution)
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution) where
  trace := ⟨.close, []⟩
  leftEvents := [(tarskiClosureContract readout execution).event
    (tarskiValueSource execution) .close]
  leftRun := tarskiExecuteClose readout execution .value
  rightEvents := [(tarskiClosureContract readout execution).event
    (tarskiCandidateSource execution) .close]
  rightRun := tarskiExecuteClose readout execution .candidate
  terminalCollision := rfl

/-- The stronger positive witness records that the common-memory execution is
also observationally common at the event level.  This is where the declared
pole-blindness of the operational event is used; it is not a hidden premise of
the later memory/readout argument. -/
structure TarskiObservedOperationalGrouping
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) where
  grouping : ExecutedOperationalGrouping (tarskiOperationalRealization readout execution)
    (tarskiValueSource execution) (tarskiCandidateSource execution)
    (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)
  eventsEqual : grouping.leftEvents = grouping.rightEvents

def tarskiObservedOperationalGrouping
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :
    TarskiObservedOperationalGrouping readout execution where
  grouping := tarskiExecutedOperationalGrouping readout execution
  eventsEqual := by
    change [ULift.up (tarskiRuntimeEvent (tarskiValueSource execution) .close)] =
      [ULift.up (tarskiRuntimeEvent (tarskiCandidateSource execution) .close)]
    exact congrArg (fun event : TarskiRuntimeEvent => [ULift.up event])
      (tarskiRuntimeEvent_pole_blind execution.occurrences .root .active .close)

theorem tarskiOperational_initial_memories_distinct
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :
    (tarskiOperationalRealization readout execution).project (tarskiValueSource execution) ≠
      (tarskiOperationalRealization readout execution).project
        (tarskiCandidateSource execution) := by
  intro same
  cases same

def tarskiIdentityRealization
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :=
  identityRealization (tarskiClosureContract readout execution)

def tarskiIdentityTerminalCorrespondence
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate) :=
  (tarskiIdentityRealization readout execution).terminalReadoutCorrespondence
    (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)

theorem tarskiIdentityTerminalsDistinct
    (execution : ExecutedTarskiProduction refinement candidate) :
    tarskiValueTerminal execution ≠ tarskiCandidateTerminal execution := by
  intro same
  have poles := congrArg TarskiClosureSource.pole same
  cases poles

theorem tarskiTerminalRead_value
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    {requests : List TarskiRuntimeRequest}
    {terminal : TarskiClosureSource execution} {events}
    (run : ExecutedRun (tarskiClosureContract readout execution)
      (tarskiValueSource execution) requests terminal events) :
    (tarskiClosureContract readout execution).read terminal =
      readout.Truth execution.production.sentence := by
  have terminalEq := run.terminal_eq_run
  have poleEq := congrArg TarskiClosureSource.pole terminalEq
  have runPole := tarskiRuntimeRun_pole (tarskiValueSource execution) requests
  have terminalPole : terminal.pole = TarskiClosurePole.value := poleEq.trans runPole
  change tarskiEndpointAt readout execution terminal.pole = _
  rw [terminalPole]
  rfl

theorem tarskiTerminalRead_candidate
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    {requests : List TarskiRuntimeRequest}
    {terminal : TarskiClosureSource execution} {events}
    (run : ExecutedRun (tarskiClosureContract readout execution)
      (tarskiCandidateSource execution) requests terminal events) :
    (tarskiClosureContract readout execution).read terminal =
      readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) := by
  have terminalEq := run.terminal_eq_run
  have poleEq := congrArg TarskiClosureSource.pole terminalEq
  have runPole := tarskiRuntimeRun_pole (tarskiCandidateSource execution) requests
  have terminalPole : terminal.pole = TarskiClosurePole.candidate := poleEq.trans runPole
  change tarskiEndpointAt readout execution terminal.pole = _
  rw [terminalPole]
  rfl

def tarskiExecutedGroupingValueToCandidate
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization leftTerminal rightTerminal) :
    readout.Truth execution.production.sentence →
      readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) := by
  have leftRead := tarskiTerminalRead_value readout execution grouping.leftRun
  have rightRead := tarskiTerminalRead_candidate readout execution grouping.rightRun
  exact fun value =>
    Eq.mp rightRead
      (grouping.directedReadout preservation (Eq.mp leftRead.symm value))

def tarskiExecutedGroupingCandidateToValue
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (preservation : DirectedTerminalReadoutPreservation
      realization rightTerminal leftTerminal) :
    readout.Truth
        (coding.applyCandidate candidate execution.production.computedOutput) →
      readout.Truth execution.production.sentence := by
  have leftRead := tarskiTerminalRead_value readout execution grouping.leftRun
  have rightRead := tarskiTerminalRead_candidate readout execution grouping.rightRun
  exact fun candidateValue =>
    Eq.mp leftRead
      (grouping.reverseDirectedReadout preservation (Eq.mp rightRead.symm candidateValue))

def tarskiExecutedGroupingToLocalAdequacyDirected
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (valueToCandidate : DirectedTerminalReadoutPreservation
      realization leftTerminal rightTerminal)
    (candidateToValue : DirectedTerminalReadoutPreservation
      realization rightTerminal leftTerminal) :
    TarskiLocalAdequacy readout execution where
  valueToCandidate := tarskiExecutedGroupingValueToCandidate readout execution
    realization grouping valueToCandidate
  candidateToValue := tarskiExecutedGroupingCandidateToValue readout execution
    realization grouping candidateToValue

def tarskiExecutedGroupingToLocalAdequacy
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    {Memory : Type (max uB uS uK uX)}
    (realization : OperationalRealization (tarskiClosureContract readout execution) Memory)
    {leftTerminal rightTerminal : TarskiClosureSource execution}
    (grouping : ExecutedOperationalGrouping realization
      (tarskiValueSource execution) (tarskiCandidateSource execution)
      leftTerminal rightTerminal)
    (correspondence : TerminalReadoutCorrespondence realization leftTerminal rightTerminal) :
    TarskiLocalAdequacy readout execution :=
  tarskiExecutedGroupingToLocalAdequacyDirected readout execution realization grouping
    correspondence.leftToRightPreservation correspondence.rightToLeftPreservation

def tarskiObservedGroupingToLocalAdequacy
    (readout : TarskiReadout.{uC,uS,uK,uT} coding)
    (execution : ExecutedTarskiProduction refinement candidate)
    (observed : TarskiObservedOperationalGrouping readout execution)
    (correspondence : TerminalReadoutCorrespondence
      (tarskiOperationalRealization readout execution)
      (tarskiValueTerminal execution) (tarskiCandidateTerminal execution)) :
    TarskiLocalAdequacy readout execution :=
  tarskiExecutedGroupingToLocalAdequacy readout execution
    (tarskiOperationalRealization readout execution) observed.grouping correspondence

end StrongPerimetralTurning
/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.TarskiClosureSource
#print axioms StrongPerimetralTurning.tarskiRuntimeNext
#print axioms StrongPerimetralTurning.tarskiRuntimeEvent_pole_blind
#print axioms StrongPerimetralTurning.tarskiClosureContract
#print axioms StrongPerimetralTurning.tarskiSearchClose
#print axioms StrongPerimetralTurning.tarskiAuthorizeClose
#print axioms StrongPerimetralTurning.tarskiDecomposeClose
#print axioms StrongPerimetralTurning.tarskiExecuteClose
#print axioms StrongPerimetralTurning.tarskiClose_changes_phase
#print axioms StrongPerimetralTurning.tarskiValueSource_ne_candidateSource
#print axioms StrongPerimetralTurning.tarskiRuntimeNext_occurrences
#print axioms StrongPerimetralTurning.tarskiRuntimeRun_occurrences
#print axioms StrongPerimetralTurning.TarskiOperationalMemory
#print axioms StrongPerimetralTurning.tarskiOperationalRealization
#print axioms StrongPerimetralTurning.tarskiExecutedOperationalGrouping
#print axioms StrongPerimetralTurning.TarskiObservedOperationalGrouping
#print axioms StrongPerimetralTurning.tarskiObservedOperationalGrouping
#print axioms StrongPerimetralTurning.tarskiOperational_initial_memories_distinct
#print axioms StrongPerimetralTurning.tarskiIdentityRealization
#print axioms StrongPerimetralTurning.tarskiIdentityTerminalCorrespondence
#print axioms StrongPerimetralTurning.tarskiIdentityTerminalsDistinct
#print axioms StrongPerimetralTurning.tarskiValueTerminal_occurrences
#print axioms StrongPerimetralTurning.tarskiCandidateTerminal_occurrences
#print axioms StrongPerimetralTurning.tarskiTerminalRead_value
#print axioms StrongPerimetralTurning.tarskiTerminalRead_candidate
#print axioms StrongPerimetralTurning.tarskiExecutedGroupingValueToCandidate
#print axioms StrongPerimetralTurning.tarskiExecutedGroupingCandidateToValue
#print axioms StrongPerimetralTurning.tarskiExecutedGroupingToLocalAdequacyDirected
#print axioms StrongPerimetralTurning.tarskiExecutedGroupingToLocalAdequacy
#print axioms StrongPerimetralTurning.tarskiObservedGroupingToLocalAdequacy
/- AXIOM_AUDIT_END -/
