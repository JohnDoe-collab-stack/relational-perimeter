import RelationalPerimeter.Relativity.Production.LocalFutureContract
import RelationalPerimeter.Relativity.Production.UsedDependencies

/-!
# Paired execution of the fixed local requests

Each action produces once, shares that result between its event and successor,
and stores the same determination in its history. Inspection and refusal do
not produce a resource. A suffix runs from the actual produced cursor. The
reference contract may compute projections separately; it is not this runner.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

structure LocalResponse (source : Cursor) where
  cursor : Cursor
  event : LocalEvent
  allowed : Bool
  history : LocalHistory source cursor

def cachedProductionHistory {source : Cursor} {kind}
    {instruction : Instruction source.kinds kind} (head : Production source instruction) :
    LocalHistory source head.successor :=
  .extend .root ⟨kind, instruction, head.determination, head.successorExact⟩

def performAdmitted (source : Cursor) :
    (request : LocalRequest) → LocalAdmission source request → LocalResponse source
  | .emit _ _, admitted =>
    let head := perform source (.emit admitted.1.ref admitted.2.ref)
    ⟨head.successor, .emitted head.determination.1, true, cachedProductionHistory head⟩
  | .relay _ _, admitted =>
    let head := perform source (.relay admitted.1.ref admitted.2.ref)
    ⟨head.successor, .relayed head.determination.1, true, cachedProductionHistory head⟩
  | .receive _, admitted =>
    let head := perform source (.receive admitted.ref)
    ⟨head.successor, .received head.determination.1, true, cachedProductionHistory head⟩
  | .inspect kind _, admitted =>
    ⟨source, .inspected (localReadout kind (source.read admitted.ref)), true, .root⟩

def performRequest (source : Cursor) (request : LocalRequest) : LocalResponse source :=
  match decideAdmission source request with
  | .inl admitted => performAdmitted source request admitted
  | .inr _ => ⟨source, .refused, false, .root⟩

theorem performAdmitted_cursor_exact (source : Cursor) (request : LocalRequest)
    (admitted : LocalAdmission source request) :
    (performAdmitted source request admitted).cursor = admittedNext source request admitted := by
  cases request <;> rfl

theorem performAdmitted_event_exact (source : Cursor) (request : LocalRequest)
    (admitted : LocalAdmission source request) :
    (performAdmitted source request admitted).event = admittedEvent source request admitted := by
  cases request <;> rfl

theorem performAdmitted_allowed (source : Cursor) (request : LocalRequest)
    (admitted : LocalAdmission source request) : (performAdmitted source request admitted).allowed = true := by
  cases request <;> rfl

theorem performRequest_cursor_exact (source : Cursor) (request : LocalRequest) :
    (performRequest source request).cursor = localContract.next source request := by
  dsimp only [localContract, FutureContract.next]
  unfold performRequest referenceNext
  cases decideAdmission source request with
  | inl admitted => exact performAdmitted_cursor_exact source request admitted
  | inr _ => rfl

theorem performRequest_event_exact (source : Cursor) (request : LocalRequest) :
    (performRequest source request).event = localContract.event source request := by
  dsimp only [localContract, FutureContract.event]
  unfold performRequest referenceEvent
  cases decideAdmission source request with
  | inl admitted => exact performAdmitted_event_exact source request admitted
  | inr _ => rfl

theorem performRequest_allowed_exact (source : Cursor) (request : LocalRequest) :
    (performRequest source request).allowed = localContract.enabled source request := by
  rw [contract_enabled_exact]
  unfold performRequest admissionEnabled
  cases decideAdmission source request with
  | inl admitted => exact performAdmitted_allowed source request admitted
  | inr _ => rfl

structure RequestedExecution (source : Cursor) where
  cursor : Cursor
  history : LocalHistory source cursor
  report : Outcome LocalEvent Unit

def runRequests (source : Cursor) : List LocalRequest → RequestedExecution source
  | [] => ⟨source, .root, .stop ()⟩
  | request :: rest =>
    let head := performRequest source request
    let suffix := runRequests head.cursor rest
    ⟨suffix.cursor, StrongPerimetralTurning.History.append head.history suffix.history,
      .step () head.allowed head.event suffix.report⟩
termination_by structural requests => requests

theorem requests_all_futures_exact (source : Cursor) (requests : List LocalRequest) :
    (runRequests source requests).report = localContract.outcome source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    change Outcome.step () _ _ _ = Outcome.step () _ _ _
    rw [performRequest_allowed_exact, performRequest_event_exact]
    apply congrArg (Outcome.step () _ _)
    exact (ih _).trans (congrArg (fun state => localContract.outcome state rest)
      (performRequest_cursor_exact source request))

theorem requests_final_cursor_exact (source : Cursor) (requests : List LocalRequest) :
    (runRequests source requests).cursor =
      ConstitutiveSearch.Grouping.Continuation.run localContract.next source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    exact (ih _).trans (congrArg
      (fun state => ConstitutiveSearch.Grouping.Continuation.run localContract.next state rest)
      (performRequest_cursor_exact source request))

/-- This result describes the new suffix. The caller retains the previous
execution; `continuedHistory` composes their actual histories without replay. -/
def RequestedExecution.continue {source} (priorRun : RequestedExecution source)
    (requests : List LocalRequest) : RequestedExecution priorRun.cursor :=
  runRequests priorRun.cursor requests

def RequestedExecution.continuedHistory {source} (priorRun : RequestedExecution source)
    (suffix : RequestedExecution priorRun.cursor) : LocalHistory source suffix.cursor :=
  StrongPerimetralTurning.History.append priorRun.history suffix.history

theorem continuation_all_futures_exact {source} (priorRun : RequestedExecution source)
    (requests : List LocalRequest) :
    (priorRun.continue requests).report = localContract.outcome priorRun.cursor requests :=
  requests_all_futures_exact priorRun.cursor requests

theorem requests_preserve_old_readings (source : Cursor) (requests : List LocalRequest)
    {kind} (ref : Ref source.kinds kind) :
    (runRequests source requests).cursor.read
      ((historyTransport (runRequests source requests).history).references ref) = source.read ref :=
  history_preserves_reads (runRequests source requests).history ref

def RequestedExecution.transportUsed {source : Cursor} (execution : RequestedExecution source)
    {one two : Occurrence source.kinds} (edge : Used source.formation one two) :
    Used execution.cursor.formation
      (extensionOccurrence (historyTransport execution.history) one)
      (extensionOccurrence (historyTransport execution.history) two) :=
  historyTransportUsed execution.history edge

def RequestedExecution.transportPath {source : Cursor} (execution : RequestedExecution source)
    {one two : Occurrence source.kinds} (path : UsedPath source.formation one two) :
    UsedPath execution.cursor.formation
      (extensionOccurrence (historyTransport execution.history) one)
      (extensionOccurrence (historyTransport execution.history) two) :=
  historyTransportPath execution.history path

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.cachedProductionHistory
#print axioms RelationalPerimeter.Relativity.Production.performAdmitted
#print axioms RelationalPerimeter.Relativity.Production.performRequest
#print axioms RelationalPerimeter.Relativity.Production.performRequest_cursor_exact
#print axioms RelationalPerimeter.Relativity.Production.performRequest_event_exact
#print axioms RelationalPerimeter.Relativity.Production.performRequest_allowed_exact
#print axioms RelationalPerimeter.Relativity.Production.runRequests
#print axioms RelationalPerimeter.Relativity.Production.requests_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.requests_final_cursor_exact
#print axioms RelationalPerimeter.Relativity.Production.RequestedExecution.continue
#print axioms RelationalPerimeter.Relativity.Production.RequestedExecution.continuedHistory
#print axioms RelationalPerimeter.Relativity.Production.continuation_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.requests_preserve_old_readings
#print axioms RelationalPerimeter.Relativity.Production.RequestedExecution.transportUsed
#print axioms RelationalPerimeter.Relativity.Production.RequestedExecution.transportPath
/- AXIOM_AUDIT_END -/
