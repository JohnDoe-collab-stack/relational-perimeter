import RelationalPerimeter.Relativity.Production.ArrivalComparisons
import RelationalPerimeter.Relativity.Production.LocalFutureContract

/-!
# Explicit futures after the constituted arrival comparison

This contract fixes the closed instrumental law of `InstrumentFormation`:
one already produced comparison, then arbitrary finite interleavings of
emission, relay, reception and full typed-resource inspection, including
refusals. It does not include a second comparison or claim the final physical
contract. The earlier signal-only contract is unchanged.

Admission is constructed from the current support. The executable runner
shares one determination between the successor, event and founded history;
the separate next/event projections below are only the reference specification.
No comparison is reconstructed by a future request or a continuation.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def InstrumentAdmission (source : InstrumentCursor) : LocalRequest → Type
  | .emit reading payload =>
      ReferenceAt source.kinds .reading reading × ReferenceAt source.kinds .payload payload
  | .relay signal calibration =>
      ReferenceAt source.kinds .signal signal × ReferenceAt source.kinds .calibration calibration
  | .receive signal => ReferenceAt source.kinds .signal signal
  | .inspect kind position => ReferenceAt source.kinds kind position

def decideInstrumentAdmission (source : InstrumentCursor) (request : LocalRequest) :
    PSum (InstrumentAdmission source request) (InstrumentAdmission source request → False) :=
  match request with
  | .emit reading payload => pairDecision (resolve source.kinds .reading reading)
      (resolve source.kinds .payload payload)
  | .relay signal calibration => pairDecision (resolve source.kinds .signal signal)
      (resolve source.kinds .calibration calibration)
  | .receive signal => resolve source.kinds .signal signal
  | .inspect kind position => resolve source.kinds kind position

def instrumentEnabled (source : InstrumentCursor) (request : LocalRequest) : Bool :=
  match decideInstrumentAdmission source request with | .inl _ => true | .inr _ => false

def instrumentAdmissionOfEnabled (source : InstrumentCursor) (request : LocalRequest)
    (yes : instrumentEnabled source request = true) : InstrumentAdmission source request := by
  cases chosen : decideInstrumentAdmission source request with
  | inl admitted => exact admitted
  | inr impossible => unfold instrumentEnabled at yes; rw [chosen] at yes; cases yes

theorem instrument_refusal_refutes (source : InstrumentCursor) (request : LocalRequest)
    (no : instrumentEnabled source request = false) (admitted : InstrumentAdmission source request) : False := by
  cases chosen : decideInstrumentAdmission source request with
  | inl witness => unfold instrumentEnabled at no; rw [chosen] at no; cases no
  | inr impossible => exact impossible admitted

def instrumentAdmittedNext (source : InstrumentCursor) :
    (request : LocalRequest) → InstrumentAdmission source request → InstrumentCursor
  | .emit _ _, admitted => source.extend (execute source.values (.emit admitted.1.ref admitted.2.ref))
  | .relay _ _, admitted => source.extend (execute source.values (.relay admitted.1.ref admitted.2.ref))
  | .receive _, admitted => source.extend (execute source.values (.receive admitted.ref))
  | .inspect _ _, _ => source

def instrumentAdmittedEvent (source : InstrumentCursor) :
    (request : LocalRequest) → InstrumentAdmission source request → LocalEvent
  | .emit _ _, admitted => .emitted ((Instruction.emit admitted.1.ref admitted.2.ref).interpret source.values)
  | .relay _ _, admitted => .relayed ((Instruction.relay admitted.1.ref admitted.2.ref).interpret source.values)
  | .receive _, admitted => .received ((Instruction.receive admitted.ref).interpret source.values)
  | .inspect kind _, admitted => .inspected (localReadout kind (source.read admitted.ref))

def instrumentReferenceNext (source : InstrumentCursor) (request : LocalRequest) : InstrumentCursor :=
  match decideInstrumentAdmission source request with
  | .inl admitted => instrumentAdmittedNext source request admitted
  | .inr _ => source

def instrumentReferenceEvent (source : InstrumentCursor) (request : LocalRequest) : LocalEvent :=
  match decideInstrumentAdmission source request with
  | .inl admitted => instrumentAdmittedEvent source request admitted
  | .inr _ => .refused

def instrumentContract : FutureContract InstrumentCursor LocalRequest LocalEvent Unit where
  next := instrumentReferenceNext
  event := instrumentReferenceEvent
  read := fun _ => ()
  Allow := InstrumentAdmission
  decision := decideInstrumentAdmission

theorem instrument_contract_enabled_exact (source : InstrumentCursor) (request : LocalRequest) :
    instrumentContract.enabled source request = instrumentEnabled source request := by
  dsimp only [FutureContract.enabled, instrumentContract, instrumentEnabled, FutureContract.decision]
  cases decideInstrumentAdmission source request <;> rfl

theorem instrument_refused_next (source : InstrumentCursor) (request : LocalRequest)
    (no : instrumentEnabled source request = false) : instrumentReferenceNext source request = source := by
  unfold instrumentReferenceNext
  cases decideInstrumentAdmission source request with
  | inl admitted => exact False.elim (instrument_refusal_refutes source request no admitted)
  | inr _ => rfl

theorem instrument_refused_event (source : InstrumentCursor) (request : LocalRequest)
    (no : instrumentEnabled source request = false) : instrumentReferenceEvent source request = .refused := by
  unfold instrumentReferenceEvent
  cases decideInstrumentAdmission source request with
  | inl admitted => exact False.elim (instrument_refusal_refutes source request no admitted)
  | inr _ => rfl

theorem instrument_inspection_exact (source : InstrumentCursor) {kind} (ref : Ref source.kinds kind) :
    instrumentReferenceEvent source (.inspect kind ref.position) = .inspected (localReadout kind (source.read ref)) := by
  unfold instrumentReferenceEvent
  cases decideInstrumentAdmission source (.inspect kind ref.position) with
  | inl admitted =>
    dsimp only [instrumentAdmittedEvent]
    rw [reference_position_injective admitted.ref ref admitted.exactPosition]
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

theorem instrument_inspection_enabled (source : InstrumentCursor) {kind} (ref : Ref source.kinds kind) :
    instrumentEnabled source (.inspect kind ref.position) = true := by
  unfold instrumentEnabled
  cases decideInstrumentAdmission source (.inspect kind ref.position) with
  | inl _ => rfl
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

/-- A differing full record is a positive finite separator for this contract.
This necessary condition does not identify source occurrences and is not a
minimality theorem for the future physical contract. -/
theorem instrument_futures_preserve_readout (source target : InstrumentCursor) {kind}
    (one : Ref source.kinds kind) (two : Ref target.kinds kind)
    (samePosition : two.position = one.position)
    (same : FutureEquivalent instrumentContract source target) :
    localReadout kind (source.read one) = localReadout kind (target.read two) := by
  have observed := congrArg firstInspection (same [.inspect kind one.position])
  dsimp only [FutureContract.outcome, instrumentContract] at observed
  rw [instrument_inspection_exact source one, ← samePosition, instrument_inspection_exact target two] at observed
  exact Option.some.inj observed

structure InstrumentResponse (source : InstrumentCursor) where
  cursor : InstrumentCursor
  event : LocalEvent
  allowed : Bool
  history : InstrumentHistory source cursor

def instrumentProductionHistory {source : InstrumentCursor} {kind}
    {instruction : Instruction source.kinds kind} (head : InstrumentProduction source instruction) :
    InstrumentHistory source head.successor :=
  .extend .root ⟨kind, instruction, head.determination, head.successorExact⟩

def performInstrumentAdmitted (source : InstrumentCursor) :
    (request : LocalRequest) → InstrumentAdmission source request → InstrumentResponse source
  | .emit _ _, admitted =>
    let head := performInstrument source (.emit admitted.1.ref admitted.2.ref)
    ⟨head.successor, .emitted head.determination.1, true, instrumentProductionHistory head⟩
  | .relay _ _, admitted =>
    let head := performInstrument source (.relay admitted.1.ref admitted.2.ref)
    ⟨head.successor, .relayed head.determination.1, true, instrumentProductionHistory head⟩
  | .receive _, admitted =>
    let head := performInstrument source (.receive admitted.ref)
    ⟨head.successor, .received head.determination.1, true, instrumentProductionHistory head⟩
  | .inspect kind _, admitted =>
    ⟨source, .inspected (localReadout kind (source.read admitted.ref)), true, .root⟩

def performInstrumentRequest (source : InstrumentCursor) (request : LocalRequest) : InstrumentResponse source :=
  match decideInstrumentAdmission source request with
  | .inl admitted => performInstrumentAdmitted source request admitted
  | .inr _ => ⟨source, .refused, false, .root⟩

theorem instrument_inspection_response (source : InstrumentCursor) {kind} (ref : Ref source.kinds kind) :
    performInstrumentRequest source (.inspect kind ref.position) =
      ⟨source, .inspected (localReadout kind (source.read ref)), true, .root⟩ := by
  unfold performInstrumentRequest
  cases decideInstrumentAdmission source (.inspect kind ref.position) with
  | inl admitted =>
    dsimp only [performInstrumentAdmitted]
    rw [reference_position_injective admitted.ref ref admitted.exactPosition]
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

theorem instrument_admitted_next_exact (source : InstrumentCursor) (request : LocalRequest)
    (admitted : InstrumentAdmission source request) :
    (performInstrumentAdmitted source request admitted).cursor = instrumentAdmittedNext source request admitted := by
  cases request <;> rfl

theorem instrument_admitted_event_exact (source : InstrumentCursor) (request : LocalRequest)
    (admitted : InstrumentAdmission source request) :
    (performInstrumentAdmitted source request admitted).event = instrumentAdmittedEvent source request admitted := by
  cases request <;> rfl

theorem instrument_admitted_allowed (source : InstrumentCursor) (request : LocalRequest)
    (admitted : InstrumentAdmission source request) :
    (performInstrumentAdmitted source request admitted).allowed = true := by cases request <;> rfl

theorem instrument_request_next_exact (source : InstrumentCursor) (request : LocalRequest) :
    (performInstrumentRequest source request).cursor = instrumentContract.next source request := by
  dsimp only [instrumentContract, FutureContract.next]
  unfold performInstrumentRequest instrumentReferenceNext
  cases decideInstrumentAdmission source request with
  | inl admitted => exact instrument_admitted_next_exact source request admitted
  | inr _ => rfl

theorem instrument_request_event_exact (source : InstrumentCursor) (request : LocalRequest) :
    (performInstrumentRequest source request).event = instrumentContract.event source request := by
  dsimp only [instrumentContract, FutureContract.event]
  unfold performInstrumentRequest instrumentReferenceEvent
  cases decideInstrumentAdmission source request with
  | inl admitted => exact instrument_admitted_event_exact source request admitted
  | inr _ => rfl

theorem instrument_request_allowed_exact (source : InstrumentCursor) (request : LocalRequest) :
    (performInstrumentRequest source request).allowed = instrumentContract.enabled source request := by
  rw [instrument_contract_enabled_exact]
  unfold performInstrumentRequest instrumentEnabled
  cases decideInstrumentAdmission source request with
  | inl admitted => exact instrument_admitted_allowed source request admitted
  | inr _ => rfl

theorem instrument_response_length_bound (source : InstrumentCursor) (request : LocalRequest) :
    StrongPerimetralTurning.History.length (performInstrumentRequest source request).history ≤ 1 := by
  unfold performInstrumentRequest
  cases decideInstrumentAdmission source request with
  | inl admitted => cases request <;> first | exact Nat.le_refl 1 | exact Nat.zero_le 1
  | inr _ => exact Nat.zero_le _

structure InstrumentRequestedExecution (source : InstrumentCursor) where
  cursor : InstrumentCursor
  history : InstrumentHistory source cursor
  report : Outcome LocalEvent Unit

def runInstrumentRequests (source : InstrumentCursor) : List LocalRequest → InstrumentRequestedExecution source
  | [] => ⟨source, .root, .stop ()⟩
  | request :: rest =>
    let head := performInstrumentRequest source request
    let suffix := runInstrumentRequests head.cursor rest
    ⟨suffix.cursor, StrongPerimetralTurning.History.append head.history suffix.history,
      .step () head.allowed head.event suffix.report⟩
termination_by structural requests => requests

theorem instrument_all_futures_exact (source : InstrumentCursor) (requests : List LocalRequest) :
    (runInstrumentRequests source requests).report = instrumentContract.outcome source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    change Outcome.step () _ _ _ = Outcome.step () _ _ _
    rw [instrument_request_allowed_exact, instrument_request_event_exact]
    apply congrArg (Outcome.step () _ _)
    exact (ih _).trans (congrArg (fun state => instrumentContract.outcome state rest)
      (instrument_request_next_exact source request))

theorem instrument_final_cursor_exact (source : InstrumentCursor) (requests : List LocalRequest) :
    (runInstrumentRequests source requests).cursor =
      ConstitutiveSearch.Grouping.Continuation.run instrumentContract.next source requests := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih =>
    exact (ih _).trans (congrArg
      (fun state => ConstitutiveSearch.Grouping.Continuation.run instrumentContract.next state rest)
      (instrument_request_next_exact source request))

/-- A count of actual productions, not elapsed time or a work bound. Reads
and refusals add no production; each admitted action adds one shared role. -/
theorem instrument_request_history_bound (source : InstrumentCursor) (requests : List LocalRequest) :
    StrongPerimetralTurning.History.length (runInstrumentRequests source requests).history ≤ requests.length := by
  induction requests generalizing source with
  | nil => exact Nat.le_refl _
  | cons request rest ih =>
    change StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _) ≤ _
    exact Nat.le_trans (Nat.le_of_eq (StrongPerimetralTurning.History.length_append
      (performInstrumentRequest source request).history
      (runInstrumentRequests (performInstrumentRequest source request).cursor rest).history))
      (Nat.le_trans (Nat.add_le_add (instrument_response_length_bound source request) (ih _))
        (Nat.le_of_eq (Nat.add_comm 1 rest.length)))

def InstrumentRequestedExecution.continue {source} (priorRun : InstrumentRequestedExecution source)
    (requests : List LocalRequest) : InstrumentRequestedExecution priorRun.cursor :=
  runInstrumentRequests priorRun.cursor requests

def InstrumentRequestedExecution.continuedHistory {source} (priorRun : InstrumentRequestedExecution source)
    (suffix : InstrumentRequestedExecution priorRun.cursor) : InstrumentHistory source suffix.cursor :=
  StrongPerimetralTurning.History.append priorRun.history suffix.history

theorem instrument_continuation_exact {source} (priorRun : InstrumentRequestedExecution source)
    (requests : List LocalRequest) :
    (priorRun.continue requests).report = instrumentContract.outcome priorRun.cursor requests :=
  instrument_all_futures_exact priorRun.cursor requests

def InstrumentRequestedExecution.transportUsed {source} (execution : InstrumentRequestedExecution source)
    {one two : Occurrence source.kinds} (edge : InstrumentUsed source.formation one two) :
    InstrumentUsed execution.cursor.formation
      ⟨one.1, (instrumentHistoryTransport execution.history).references one.2⟩
      ⟨two.1, (instrumentHistoryTransport execution.history).references two.2⟩ :=
  instrumentHistoryTransportUsed execution.history edge

theorem instrument_requests_preserve_reads (source : InstrumentCursor) (requests : List LocalRequest)
    {kind} (ref : Ref source.kinds kind) :
    (runInstrumentRequests source requests).cursor.read
      ((instrumentHistoryTransport (runInstrumentRequests source requests).history).references ref) = source.read ref :=
  (instrumentHistoryTransport (runInstrumentRequests source requests).history).reads ref

structure ComparedRequests {source : Cursor} (pair : ArrivalPair source) where
  head : ComparisonProduction pair
  continuation : InstrumentRequestedExecution head.successor

/-- A new comparison is produced before its requests. Repeated continuation
uses the stored record via `.continue`, not this initial constructor. -/
def runComparedRequests {source : Cursor} (pair : ArrivalPair source) (requests : List LocalRequest) :
    ComparedRequests pair :=
  let head := performComparison pair
  let continuation := runInstrumentRequests head.successor requests
  ⟨head, continuation⟩

theorem compared_requests_head_independent {source : Cursor} (pair : ArrivalPair source)
    (one two : List LocalRequest) : (runComparedRequests pair one).head = (runComparedRequests pair two).head := rfl

theorem compared_requests_all_futures {source : Cursor} (pair : ArrivalPair source) (requests : List LocalRequest) :
    (runComparedRequests pair requests).continuation.report =
      instrumentContract.outcome (runComparedRequests pair requests).head.successor requests :=
  instrument_all_futures_exact (performComparison pair).successor requests

def ComparedRequests.transport {source : Cursor} {pair : ArrivalPair source} (execution : ComparedRequests pair) :
    Support.Extension source.support execution.continuation.cursor.support :=
  (comparisonTransport execution.head).compose (instrumentHistoryTransport execution.continuation.history)

theorem compared_requests_keep_sources {source : Cursor} (pair : ArrivalPair source) (requests : List LocalRequest) :
    (runComparedRequests pair requests).transport.references pair.first ≠
      (runComparedRequests pair requests).transport.references pair.second :=
  fun same => pair.distinct ((runComparedRequests pair requests).transport.injective _ _ same)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InstrumentAdmission
#print axioms RelationalPerimeter.Relativity.Production.decideInstrumentAdmission
#print axioms RelationalPerimeter.Relativity.Production.instrumentEnabled
#print axioms RelationalPerimeter.Relativity.Production.instrumentAdmissionOfEnabled
#print axioms RelationalPerimeter.Relativity.Production.instrument_refusal_refutes
#print axioms RelationalPerimeter.Relativity.Production.instrumentAdmittedNext
#print axioms RelationalPerimeter.Relativity.Production.instrumentAdmittedEvent
#print axioms RelationalPerimeter.Relativity.Production.instrumentReferenceNext
#print axioms RelationalPerimeter.Relativity.Production.instrumentReferenceEvent
#print axioms RelationalPerimeter.Relativity.Production.instrumentContract
#print axioms RelationalPerimeter.Relativity.Production.instrument_contract_enabled_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_refused_next
#print axioms RelationalPerimeter.Relativity.Production.instrument_refused_event
#print axioms RelationalPerimeter.Relativity.Production.instrument_inspection_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_inspection_enabled
#print axioms RelationalPerimeter.Relativity.Production.instrument_futures_preserve_readout
#print axioms RelationalPerimeter.Relativity.Production.instrumentProductionHistory
#print axioms RelationalPerimeter.Relativity.Production.performInstrumentAdmitted
#print axioms RelationalPerimeter.Relativity.Production.performInstrumentRequest
#print axioms RelationalPerimeter.Relativity.Production.instrument_inspection_response
#print axioms RelationalPerimeter.Relativity.Production.instrument_admitted_next_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_admitted_event_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_admitted_allowed
#print axioms RelationalPerimeter.Relativity.Production.instrument_request_next_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_request_event_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_request_allowed_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_response_length_bound
#print axioms RelationalPerimeter.Relativity.Production.runInstrumentRequests
#print axioms RelationalPerimeter.Relativity.Production.instrument_all_futures_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_final_cursor_exact
#print axioms RelationalPerimeter.Relativity.Production.instrument_request_history_bound
#print axioms RelationalPerimeter.Relativity.Production.InstrumentRequestedExecution.continue
#print axioms RelationalPerimeter.Relativity.Production.InstrumentRequestedExecution.continuedHistory
#print axioms RelationalPerimeter.Relativity.Production.instrument_continuation_exact
#print axioms RelationalPerimeter.Relativity.Production.InstrumentRequestedExecution.transportUsed
#print axioms RelationalPerimeter.Relativity.Production.instrument_requests_preserve_reads
#print axioms RelationalPerimeter.Relativity.Production.runComparedRequests
#print axioms RelationalPerimeter.Relativity.Production.compared_requests_head_independent
#print axioms RelationalPerimeter.Relativity.Production.compared_requests_all_futures
#print axioms RelationalPerimeter.Relativity.Production.ComparedRequests.transport
#print axioms RelationalPerimeter.Relativity.Production.compared_requests_keep_sources
/- AXIOM_AUDIT_END -/
