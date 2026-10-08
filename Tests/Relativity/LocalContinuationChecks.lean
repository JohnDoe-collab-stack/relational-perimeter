import RelationalPerimeter

/-! Public consumers of the candidate's fixed contract. No geometry claim. -/
set_option genInjectivity false
namespace Tests.Relativity.LocalContinuationChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := Cursor.received input

def initialReadingMayBeUsed : PermittedUse source ⟨.reading, .here⟩ :=
  permittedUse (source := source) emission .here (.emissionReading .here (.prior .here))

theorem permitted_does_not_mean_executed {one two : Occurrence receivedKinds}
    (edge : Used source.formation one two) : False := received_has_no_used_edge input edge

def emittedReadingEdge :
    Used (perform source emission).successor.formation
      (oldOccurrence .signal ⟨.reading, .here⟩) (freshOccurrence receivedKinds .signal) :=
  executedPort (perform source emission).determination .here (.emissionReading .here (.prior .here))

theorem emittedReadingEdge_no_reverse
    (back : Used (perform source emission).successor.formation
      (freshOccurrence receivedKinds .signal) (oldOccurrence .signal ⟨.reading, .here⟩)) : False :=
  Nat.lt_irrefl _ (Nat.lt_trans back.position_decreases emittedReadingEdge.position_decreases)

def emittedReadingPath := UsedPath.single emittedReadingEdge

def emittedReadingPath_after_receive :=
  emittedReadingPath.extend (perform (perform source emission).successor (.receive .here)).determination.2

def emittedReadingEdge_after_requests (execution : RequestedExecution (perform source emission).successor) :=
  execution.transportUsed emittedReadingEdge

def emittedReadingPath_after_requests (execution : RequestedExecution (perform source emission).successor) :=
  execution.transportPath emittedReadingPath

theorem available_inspection_exact (start : Cursor) {kind} (ref : Ref start.kinds kind) :
    (performRequest start (.inspect kind ref.position)).event = .inspected (localReadout kind (start.read ref)) :=
  (performRequest_event_exact start _).trans (inspection_reference_exact start ref)

theorem unavailable_receive_refused : admissionEnabled source (.receive 0) = false := rfl

theorem wrong_sort_refused : admissionEnabled source (.inspect .signal 1) = false := rfl

theorem out_of_range_refused : admissionEnabled source (.inspect .reading 100) = false := by decide

def admitted_emission : LocalAdmission source (.emit 0 1) :=
  (⟨.here, rfl⟩, ⟨.prior .here, rfl⟩)

theorem refused_receive_keeps_cursor : (performRequest source (.receive 0)).cursor = source := rfl

theorem successful_emission_creates_one_resource :
    (performRequest source (.emit 0 1)).cursor.kinds = .signal :: receivedKinds := rfl

def interleavedRequests : List LocalRequest :=
  [.receive 0, .inspect .reading 0, .emit 0 1, .relay 0 3, .receive 0, .inspect .reading 0]

theorem all_interleaved_futures_exact (start : Cursor) (requests : List LocalRequest) :
    (runRequests start requests).report = localContract.outcome start requests :=
  requests_all_futures_exact start requests

theorem example_has_three_productions :
    StrongPerimetralTurning.History.length (runRequests source interleavedRequests).history = 3 := by decide

theorem interleaved_keeps_initial_reading :
    (runRequests source interleavedRequests).cursor.read
      ((historyTransport (runRequests source interleavedRequests).history).references
        (Ref.here : Ref receivedKinds .reading)) = input.reading :=
  requests_preserve_old_readings source interleavedRequests .here

def relayed : RequestedExecution source := runRequests source [.emit 0 1, .relay 0 3, .relay 0 4]
def reemitted : RequestedExecution relayed.cursor := relayed.continue [.receive 0, .emit 0 5]

theorem same_final_signal_reading :
    (relayed.cursor.read (Ref.here : Ref relayed.cursor.kinds .signal)).reading =
      (reemitted.cursor.read (Ref.here : Ref reemitted.cursor.kinds .signal)).reading := by decide

def firstSignalLength : Outcome LocalEvent Unit → Option Nat
  | .stop _ => none
  | .step _ _ event _ => event.observedSignal.map (fun signal => signal.increments.length)

def signalReadoutLength : LocalReadout → Option Nat
  | .reading _ => none
  | .payload _ => none
  | .calibration _ => none
  | .signal signal => some signal.increments.length

theorem path_record_is_future_separable :
    ¬ FutureEquivalent localContract relayed.cursor reemitted.cursor := by
  intro same
  have records := futures_preserve_available_readout relayed.cursor reemitted.cursor
    (Ref.here : Ref relayed.cursor.kinds .signal) (Ref.here : Ref reemitted.cursor.kinds .signal) rfl same
  have separated := congrArg signalReadoutLength records
  change (some 2 : Option Nat) = some 0 at separated
  cases separated

theorem resumed_report_exact :
    reemitted.report = localContract.outcome relayed.cursor [.receive 0, .emit 0 5] :=
  continuation_all_futures_exact relayed [.receive 0, .emit 0 5]

theorem combined_continuation_has_five_productions :
    StrongPerimetralTurning.History.length (relayed.continuedHistory reemitted) = 5 := by decide

theorem continuation_composition_uses_stored_history :
    relayed.continuedHistory reemitted =
      StrongPerimetralTurning.History.append relayed.history reemitted.history := rfl

-- Executability only, not a physical or complexity measurement.
#eval firstSignalLength (runRequests relayed.cursor [.inspect .signal 0]).report
#eval firstSignalLength (runRequests reemitted.cursor [.inspect .signal 0]).report

end Tests.Relativity.LocalContinuationChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.LocalContinuationChecks.initialReadingMayBeUsed
#print axioms Tests.Relativity.LocalContinuationChecks.permitted_does_not_mean_executed
#print axioms Tests.Relativity.LocalContinuationChecks.emittedReadingEdge
#print axioms Tests.Relativity.LocalContinuationChecks.emittedReadingEdge_no_reverse
#print axioms Tests.Relativity.LocalContinuationChecks.emittedReadingPath_after_receive
#print axioms Tests.Relativity.LocalContinuationChecks.emittedReadingEdge_after_requests
#print axioms Tests.Relativity.LocalContinuationChecks.emittedReadingPath_after_requests
#print axioms Tests.Relativity.LocalContinuationChecks.available_inspection_exact
#print axioms Tests.Relativity.LocalContinuationChecks.unavailable_receive_refused
#print axioms Tests.Relativity.LocalContinuationChecks.wrong_sort_refused
#print axioms Tests.Relativity.LocalContinuationChecks.out_of_range_refused
#print axioms Tests.Relativity.LocalContinuationChecks.refused_receive_keeps_cursor
#print axioms Tests.Relativity.LocalContinuationChecks.successful_emission_creates_one_resource
#print axioms Tests.Relativity.LocalContinuationChecks.all_interleaved_futures_exact
#print axioms Tests.Relativity.LocalContinuationChecks.example_has_three_productions
#print axioms Tests.Relativity.LocalContinuationChecks.interleaved_keeps_initial_reading
#print axioms Tests.Relativity.LocalContinuationChecks.same_final_signal_reading
#print axioms Tests.Relativity.LocalContinuationChecks.signalReadoutLength
#print axioms Tests.Relativity.LocalContinuationChecks.path_record_is_future_separable
#print axioms Tests.Relativity.LocalContinuationChecks.resumed_report_exact
#print axioms Tests.Relativity.LocalContinuationChecks.combined_continuation_has_five_productions
#print axioms Tests.Relativity.LocalContinuationChecks.continuation_composition_uses_stored_history
/- AXIOM_AUDIT_END -/
