import RelationalPerimeter

/-! Closed public client of the post-comparison contract. Both arrivals are
executed before the comparison. Smoke evaluations are not physical measures.
The tests keep full path records rather than replacing them by one reading. -/
set_option genInjectivity false
namespace Tests.Relativity.InstrumentFutureChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def arrivals : (source : Cursor) ×' ArrivalPair source :=
  let firstEmission := perform (.received input) emission
  let firstReception := perform firstEmission.successor (.receive .here)
  let secondEmission := perform firstReception.successor
    (.emit (.prior (.prior .here)) (.prior (.prior (.prior .here))))
  let secondReception := perform secondEmission.successor (.receive .here)
  let firstArrival := Arrived.inherited secondReception.determination.2
    (Arrived.inherited secondEmission.determination.2 (arrivalOfProduction firstReception))
  ⟨secondReception.successor, ⟨.prior (.prior .here), .here, .prior (.prior (.prior .here)), .prior .here,
    firstArrival, arrivalOfProduction secondReception, fun same =>
      fresh_distinct secondEmission.successor secondReception.determination (.prior .here) same.symm⟩⟩

def compared := runComparedRequests arrivals.2 []
def start := compared.head.successor

theorem comparison_zero_sources_distinct :
    compared.head.determination.1 = Rational.zero ∧ arrivals.2.first ≠ arrivals.2.second :=
  comparison_equal_readings_not_equal_sources arrivals.2 rfl

theorem actual_comparison_read_enabled : instrumentEnabled start (.inspect .reading 0) = true :=
  instrument_inspection_enabled start .here

theorem actual_comparison_read_exact :
    (performInstrumentRequest start (.inspect .reading 0)).event = .inspected (.reading Rational.zero) :=
  (instrument_request_event_exact start _).trans (instrument_inspection_exact start .here)

theorem wrong_kind_refused : instrumentEnabled start (.receive 0) = false := rfl
theorem missing_resource_refused : instrumentEnabled start (.emit 0 100) = false := by decide
theorem refusal_keeps_actual_cursor : (performInstrumentRequest start (.receive 0)).cursor = start := rfl
theorem refusal_has_no_production :
    StrongPerimetralTurning.History.length (performInstrumentRequest start (.receive 0)).history = 0 := rfl

theorem admitted_emission_uses_comparison :
    (performInstrumentRequest start (.emit 0 6)).event =
      .emitted (SignalRecord.emit compared.head.determination.1 input.payload) := rfl

theorem successor_contains_the_same_emission :
    (performInstrumentRequest start (.emit 0 6)).cursor.read
      (Ref.here : Ref (performInstrumentRequest start (.emit 0 6)).cursor.kinds .signal) =
      SignalRecord.emit compared.head.determination.1 input.payload := rfl

def interleaved : List LocalRequest :=
  [.receive 0, .inspect .reading 0, .emit 0 6, .inspect .signal 0,
    .relay 0 8, .receive 0, .inspect .reading 0, .receive 100]

def session := runInstrumentRequests start interleaved

theorem finite_interleavings_exact (source : InstrumentCursor) (requests : List LocalRequest) :
    (runInstrumentRequests source requests).report = instrumentContract.outcome source requests :=
  instrument_all_futures_exact source requests

theorem every_final_cursor_exact (source : InstrumentCursor) (requests : List LocalRequest) :
    (runInstrumentRequests source requests).cursor =
      ConstitutiveSearch.Grouping.Continuation.run instrumentContract.next source requests :=
  instrument_final_cursor_exact source requests

theorem interleaving_contains_three_shared_productions :
    StrongPerimetralTurning.History.length session.history = 3 := by decide

theorem source_reception_survives (requests : List LocalRequest) :
    (runComparedRequests arrivals.2 requests).continuation.cursor.read
      ((runComparedRequests arrivals.2 requests).transport.references arrivals.2.first) =
      arrivals.1.read arrivals.2.first :=
  (runComparedRequests arrivals.2 requests).transport.reads arrivals.2.first

theorem source_occurrences_stay_distinct (requests : List LocalRequest) :
    (runComparedRequests arrivals.2 requests).transport.references arrivals.2.first ≠
      (runComparedRequests arrivals.2 requests).transport.references arrivals.2.second :=
  compared_requests_keep_sources arrivals.2 requests

def first_used_edge_kept := session.transportUsed (comparison_first_used arrivals.2)
def second_used_edge_kept := session.transportUsed (comparison_second_used arrivals.2)
def prior_reception_edge_kept := session.transportUsed (comparison_first_reception_kept arrivals.2)

theorem head_never_reads_request_tail (one two : List LocalRequest) :
    (runComparedRequests arrivals.2 one).head = (runComparedRequests arrivals.2 two).head :=
  compared_requests_head_independent arrivals.2 one two

def resumed := session.continue [.inspect .reading 0, .emit 0 9, .receive 0]

theorem resumed_uses_actual_cursor : resumed.report =
    instrumentContract.outcome session.cursor [.inspect .reading 0, .emit 0 9, .receive 0] :=
  instrument_continuation_exact session _

theorem composed_history_uses_cached_prefix : session.continuedHistory resumed =
    StrongPerimetralTurning.History.append session.history resumed.history := rfl

theorem composed_history_has_five_productions :
    StrongPerimetralTurning.History.length (session.continuedHistory resumed) = 5 := by decide

theorem repeated_inspections_have_no_production (source : InstrumentCursor) {kind}
    (ref : Ref source.kinds kind) (count : Nat) :
    StrongPerimetralTurning.History.length
      (runInstrumentRequests source (List.replicate count (.inspect kind ref.position))).history = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ]
    dsimp only [runInstrumentRequests]
    rw [instrument_inspection_response source ref]
    exact (StrongPerimetralTurning.History.length_append .root _).trans ((Nat.zero_add _).trans ih)

theorem repeat_read_all_futures (count : Nat) :
    (runInstrumentRequests start (List.replicate count (.inspect .reading 0))).report =
      instrumentContract.outcome start (List.replicate count (.inspect .reading 0)) :=
  instrument_all_futures_exact ..

def relayed := runInstrumentRequests start [.emit 0 6, .relay 0 8, .relay 0 9]
def reemitted := relayed.continue [.receive 0, .emit 0 10]

theorem same_signal_reading_different_path :
    (relayed.cursor.read (Ref.here : Ref relayed.cursor.kinds .signal)).reading =
      (reemitted.cursor.read (Ref.here : Ref reemitted.cursor.kinds .signal)).reading := by decide

def recordLength : LocalReadout → Option Nat
  | .signal record => some record.increments.length
  | .reading _ => none
  | .payload _ => none
  | .calibration _ => none

theorem path_effect_is_still_future_distinguishable :
    ¬ FutureEquivalent instrumentContract relayed.cursor reemitted.cursor := by
  intro same
  have records := instrument_futures_preserve_readout relayed.cursor reemitted.cursor
    (Ref.here : Ref relayed.cursor.kinds .signal) (Ref.here : Ref reemitted.cursor.kinds .signal) rfl same
  have separated := congrArg recordLength records
  change (some 2 : Option Nat) = some 0 at separated
  cases separated

-- Smoke evaluations of the real shared runner, not timing evidence.
#eval (instrumentEnabled start (.inspect .reading 0), instrumentEnabled start (.receive 0))
#eval (StrongPerimetralTurning.History.length session.history,
  StrongPerimetralTurning.History.length (session.continuedHistory resumed))
#eval (recordLength ((match performInstrumentRequest relayed.cursor (.inspect .signal 0) with
  | response => match response.event with | .inspected value => value | _ => .payload 0)),
  recordLength ((match performInstrumentRequest reemitted.cursor (.inspect .signal 0) with
  | response => match response.event with | .inspected value => value | _ => .payload 0)))

end Tests.Relativity.InstrumentFutureChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.InstrumentFutureChecks.arrivals
#print axioms Tests.Relativity.InstrumentFutureChecks.comparison_zero_sources_distinct
#print axioms Tests.Relativity.InstrumentFutureChecks.actual_comparison_read_enabled
#print axioms Tests.Relativity.InstrumentFutureChecks.actual_comparison_read_exact
#print axioms Tests.Relativity.InstrumentFutureChecks.wrong_kind_refused
#print axioms Tests.Relativity.InstrumentFutureChecks.missing_resource_refused
#print axioms Tests.Relativity.InstrumentFutureChecks.refusal_keeps_actual_cursor
#print axioms Tests.Relativity.InstrumentFutureChecks.refusal_has_no_production
#print axioms Tests.Relativity.InstrumentFutureChecks.admitted_emission_uses_comparison
#print axioms Tests.Relativity.InstrumentFutureChecks.successor_contains_the_same_emission
#print axioms Tests.Relativity.InstrumentFutureChecks.finite_interleavings_exact
#print axioms Tests.Relativity.InstrumentFutureChecks.every_final_cursor_exact
#print axioms Tests.Relativity.InstrumentFutureChecks.interleaving_contains_three_shared_productions
#print axioms Tests.Relativity.InstrumentFutureChecks.source_reception_survives
#print axioms Tests.Relativity.InstrumentFutureChecks.source_occurrences_stay_distinct
#print axioms Tests.Relativity.InstrumentFutureChecks.first_used_edge_kept
#print axioms Tests.Relativity.InstrumentFutureChecks.second_used_edge_kept
#print axioms Tests.Relativity.InstrumentFutureChecks.prior_reception_edge_kept
#print axioms Tests.Relativity.InstrumentFutureChecks.head_never_reads_request_tail
#print axioms Tests.Relativity.InstrumentFutureChecks.resumed_uses_actual_cursor
#print axioms Tests.Relativity.InstrumentFutureChecks.composed_history_uses_cached_prefix
#print axioms Tests.Relativity.InstrumentFutureChecks.composed_history_has_five_productions
#print axioms Tests.Relativity.InstrumentFutureChecks.repeated_inspections_have_no_production
#print axioms Tests.Relativity.InstrumentFutureChecks.repeat_read_all_futures
#print axioms Tests.Relativity.InstrumentFutureChecks.same_signal_reading_different_path
#print axioms Tests.Relativity.InstrumentFutureChecks.recordLength
#print axioms Tests.Relativity.InstrumentFutureChecks.path_effect_is_still_future_distinguishable
/- AXIOM_AUDIT_END -/
