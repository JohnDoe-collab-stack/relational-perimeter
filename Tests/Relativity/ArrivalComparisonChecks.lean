import RelationalPerimeter

/-! Public clients of the declared arrival comparison. The instance below
uses two separate emissions, genuine receptions, and finitely many but
arbitrarily many relays. Evaluations are executable smoke checks only. -/
set_option genInjectivity false
namespace Tests.Relativity.ArrivalComparisonChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure ReceptionResult (source : Cursor) where
  cursor : Cursor
  history : LocalHistory source cursor
  reading : Ref cursor.kinds .reading
  signal : Ref cursor.kinds .signal
  arrived : Arrived cursor.formation reading signal
  fresh : ∀ old : Ref source.kinds .reading, (historyTransport history).references old ≠ reading

def receiveAfterRelays (count : Nat) (source : Cursor) (signal : Ref source.kinds .signal)
    (calibration : Ref source.kinds .calibration) : ReceptionResult source :=
  match count with
  | 0 =>
    let head := perform source (.receive signal)
    ⟨head.successor, productionHistory head, .here, .prior signal, arrivalOfProduction head,
      fun old same => fresh_distinct source head.determination old same.symm⟩
  | count + 1 =>
    let head := perform source (.relay signal calibration)
    let suffix := receiveAfterRelays count head.successor .here (.prior calibration)
    ⟨suffix.cursor, StrongPerimetralTurning.History.append (productionHistory head) suffix.history,
      suffix.reading, suffix.signal, suffix.arrived, fun old same =>
        suffix.fresh (.prior old)
          ((historyTransport_append_reference (productionHistory head) suffix.history old).symm.trans same)⟩
termination_by structural count

theorem receiveAfterRelays_length (count : Nat) (source : Cursor)
    (signal : Ref source.kinds .signal) (calibration : Ref source.kinds .calibration) :
    StrongPerimetralTurning.History.length (receiveAfterRelays count source signal calibration).history = count + 1 := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih =>
    change StrongPerimetralTurning.History.length (StrongPerimetralTurning.History.append _ _) = _
    exact (StrongPerimetralTurning.History.length_append _ _).trans
      ((congrArg (fun n => 1 + n) (ih _ _ _)).trans (Nat.add_comm 1 (count + 1)))

/-- No arrival is supplied by the family. Four shared heads emit, receive,
emit, then relay/receive. The first arrival is transported through the actual
second chain. A fresh received reading cannot coincide with this old port. -/
def pairedArrivals (input : Received) (count : Nat) : (source : Cursor) ×' ArrivalPair source :=
  let emitted := perform (Cursor.received input) emission
  let first := perform emitted.successor (.receive .here)
  let second := perform first.successor (.emit (.prior (.prior .here)) (.prior (.prior (.prior .here))))
  let firstArrival := Arrived.inherited second.determination.2 (arrivalOfProduction first)
  let received := receiveAfterRelays count second.successor .here
    (.prior (.prior (.prior (.prior (.prior .here)))))
  let firstRef := (historyTransport received.history).references (.prior .here)
  let firstSignal := (historyTransport received.history).references (.prior (.prior .here))
  ⟨received.cursor, ⟨firstRef, received.reading, firstSignal, received.signal,
    historyTransportArrival received.history firstArrival, received.arrived, received.fresh (.prior .here)⟩⟩

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def zeroPair := pairedArrivals input 0
def onePair := pairedArrivals input 1
def zeroComparison := performComparison zeroPair.2
def oneComparison := performComparison onePair.2

theorem initial_reading_refused (address : Nat) : arrivalEnabled (.received input) address = false :=
  received_root_refuses_arrivals input address

theorem initial_comparison_refused (one two : Nat) : comparisonEnabled (.received input) one two = false :=
  comparison_refuses_given_root input one two

theorem both_arrivals_admitted : comparisonEnabled zeroPair.1 2 0 = true := rfl
theorem same_arrival_rejected : comparisonEnabled zeroPair.1 0 0 = false := same_arrival_refused _ _

theorem given_reading_still_refused_after_receptions : comparisonEnabled zeroPair.1 4 0 = false := rfl

theorem matching_value_does_not_authorize_given_port :
    zeroPair.1.read (Ref.prior (Ref.prior (Ref.prior (Ref.prior Ref.here)))) =
      zeroPair.1.read zeroPair.2.second ∧ comparisonEnabled zeroPair.1 4 0 = false :=
  ⟨rfl, given_reading_still_refused_after_receptions⟩

theorem zero_arrivals_have_equal_readings : zeroPair.1.read zeroPair.2.first = zeroPair.1.read zeroPair.2.second := rfl

theorem equal_arrivals_remain_distinct :
    zeroComparison.determination.1 = Rational.zero ∧ zeroPair.2.first ≠ zeroPair.2.second :=
  comparison_equal_readings_not_equal_sources zeroPair.2 zero_arrivals_have_equal_readings

theorem one_relay_changes_comparison : oneComparison.determination.1 = Rational.one := rfl

theorem interaction_responds_to_received_path :
    zeroComparison.determination.1 ≠ oneComparison.determination.1 := by
  intro same
  exact Rational.one_ne_zero same.symm

def first_arrival_dependency := comparison_first_reception_kept onePair.2
def first_comparison_dependency := comparison_first_used onePair.2
def second_comparison_dependency := comparison_second_used onePair.2

def continued :=
  emitComparison oneComparison (.prior (.prior (.prior (.prior (.prior (.prior .here))))))

theorem continuation_consumes_shared_reading : continued.determination.1.reading = oneComparison.determination.1 :=
  emitted_comparison_reading ..

theorem continuation_consumes_same_payload : continued.determination.1.payload = input.payload := rfl

def comparisonConsumer {source : Cursor} (_pair : ArrivalPair source)
    (payload : Ref source.kinds .payload) : Program (.reading :: source.kinds) :=
  .step (.emit .here (.prior payload)) (.step (.receive .here) .done)

def session := runCompared onePair.2
  (comparisonConsumer onePair.2 (.prior (.prior (.prior (.prior (.prior (.prior .here)))))))

theorem consumed_then_received : session.continuation.cursor.read (Ref.here : Ref session.continuation.cursor.kinds .reading) =
    oneComparison.determination.1 := rfl

theorem old_arrival_reads_preserved {source : Cursor} (pair : ArrivalPair source)
    (schedule : Program (.reading :: source.kinds)) :
    (runCompared pair schedule).continuation.cursor.read
      ((runCompared pair schedule).transport.references pair.first) = source.read pair.first :=
  (runCompared pair schedule).transport.reads pair.first

theorem old_arrival_distinction_preserved {source : Cursor} (pair : ArrivalPair source)
    (schedule : Program (.reading :: source.kinds)) :
    (runCompared pair schedule).transport.references pair.first ≠
      (runCompared pair schedule).transport.references pair.second :=
  fun same => pair.distinct ((runCompared pair schedule).transport.injective _ _ same)

theorem comparison_not_determined_by_future {source : Cursor} (pair : ArrivalPair source)
    (one two : Program (.reading :: source.kinds)) :
    (runCompared pair one).head = (runCompared pair two).head := compared_head_independent pair one two

theorem arbitrary_finite_continuation {source : Cursor} (pair : ArrivalPair source)
    (schedule : Program (.reading :: source.kinds)) :
    StrongPerimetralTurning.History.length (runCompared pair schedule).continuation.history = schedule.steps :=
  runInstrument_length (performComparison pair).successor schedule

def dependencies_survive_continuation := instrumentHistoryTransportUsed session.continuation.history
  (comparison_first_used onePair.2)

def second_emission_origin := onePair.2.secondArrival.journey.originEvent
def first_emission_origin := onePair.2.firstArrival.journey.originEvent

theorem different_origins_kept :
    onePair.2.firstArrival.journey.origin ≠ onePair.2.secondArrival.journey.origin := by
  intro same
  have impossible := congrArg Ref.position same
  change (4 : Nat) = 2 at impossible
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj impossible))

#eval (comparisonEnabled zeroPair.1 2 0, comparisonEnabled zeroPair.1 0 0)
#eval (zeroComparison.determination.1.index, oneComparison.determination.1.index)
#eval (session.continuation.cursor.kinds.length, continued.determination.1.payload)

end Tests.Relativity.ArrivalComparisonChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ArrivalComparisonChecks.receiveAfterRelays
#print axioms Tests.Relativity.ArrivalComparisonChecks.receiveAfterRelays_length
#print axioms Tests.Relativity.ArrivalComparisonChecks.pairedArrivals
#print axioms Tests.Relativity.ArrivalComparisonChecks.initial_reading_refused
#print axioms Tests.Relativity.ArrivalComparisonChecks.initial_comparison_refused
#print axioms Tests.Relativity.ArrivalComparisonChecks.both_arrivals_admitted
#print axioms Tests.Relativity.ArrivalComparisonChecks.same_arrival_rejected
#print axioms Tests.Relativity.ArrivalComparisonChecks.given_reading_still_refused_after_receptions
#print axioms Tests.Relativity.ArrivalComparisonChecks.matching_value_does_not_authorize_given_port
#print axioms Tests.Relativity.ArrivalComparisonChecks.equal_arrivals_remain_distinct
#print axioms Tests.Relativity.ArrivalComparisonChecks.one_relay_changes_comparison
#print axioms Tests.Relativity.ArrivalComparisonChecks.interaction_responds_to_received_path
#print axioms Tests.Relativity.ArrivalComparisonChecks.first_arrival_dependency
#print axioms Tests.Relativity.ArrivalComparisonChecks.first_comparison_dependency
#print axioms Tests.Relativity.ArrivalComparisonChecks.second_comparison_dependency
#print axioms Tests.Relativity.ArrivalComparisonChecks.continuation_consumes_shared_reading
#print axioms Tests.Relativity.ArrivalComparisonChecks.continuation_consumes_same_payload
#print axioms Tests.Relativity.ArrivalComparisonChecks.consumed_then_received
#print axioms Tests.Relativity.ArrivalComparisonChecks.old_arrival_reads_preserved
#print axioms Tests.Relativity.ArrivalComparisonChecks.old_arrival_distinction_preserved
#print axioms Tests.Relativity.ArrivalComparisonChecks.comparison_not_determined_by_future
#print axioms Tests.Relativity.ArrivalComparisonChecks.arbitrary_finite_continuation
#print axioms Tests.Relativity.ArrivalComparisonChecks.dependencies_survive_continuation
#print axioms Tests.Relativity.ArrivalComparisonChecks.second_emission_origin
#print axioms Tests.Relativity.ArrivalComparisonChecks.first_emission_origin
#print axioms Tests.Relativity.ArrivalComparisonChecks.different_origins_kept
/- AXIOM_AUDIT_END -/
