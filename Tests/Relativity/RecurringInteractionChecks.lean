import RelationalPerimeter

/-! Closed public client: the first comparison is actually executed, then
its output is emitted and received before it can enter a later comparison.
All evaluations below are smoke checks, not physical timing experiments. -/
set_option genInjectivity false
namespace Tests.Relativity.RecurringInteractionChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def arrivals : (source : Cursor) ×' ArrivalPair source :=
  let emissionOne := perform (.received input) emission
  let receptionOne := perform emissionOne.successor (.receive .here)
  let emissionTwo := perform receptionOne.successor
    (.emit (.prior (.prior .here)) (.prior (.prior (.prior .here))))
  let receptionTwo := perform emissionTwo.successor (.receive .here)
  let firstArrival := Arrived.inherited receptionTwo.determination.2
    (Arrived.inherited emissionTwo.determination.2 (arrivalOfProduction receptionOne))
  ⟨receptionTwo.successor, ⟨.prior (.prior .here), .here, .prior (.prior (.prior .here)), .prior .here,
    firstArrival, arrivalOfProduction receptionTwo, fun same =>
      fresh_distinct emissionTwo.successor receptionTwo.determination (.prior .here) same.symm⟩⟩

def firstComparison := performComparison arrivals.2
def start := RecurringCursor.fromInstrument firstComparison.successor

theorem first_output_zero : firstComparison.determination.1 = Rational.zero :=
  (comparison_equal_readings_not_equal_sources arrivals.2 rfl).1

def startingPair : RecurringPair start :=
  ⟨.prior arrivals.2.first, .prior arrivals.2.second, .prior arrivals.2.firstSignal, .prior arrivals.2.secondSignal,
    .fromInstrument (.priorComparison firstComparison.determination.2 arrivals.2.firstArrival),
    .fromInstrument (.priorComparison firstComparison.determination.2 arrivals.2.secondArrival),
    fun same => arrivals.2.distinct (prior_injective _ _ same)⟩

theorem embedding_keeps_the_actual_support : start.support = firstComparison.successor.support := rfl

theorem initial_reading_cannot_supply_an_arrival (pair : RecurringPair (.fromCursor (.received input))) : False :=
  recurring_given_not_reception input pair.firstArrival

theorem computed_reading_is_not_a_received_port : recurringEnabled start (.compare 0 1) = false := rfl

theorem same_occurrence_is_refused : recurringEnabled start (.compare 1 1) = false :=
  recurring_same_arrival_refused start 1

theorem actual_distinct_arrivals_are_enabled :
    recurringEnabled start (.compare startingPair.first.position startingPair.second.position) = true :=
  recurring_pair_request_enabled startingPair

theorem equal_readings_keep_the_sources_distinct :
    (performRecurringRequest start (.compare 3 1)).event = .compared Rational.zero ∧
      startingPair.first ≠ startingPair.second :=
  ⟨recurring_pair_response_output startingPair, startingPair.distinct⟩

def newReceptions : List RecurringRequest :=
  [.local (.emit 0 6), .local (.receive 0), .local (.relay 1 9), .local (.receive 0)]

def newArrivals : (source : RecurringCursor) ×' RecurringPair source :=
  let emitted := performRecurring start (.signal (.emit .here (.prior (.prior (.prior (.prior (.prior (.prior .here))))))))
  let received := performRecurring emitted.successor (.signal (.receive .here))
  let relayed := performRecurring received.successor
    (.signal (.relay (.prior .here) (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior .here)))))))))))
  let receivedAgain := performRecurring relayed.successor (.signal (.receive .here))
  let subsequentHistory := StrongPerimetralTurning.History.append
    (recurringProductionHistory relayed) (recurringProductionHistory receivedAgain)
  let earlier := recurringHistoryArrival subsequentHistory (recurringArrivalOfProduction received)
  ⟨receivedAgain.successor, ⟨.prior (.prior .here), .here, .prior (.prior (.prior .here)), .prior .here,
    earlier, recurringArrivalOfProduction receivedAgain, fun same =>
      fresh_position_distinct (Ref.prior (Ref.here : Ref received.successor.kinds .reading))
        (congrArg Ref.position same.symm)⟩⟩

def secondComparison := performRecurring newArrivals.1 (.compare newArrivals.2)

theorem second_comparison_uses_new_receptions :
    recurringEnabled newArrivals.1 (.compare 2 0) = true := recurring_pair_request_enabled newArrivals.2

theorem second_comparison_changes_the_actual_reading : secondComparison.determination.1 = Rational.one := by
  change Rational.sub (Rational.add firstComparison.determination.1 Rational.one) firstComparison.determination.1 = _
  rw [first_output_zero, Rational.zero_add, Rational.sub_zero]

theorem second_result_is_shared_with_successor :
    secondComparison.successor.read (Ref.here : Ref secondComparison.successor.kinds .reading) = Rational.one :=
  second_comparison_changes_the_actual_reading

def interleaved : List RecurringRequest :=
  [.compare 0 1, .local (.inspect .reading 0), .local (.emit 0 6), .local (.receive 0),
    .local (.relay 1 9), .local (.receive 0), .compare 2 0, .local (.inspect .reading 0),
    .local (.emit 0 11), .local (.receive 0), .compare 3 0, .local (.inspect .reading 0)]

def session := runRecurringRequests start interleaved

theorem interleavings_contain_eight_shared_productions :
    StrongPerimetralTurning.History.length session.history = 8 := by decide

def thirdArrivals : (source : RecurringCursor) ×' RecurringPair source :=
  let emitted := performRecurring secondComparison.successor
    (.signal (.emit .here (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior .here)))))))))))))
  let received := performRecurring emitted.successor (.signal (.receive .here))
  let history := StrongPerimetralTurning.History.append (recurringProductionHistory secondComparison)
    (StrongPerimetralTurning.History.append (recurringProductionHistory emitted) (recurringProductionHistory received))
  let earlier := recurringHistoryArrival history newArrivals.2.secondArrival
  ⟨received.successor, ⟨.prior (.prior (.prior newArrivals.2.second)), .here,
    .prior (.prior (.prior newArrivals.2.secondSignal)), .prior .here,
    earlier, recurringArrivalOfProduction received, fun same =>
      fresh_position_distinct (.prior (.prior newArrivals.2.second)) (congrArg Ref.position same.symm)⟩⟩

def thirdComparison := performRecurring thirdArrivals.1 (.compare thirdArrivals.2)

theorem third_result_is_received_then_compared : thirdComparison.determination.1 = Rational.zero := by
  have firstMeasure : thirdArrivals.2.firstArrival.measure = newArrivals.2.secondArrival.measure :=
    recurring_history_arrival_measure _ newArrivals.2.secondArrival
  have secondMeasure : thirdArrivals.2.secondArrival.measure = secondComparison.determination.1 := rfl
  have earlierOne : newArrivals.2.secondArrival.measure = Rational.one := by
    change Rational.add firstComparison.determination.1 Rational.one = _
    rw [first_output_zero, Rational.zero_add]
  change Rational.sub thirdArrivals.2.secondArrival.measure thirdArrivals.2.firstArrival.measure = _
  rw [secondMeasure, firstMeasure, second_comparison_changes_the_actual_reading, earlierOne, Rational.sub_self]

theorem every_finite_interleaving_matches (source : RecurringCursor) (requests : List RecurringRequest) :
    (runRecurringRequests source requests).report = recurringContract.outcome source requests :=
  recurring_all_futures_exact source requests

theorem every_final_cursor_matches (source : RecurringCursor) (requests : List RecurringRequest) :
    (runRecurringRequests source requests).cursor =
      ConstitutiveSearch.Grouping.Continuation.run recurringContract.next source requests :=
  recurring_final_cursor_exact source requests

theorem arbitrary_repetition_is_not_a_fixed_bound (count : Nat) :
    StrongPerimetralTurning.History.length (repeatRecurringPair startingPair count).history = count :=
  recurring_repetition_length startingPair count

theorem arbitrary_repetition_is_the_same_contract (count : Nat) :
    (repeatRecurringPair startingPair count).report =
      recurringContract.outcome start (repeatRecurringPair startingPair count).requests :=
  recurring_repetition_all_futures startingPair count

theorem arbitrary_repetition_keeps_distinct_sources (count : Nat) :
    (recurringHistoryTransport (repeatRecurringPair startingPair count).history).references startingPair.first ≠
      (recurringHistoryTransport (repeatRecurringPair startingPair count).history).references startingPair.second :=
  recurring_repetition_preserves_sources startingPair count

theorem arbitrary_requests_preserve_received_value (requests : List RecurringRequest) :
    (runRecurringRequests start requests).cursor.read
      ((recurringHistoryTransport (runRecurringRequests start requests).history).references startingPair.first) =
      start.read startingPair.first := recurring_requests_preserve_reads start requests startingPair.first

def sourceReceptionStillArrived := recurringHistoryArrival session.history startingPair.firstArrival
def secondReceptionStillArrived := recurringHistoryArrival session.history startingPair.secondArrival
def comparisonDependencyStillUsed := session.transportUsed
  (RecurringUsed.fromInstrument (comparison_first_used arrivals.2))

def resumed := session.continue [.local (.emit 0 14), .local (.receive 0), .compare 0 3]

theorem continuation_uses_produced_cursor : resumed.report =
    recurringContract.outcome session.cursor [.local (.emit 0 14), .local (.receive 0), .compare 0 3] :=
  recurring_continuation_exact session _

theorem composed_history_keeps_the_prefix : session.continuedHistory resumed =
    StrongPerimetralTurning.History.append session.history resumed.history := rfl

theorem repeated_reads_do_not_reexecute (source : RecurringCursor) {kind}
    (ref : Ref source.kinds kind) (count : Nat) :
    StrongPerimetralTurning.History.length
      (runRecurringRequests source (List.replicate count (.local (.inspect kind ref.position)))).history = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ]
    dsimp only [runRecurringRequests]
    rw [recurring_inspection_response source ref]
    exact (StrongPerimetralTurning.History.length_append .root _).trans ((Nat.zero_add _).trans ih)

def relayed := runRecurringRequests start [.local (.emit 0 6), .local (.relay 0 8), .local (.relay 0 9)]
def reemitted := relayed.continue [.local (.receive 0), .local (.emit 0 10)]

theorem same_present_reading_different_path :
    (relayed.cursor.read (Ref.here : Ref relayed.cursor.kinds .signal)).reading =
      (reemitted.cursor.read (Ref.here : Ref reemitted.cursor.kinds .signal)).reading := by decide

def recordLength : LocalReadout → Option Nat
  | .signal record => some record.increments.length
  | .reading _ => none
  | .payload _ => none
  | .calibration _ => none

theorem path_effect_remains_future_distinguishable :
    ¬ FutureEquivalent recurringContract relayed.cursor reemitted.cursor := by
  intro same
  have records := recurring_futures_preserve_readout relayed.cursor reemitted.cursor
    (Ref.here : Ref relayed.cursor.kinds .signal) (Ref.here : Ref reemitted.cursor.kinds .signal) rfl same
  have separated := congrArg recordLength records
  change (some 2 : Option Nat) = some 0 at separated
  cases separated

-- Smoke evaluations of compiled definitions; no timing or physical claim.
#eval (recurringEnabled start (.compare 0 1), recurringEnabled start (.compare 3 1))
#eval (StrongPerimetralTurning.History.length session.history,
  StrongPerimetralTurning.History.length (repeatRecurringPair startingPair 40).history)
#eval (secondComparison.determination.1.index, thirdComparison.determination.1.index)

end Tests.Relativity.RecurringInteractionChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.RecurringInteractionChecks.arrivals
#print axioms Tests.Relativity.RecurringInteractionChecks.startingPair
#print axioms Tests.Relativity.RecurringInteractionChecks.first_output_zero
#print axioms Tests.Relativity.RecurringInteractionChecks.newArrivals
#print axioms Tests.Relativity.RecurringInteractionChecks.thirdArrivals
#print axioms Tests.Relativity.RecurringInteractionChecks.embedding_keeps_the_actual_support
#print axioms Tests.Relativity.RecurringInteractionChecks.initial_reading_cannot_supply_an_arrival
#print axioms Tests.Relativity.RecurringInteractionChecks.computed_reading_is_not_a_received_port
#print axioms Tests.Relativity.RecurringInteractionChecks.same_occurrence_is_refused
#print axioms Tests.Relativity.RecurringInteractionChecks.actual_distinct_arrivals_are_enabled
#print axioms Tests.Relativity.RecurringInteractionChecks.equal_readings_keep_the_sources_distinct
#print axioms Tests.Relativity.RecurringInteractionChecks.second_comparison_uses_new_receptions
#print axioms Tests.Relativity.RecurringInteractionChecks.second_comparison_changes_the_actual_reading
#print axioms Tests.Relativity.RecurringInteractionChecks.second_result_is_shared_with_successor
#print axioms Tests.Relativity.RecurringInteractionChecks.interleavings_contain_eight_shared_productions
#print axioms Tests.Relativity.RecurringInteractionChecks.third_result_is_received_then_compared
#print axioms Tests.Relativity.RecurringInteractionChecks.every_finite_interleaving_matches
#print axioms Tests.Relativity.RecurringInteractionChecks.every_final_cursor_matches
#print axioms Tests.Relativity.RecurringInteractionChecks.arbitrary_repetition_is_not_a_fixed_bound
#print axioms Tests.Relativity.RecurringInteractionChecks.arbitrary_repetition_is_the_same_contract
#print axioms Tests.Relativity.RecurringInteractionChecks.arbitrary_repetition_keeps_distinct_sources
#print axioms Tests.Relativity.RecurringInteractionChecks.arbitrary_requests_preserve_received_value
#print axioms Tests.Relativity.RecurringInteractionChecks.sourceReceptionStillArrived
#print axioms Tests.Relativity.RecurringInteractionChecks.secondReceptionStillArrived
#print axioms Tests.Relativity.RecurringInteractionChecks.comparisonDependencyStillUsed
#print axioms Tests.Relativity.RecurringInteractionChecks.continuation_uses_produced_cursor
#print axioms Tests.Relativity.RecurringInteractionChecks.composed_history_keeps_the_prefix
#print axioms Tests.Relativity.RecurringInteractionChecks.repeated_reads_do_not_reexecute
#print axioms Tests.Relativity.RecurringInteractionChecks.same_present_reading_different_path
#print axioms Tests.Relativity.RecurringInteractionChecks.path_effect_remains_future_distinguishable
/- AXIOM_AUDIT_END -/
