import RelationalPerimeter

/-! Public closed descriptions, common refinements and a full-contract path
separator. Reader selection is not a physical measurement or memory quotient. -/
set_option genInjectivity false
namespace Tests.Relativity.ConstitutedDescriptionChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source := emittedCursor input
def first : Instruction source.kinds .signal := .relay .here (.prior (.prior (.prior .here)))
def second : Instruction (.signal :: source.kinds) .reading := .receive (.prior .here)
def actual := produceStoredPair source first second
theorem exchange_found : exchangeFound actual = true := rfl
def found := discoveredExchangeOfFound actual exchange_found
def origin : RecurringCursor := .fromCursor actual.cursor
def anchor : Ref origin.kinds .signal := .prior .here
def originalSignal : Ref origin.kinds .signal := .prior (.prior .here)
def initial : DescriptionPath origin origin := .root
def exchanged := initial.reexpressed found.raccord

def simpleReaders : SignalReaders := ⟨true, true, false⟩
def pathReaders : SignalReaders := ⟨false, false, true⟩

theorem complement_is_full : simpleReaders.join pathReaders = SignalReaders.full := rfl
theorem descriptions_are_not_occurrence_identification :
    exchanged.reference anchor ≠ exchanged.reference originalSignal := by
  intro same
  have original := exchanged.injective _ _ same
  have positions := congrArg Ref.position original
  change 1 = 2 at positions
  exact Nat.noConfusion (Nat.succ.inj positions)

theorem actual_transport_not_value_matching :
    (exchanged.reference anchor).position = 0 ∧ (exchanged.reference originalSignal).position = 2 := ⟨rfl, rfl⟩

theorem reverse_returns_the_source_occurrence :
    (exchanged.reexpressed found.raccord.reverse).reference anchor = anchor :=
  description_round_trip_reference initial found.raccord anchor

theorem full_view_comes_from_the_cached_relay :
    describeSignal exchanged anchor .full = observeSignal .full actual.firstDetermination.1 :=
  described_signal_exact exchanged anchor .full

theorem common_refinement_has_both_restrictions :
    (describeSignal exchanged anchor (simpleReaders.join pathReaders)).restrict simpleReaders =
      describeSignal exchanged anchor simpleReaders ∧
    (describeSignal exchanged anchor (simpleReaders.join pathReaders)).restrict pathReaders =
      describeSignal exchanged anchor pathReaders :=
  described_signal_common_refinement exchanged anchor simpleReaders pathReaders

theorem refinement_is_not_an_event : exchanged.producedCount = initial.producedCount := rfl

def requests : List RecurringRequest := [.local (.receive 1), .compare 1 0, .local (.receive 100)]
def continued := found.continue requests
def describedContinuation := continuedExchangeDescription found continued

theorem physical_continuation_incorporated : describedContinuation.producedCount = 2 := rfl

theorem continuation_description_uses_actual_history :
    describedContinuation.reference anchor = continued.raccord.constitution.references.forward
      ((recurringHistoryTransport continued.first.history).references anchor) :=
  DescriptionPath.prolong_reference initial continued.first.history anchor |>
    congrArg continued.raccord.constitution.references.forward

theorem continuation_full_record_exact :
    describeSignal describedContinuation anchor .full = observeSignal .full actual.firstDetermination.1 :=
  continued_exchange_description_exact found continued anchor .full

theorem refine_then_prolong_or_prolong_then_refine :
    (describeSignal describedContinuation anchor .full).restrict simpleReaders =
      describeSignal initial anchor simpleReaders :=
  (described_signal_restriction describedContinuation anchor
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩).trans
      (described_signal_exact describedContinuation anchor simpleReaders)

def arrival : RecurringArrival origin.formation .here (.prior (.prior .here)) :=
  .fromCursor (Arrived.ofReception (source.extend actual.firstDetermination).formation actual.secondDetermination.2)
def transportedArrival := describedContinuation.arrival arrival
def edge : RecurringUsed origin.formation ⟨.signal, .prior (.prior .here)⟩ ⟨.reading, .here⟩ :=
  .fromCursor (.produced (source.extend actual.firstDetermination).formation actual.secondDetermination.2
    (.prior .here) (.receptionSignal _))
def transportedEdge := describedContinuation.used edge

theorem every_finite_continuation_retains_attached_record (future : List RecurringRequest) :
    describeSignal (continuedExchangeDescription found (found.continue future)) anchor .full =
      describeSignal initial anchor .full := continued_exchange_description_exact found _ anchor .full

theorem every_finite_continuation_preserves_contract (future : List RecurringRequest) :
    recurringContract.outcome (.fromCursor found.exchanged.cursor) (found.continue future).translated =
      recurringContract.outcome origin future := discovered_exchange_all_futures found future

def doubleCalibration : Calibration where
  increment := Rational.ofNat 2
  nonnegative := Rational.nat_nonnegative 2
  nonzero := by decide

def doubleInput : Received := ⟨Rational.zero, 7, doubleCalibration⟩
def twoRelays : RecurringCursor := .fromCursor (relayExecution input 2).cursor
def oneRelay : RecurringCursor := .fromCursor (relayExecution doubleInput 1).cursor
def twoAnchor : Ref twoRelays.kinds .signal := .here
def oneAnchor : Ref oneRelay.kinds .signal := .here

theorem same_partial_readers :
    describeSignal (DescriptionPath.root (origin := twoRelays)) twoAnchor simpleReaders =
      describeSignal (DescriptionPath.root (origin := oneRelay)) oneAnchor simpleReaders := rfl

theorem path_records_differ : (twoRelays.read twoAnchor).increments ≠ (oneRelay.read oneAnchor).increments := by
  intro same
  have lengths := congrArg List.length same
  change 2 = 1 at lengths
  exact Nat.noConfusion (Nat.succ.inj lengths)

theorem full_readers_do_not_agree :
    describeSignal (DescriptionPath.root (origin := twoRelays)) twoAnchor .full ≠
      describeSignal (DescriptionPath.root (origin := oneRelay)) oneAnchor .full := by
  intro same
  have records := (joint_signal_readers_exact _ _).mp same
  exact path_records_differ (congrArg SignalRecord.increments records)

theorem partial_agreement_does_not_authorize_forgetting :
    ¬ FutureEquivalent recurringContract twoRelays oneRelay :=
  differing_paths_separate_futures twoRelays oneRelay twoAnchor oneAnchor rfl path_records_differ

def separatingFuture : List RecurringRequest := [.local (.inspect .signal 0)]

theorem actual_future_reports_differ :
    (runRecurringRequests twoRelays separatingFuture).report ≠
      (runRecurringRequests oneRelay separatingFuture).report := by
  rw [recurring_all_futures_exact, recurring_all_futures_exact]
  exact differing_paths_separate_inspection twoRelays oneRelay twoAnchor oneAnchor rfl path_records_differ

end Tests.Relativity.ConstitutedDescriptionChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.actual
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.found
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.descriptions_are_not_occurrence_identification
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.actual_transport_not_value_matching
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.reverse_returns_the_source_occurrence
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.full_view_comes_from_the_cached_relay
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.common_refinement_has_both_restrictions
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.refinement_is_not_an_event
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.describedContinuation
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.physical_continuation_incorporated
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.continuation_description_uses_actual_history
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.continuation_full_record_exact
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.refine_then_prolong_or_prolong_then_refine
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.transportedArrival
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.transportedEdge
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.every_finite_continuation_retains_attached_record
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.every_finite_continuation_preserves_contract
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.doubleCalibration
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.same_partial_readers
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.path_records_differ
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.full_readers_do_not_agree
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.partial_agreement_does_not_authorize_forgetting
#print axioms Tests.Relativity.ConstitutedDescriptionChecks.actual_future_reports_differ
/- AXIOM_AUDIT_END -/
