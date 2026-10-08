import RelationalPerimeter

/-! Closed public client with different constituted execution orders.
Evaluations are executability smoke checks, not physical measurements. -/
set_option genInjectivity false
namespace Tests.Relativity.TransportedRecurringChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := emittedCursor input
def first : Instruction source.kinds .signal := .relay .here (.prior (.prior (.prior .here)))
def second : Instruction source.kinds .reading := .receive .here
def original := produceIndependentPair source first second
def reversed := produceIndependentPair source second first
def initial := independentRecurringPair original reversed

theorem same_actual_source_support : (RecurringCursor.fromCursor original.cursor).support = original.cursor.support := rfl

theorem exchanged_positions_are_not_identity : initial.addresses.forward 0 = 1 ∧ initial.addresses.forward 1 = 0 := ⟨rfl, rfl⟩

theorem request_returns (request : RecurringRequest) :
    (request.rename initial.addresses.forward).rename initial.addresses.backward = request :=
  request.rename_returns _ _ initial.addresses.forwardBackward

def originalArrival : RecurringArrival (RecurringCursor.fromCursor original.cursor).formation
    (Ref.here : Ref original.cursor.kinds .reading) (.prior (.prior .here)) :=
  .fromCursor (Arrived.ofReception (source.extend original.firstDetermination).formation original.secondDetermination.2)

def exchangedArrival := initial.constitution.forwardArrival originalArrival
def returnedArrival := initial.constitution.backwardArrival exchangedArrival

theorem no_value_substitution_for_reception :
    recurringEnabled (.fromCursor original.cursor) (.compare 0 3) = false := rfl

theorem same_occurrence_still_refused : recurringEnabled (.fromCursor original.cursor) (.compare 0 0) = false :=
  recurring_same_arrival_refused _ _

theorem all_current_admissions_and_refusals (request : RecurringRequest) :
    recurringEnabled (.fromCursor reversed.cursor) (request.rename initial.addresses.forward) =
      recurringEnabled (.fromCursor original.cursor) request := recurring_transported_admission_exact initial request

def requests : List RecurringRequest :=
  [.local (.inspect .reading 0), .local (.receive 1), .compare 1 0, .compare 0 1, .local (.receive 100)]

def paired := runCorrespondingRecurring initial requests

theorem translated_requests_use_current_ports : paired.translated =
    [.local (.inspect .reading 1), .local (.receive 0), .compare 2 0, .compare 0 1, .local (.receive 100)] := rfl

theorem source_is_the_existing_runner : paired.first = runRecurringRequests (.fromCursor original.cursor) requests :=
  correspondingRecurring_source_exact initial requests

theorem target_is_the_existing_runner : paired.second = runRecurringRequests (.fromCursor reversed.cursor) paired.translated :=
  correspondingRecurring_target_exact initial requests

theorem complete_forward_contract (future : List RecurringRequest) :
    recurringContract.outcome (.fromCursor reversed.cursor) (runCorrespondingRecurring initial future).translated =
      recurringContract.outcome (.fromCursor original.cursor) future := recurring_transported_all_futures initial future

theorem complete_reverse_contract (future : List RecurringRequest) :
    recurringContract.outcome (.fromCursor original.cursor) (runCorrespondingRecurring initial.reverse future).translated =
      recurringContract.outcome (.fromCursor reversed.cursor) future := recurring_transported_all_futures initial.reverse future

def permissions : Outcome RecurringEvent Unit → List Bool
  | .stop _ => []
  | .step _ allowed _ rest => allowed :: permissions rest

def comparisons : Outcome RecurringEvent Unit → List Rational
  | .stop _ => []
  | .step _ _ event rest => match event with
    | .compared value => value :: comparisons rest
    | .local _ => comparisons rest

theorem mixed_permissions : permissions paired.first.report =
    [true, true, true, false, false] := rfl

theorem compared_values_are_actual_outputs : comparisons paired.first.report = [Rational.one] := by decide

theorem two_shared_productions : StrongPerimetralTurning.History.length paired.first.history = 2 := by decide

theorem both_production_counts_agree : StrongPerimetralTurning.History.length paired.second.history =
    StrongPerimetralTurning.History.length paired.first.history := corresponding_recurring_history_lengths initial requests

theorem no_request_dropped : paired.translated.length = requests.length := recurring_translated_length initial requests

theorem final_readings_still_correspond {kind} (ref : Ref paired.first.cursor.kinds kind) :
    paired.second.cursor.read (paired.raccord.constitution.references.forward ref) = paired.first.cursor.read ref :=
  paired.raccord.constitution.reads ref

def sourceArrivalStillPresent := recurringHistoryArrival paired.first.history originalArrival
def targetArrivalStillPresent := paired.raccord.constitution.forwardArrival sourceArrivalStillPresent
def sourceArrivalReturned := paired.raccord.constitution.backwardArrival targetArrivalStillPresent

def initialEdge : RecurringUsed (RecurringCursor.fromCursor original.cursor).formation
    ⟨.signal, .prior (.prior .here)⟩ ⟨.reading, .here⟩ := .fromCursor originalArrival.view.usedEdge

def sourceEdgeStillUsed := recurringHistoryUsed paired.first.history initialEdge
def targetEdgeStillUsed := paired.raccord.constitution.forwardUsed sourceEdgeStillUsed
def sourceEdgeReturned := paired.raccord.constitution.backwardUsed targetEdgeStillUsed

def dynamicRequests : List RecurringRequest := [.local (.receive 1), .compare 1 0]
def dynamicPair := runCorrespondingRecurring initial dynamicRequests

theorem comparison_address_follows_production : dynamicPair.translated = [.local (.receive 0), .compare 2 0] := rfl

theorem frozen_translation_changes_the_contract :
    recurringContract.outcome (.fromCursor reversed.cursor) (dynamicRequests.map (RecurringRequest.rename initial.addresses.forward)) ≠
      recurringContract.outcome (.fromCursor original.cursor) dynamicRequests := by
  intro same
  have tailAllowed := congrArg (fun outcome => match outcome with
    | .stop _ => false
    | .step _ _ _ tail => match tail with
      | .stop _ => false
      | .step _ allowed _ _ => allowed) same
  change false = true at tailAllowed
  cases tailAllowed

theorem changed_address_does_not_identify_occurrences :
    (initial.constitution.references.forward (Ref.here : Ref original.cursor.kinds .reading)) = .prior .here := rfl

def resumed := paired.continue [.local (.inspect .reading 0), .compare 0 1]

theorem resume_from_actual_cursors : resumed.first = runRecurringRequests paired.first.cursor
    [.local (.inspect .reading 0), .compare 0 1] := (recurring_corresponding_continuation_exact paired _).1

def continuedSourceHistory := paired.firstContinuedHistory resumed
def continuedTargetHistory := paired.secondContinuedHistory resumed

theorem histories_consume_the_stored_continuation :
    continuedSourceHistory = StrongPerimetralTurning.History.append paired.first.history resumed.first.history ∧
      continuedTargetHistory = StrongPerimetralTurning.History.append paired.second.history resumed.second.history :=
  recurring_continued_history_uses_cached_suffix paired resumed

#eval permissions paired.first.report
#eval permissions paired.second.report
#eval (comparisons paired.first.report).map Rational.index

/-- A longer executability smoke check. Its evaluation is not a kernel proof
of the numerical table; exactness for every length is proved above. -/
def longRequests : List RecurringRequest :=
  [.local (.inspect .reading 0), .local (.inspect .signal 0), .compare 0 3, .compare 0 0,
    .local (.receive 1), .compare 1 0, .local (.inspect .reading 0), .compare 0 1,
    .local (.emit 0 6), .local (.receive 0), .compare 3 0, .local (.inspect .reading 0), .local (.receive 100)]

def requestCode : RecurringRequest → Nat × Nat × Nat
  | .local (.emit first second) => (0, first, second)
  | .local (.relay first second) => (1, first, second)
  | .local (.receive port) => (2, port, 0)
  | .local (.inspect kind port) =>
    let tag := match kind with
      | .reading => 3 | .signal => 4 | .calibration => 5 | .payload => 6
    (tag, port, 0)
  | .compare first second => (7, first, second)

#eval let longRun := runCorrespondingRecurring initial longRequests
  (longRun.translated.map requestCode, permissions longRun.first.report, permissions longRun.second.report,
    (comparisons longRun.first.report).map Rational.index,
    StrongPerimetralTurning.History.length longRun.first.history,
    StrongPerimetralTurning.History.length longRun.second.history)

end Tests.Relativity.TransportedRecurringChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.TransportedRecurringChecks.initial
#print axioms Tests.Relativity.TransportedRecurringChecks.same_actual_source_support
#print axioms Tests.Relativity.TransportedRecurringChecks.exchanged_positions_are_not_identity
#print axioms Tests.Relativity.TransportedRecurringChecks.request_returns
#print axioms Tests.Relativity.TransportedRecurringChecks.originalArrival
#print axioms Tests.Relativity.TransportedRecurringChecks.exchangedArrival
#print axioms Tests.Relativity.TransportedRecurringChecks.returnedArrival
#print axioms Tests.Relativity.TransportedRecurringChecks.no_value_substitution_for_reception
#print axioms Tests.Relativity.TransportedRecurringChecks.same_occurrence_still_refused
#print axioms Tests.Relativity.TransportedRecurringChecks.all_current_admissions_and_refusals
#print axioms Tests.Relativity.TransportedRecurringChecks.translated_requests_use_current_ports
#print axioms Tests.Relativity.TransportedRecurringChecks.source_is_the_existing_runner
#print axioms Tests.Relativity.TransportedRecurringChecks.target_is_the_existing_runner
#print axioms Tests.Relativity.TransportedRecurringChecks.complete_forward_contract
#print axioms Tests.Relativity.TransportedRecurringChecks.complete_reverse_contract
#print axioms Tests.Relativity.TransportedRecurringChecks.mixed_permissions
#print axioms Tests.Relativity.TransportedRecurringChecks.compared_values_are_actual_outputs
#print axioms Tests.Relativity.TransportedRecurringChecks.two_shared_productions
#print axioms Tests.Relativity.TransportedRecurringChecks.both_production_counts_agree
#print axioms Tests.Relativity.TransportedRecurringChecks.no_request_dropped
#print axioms Tests.Relativity.TransportedRecurringChecks.final_readings_still_correspond
#print axioms Tests.Relativity.TransportedRecurringChecks.sourceArrivalStillPresent
#print axioms Tests.Relativity.TransportedRecurringChecks.targetArrivalStillPresent
#print axioms Tests.Relativity.TransportedRecurringChecks.sourceArrivalReturned
#print axioms Tests.Relativity.TransportedRecurringChecks.sourceEdgeStillUsed
#print axioms Tests.Relativity.TransportedRecurringChecks.targetEdgeStillUsed
#print axioms Tests.Relativity.TransportedRecurringChecks.sourceEdgeReturned
#print axioms Tests.Relativity.TransportedRecurringChecks.comparison_address_follows_production
#print axioms Tests.Relativity.TransportedRecurringChecks.frozen_translation_changes_the_contract
#print axioms Tests.Relativity.TransportedRecurringChecks.changed_address_does_not_identify_occurrences
#print axioms Tests.Relativity.TransportedRecurringChecks.resume_from_actual_cursors
#print axioms Tests.Relativity.TransportedRecurringChecks.continuedSourceHistory
#print axioms Tests.Relativity.TransportedRecurringChecks.continuedTargetHistory
#print axioms Tests.Relativity.TransportedRecurringChecks.histories_consume_the_stored_continuation
#print axioms Tests.Relativity.TransportedRecurringChecks.longRequests
#print axioms Tests.Relativity.TransportedRecurringChecks.requestCode
/- AXIOM_AUDIT_END -/
