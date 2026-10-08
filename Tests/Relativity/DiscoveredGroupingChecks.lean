import RelationalPerimeter

/-! Closed discovery, exact shared continuation and a future separator.
The two histories describe exchanged occurrences, not two equal sources. -/
set_option genInjectivity false
namespace Tests.Relativity.DiscoveredGroupingChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := emittedCursor input
def first : Instruction source.kinds .signal := .relay .here (.prior (.prior (.prior .here)))
def independentSecond : Instruction (.signal :: source.kinds) .reading := .receive (.prior .here)
def actual := produceStoredPair source first independentSecond

theorem exchange_is_found : exchangeFound actual = true := rfl
def found := discoveredExchangeOfFound actual exchange_is_found

theorem source_cursor_is_the_actual_runner : actual.execution =
    run source (.step first (.step independentSecond .done)) := stored_pair_runner_exact source first independentSecond

theorem exchanged_outputs_use_cached_determinations :
    (found.exchanged.cursor.read (.here : Ref found.exchanged.cursor.kinds .signal)) = actual.firstDetermination.1 ∧
      (found.exchanged.cursor.read (.prior .here : Ref found.exchanged.cursor.kinds .reading)) =
        actual.secondDetermination.1 := ⟨rfl, rfl⟩

theorem exchange_is_not_occurrence_identity : found.raccord.addresses.forward 0 = 1 ∧
    found.raccord.addresses.forward 1 = 0 := ⟨rfl, rfl⟩

def requests : List RecurringRequest :=
  [.local (.inspect .reading 0), .local (.receive 1), .compare 1 0, .compare 0 1, .local (.receive 100)]
def grouped := found.continue requests

theorem whole_source_runner_exact : grouped.first = runRecurringRequests (.fromCursor actual.cursor) requests :=
  (shared_recurring_runners_exact found.raccord requests).1

theorem whole_other_runner_exact : grouped.second =
    runRecurringRequests (.fromCursor found.exchanged.cursor) grouped.translated :=
  (shared_recurring_runners_exact found.raccord requests).2

theorem every_finite_future_preserved (future : List RecurringRequest) :
    recurringContract.outcome (.fromCursor found.exchanged.cursor) (found.continue future).translated =
      recurringContract.outcome (.fromCursor actual.cursor) future := discovered_exchange_all_futures found future

theorem every_reverse_future_preserved (future : List RecurringRequest) :
    recurringContract.outcome (.fromCursor actual.cursor) (runSharedRecurring found.raccord.reverse future).translated =
      recurringContract.outcome (.fromCursor found.exchanged.cursor) future := shared_recurring_all_futures found.raccord.reverse future

theorem translated_addresses_are_current : grouped.translated =
    [.local (.inspect .reading 1), .local (.receive 0), .compare 2 0, .compare 0 1, .local (.receive 100)] := rfl

def permissions : Outcome RecurringEvent Unit → List Bool
  | .stop _ => []
  | .step _ allowed _ rest => allowed :: permissions rest

theorem permissions_include_refusals : permissions grouped.first.report = [true, true, true, false, false] := rfl
theorem presentation_reports_agree : grouped.second.report = grouped.first.report := grouped.reportExact

def oldArrival : RecurringArrival (RecurringCursor.fromCursor actual.cursor).formation
    (Ref.here : Ref actual.cursor.kinds .reading) (.prior (.prior .here)) :=
  .fromCursor (Arrived.ofReception (source.extend actual.firstDetermination).formation actual.secondDetermination.2)
def stillArrived := recurringHistoryArrival grouped.first.history oldArrival
def otherArrival := grouped.raccord.constitution.forwardArrival stillArrived
def returnedArrival := grouped.raccord.constitution.backwardArrival otherArrival

theorem source_occurrences_still_distinct :
    (recurringHistoryTransport grouped.first.history).references (Ref.here : Ref actual.cursor.kinds .reading) ≠
      (recurringHistoryTransport grouped.first.history).references (.prior (.prior (.prior .here))) := by
  intro same
  have original := (recurringHistoryTransport grouped.first.history).injective _ _ same
  exact fresh_position_distinct (.prior (.prior .here)) (congrArg Ref.position original)

def resumed := grouped.continueShared [.local (.inspect .reading 0), .compare 0 1]
def sourceHistory := grouped.firstContinuedHistory resumed
def otherHistory := grouped.secondContinuedHistory resumed

theorem continuation_uses_actual_cursors : resumed.first =
    runRecurringRequests grouped.first.cursor [.local (.inspect .reading 0), .compare 0 1] :=
  (shared_continuation_exact grouped _).1

theorem assembly_uses_stored_suffix :
    sourceHistory = StrongPerimetralTurning.History.append grouped.first.history resumed.first.history ∧
      otherHistory = StrongPerimetralTurning.History.append grouped.second.history resumed.second.history :=
  recurring_continued_history_uses_cached_suffix grouped resumed

def dependentSecond : Instruction (.signal :: source.kinds) .reading := .receive .here
def dependentPair : StoredPairProduction source first dependentSecond :=
  ⟨actual.firstDetermination, execute (source.extend actual.firstDetermination).values dependentSecond⟩

theorem both_cases_share_the_same_first_production : dependentPair.firstDetermination = actual.firstDetermination := rfl
def fresh_use_is_found : InputPort dependentSecond (Ref.here : Ref (.signal :: source.kinds) .signal) :=
  .receptionSignal .here
theorem dependent_exchange_is_refused : exchangeFound dependentPair = false := rfl
def discoveredFreshPort := freshPortOfRefusedExchange dependentPair dependent_exchange_is_refused
def discoveredActualEdge := dependentPair.freshUsedEdge discoveredFreshPort
theorem no_old_port_license (old : OldInstruction dependentSecond) : False :=
  exchange_refusal_excludes_old dependentPair dependent_exchange_is_refused old

def naive := produceIndependentPair source (.receive (.here : Ref source.kinds .signal)) first

theorem future_reading_separates_naive_exchange :
    dependentPair.cursor.read (Ref.here : Ref dependentPair.cursor.kinds .reading) ≠
      naive.cursor.read (.prior .here : Ref naive.cursor.kinds .reading) :=
  relay_changes_reading (source.read .here) input.calibration

theorem future_report_separates_naive_exchange :
    recurringContract.outcome (.fromCursor dependentPair.cursor) [.local (.inspect .reading 0)] ≠
      recurringContract.outcome (.fromCursor naive.cursor) [.local (.inspect .reading 1)] := by
  intro same
  have observation := congrArg firstRecurringInspection same
  have reading := Option.some.inj observation
  have numeric := congrArg (fun value : LocalReadout => match value with
    | .reading reading => reading
    | .payload _ => Rational.zero
    | .calibration _ => Rational.zero
    | .signal _ => Rational.zero) reading
  exact future_reading_separates_naive_exchange numeric

def acceptedContinuation := searchExchangeAndContinue actual requests
def refusedContinuation := searchExchangeAndContinue dependentPair [.local (.inspect .reading 0)]

theorem accepted_branch_selected : (match acceptedContinuation with | .inl _ => true | .inr _ => false) = true := rfl
theorem refused_branch_keeps_execution : (match refusedContinuation with | .inl _ => true | .inr _ => false) = false := rfl

end Tests.Relativity.DiscoveredGroupingChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.DiscoveredGroupingChecks.exchange_is_found
#print axioms Tests.Relativity.DiscoveredGroupingChecks.found
#print axioms Tests.Relativity.DiscoveredGroupingChecks.source_cursor_is_the_actual_runner
#print axioms Tests.Relativity.DiscoveredGroupingChecks.exchanged_outputs_use_cached_determinations
#print axioms Tests.Relativity.DiscoveredGroupingChecks.exchange_is_not_occurrence_identity
#print axioms Tests.Relativity.DiscoveredGroupingChecks.whole_source_runner_exact
#print axioms Tests.Relativity.DiscoveredGroupingChecks.whole_other_runner_exact
#print axioms Tests.Relativity.DiscoveredGroupingChecks.every_finite_future_preserved
#print axioms Tests.Relativity.DiscoveredGroupingChecks.every_reverse_future_preserved
#print axioms Tests.Relativity.DiscoveredGroupingChecks.translated_addresses_are_current
#print axioms Tests.Relativity.DiscoveredGroupingChecks.permissions_include_refusals
#print axioms Tests.Relativity.DiscoveredGroupingChecks.presentation_reports_agree
#print axioms Tests.Relativity.DiscoveredGroupingChecks.oldArrival
#print axioms Tests.Relativity.DiscoveredGroupingChecks.stillArrived
#print axioms Tests.Relativity.DiscoveredGroupingChecks.otherArrival
#print axioms Tests.Relativity.DiscoveredGroupingChecks.returnedArrival
#print axioms Tests.Relativity.DiscoveredGroupingChecks.source_occurrences_still_distinct
#print axioms Tests.Relativity.DiscoveredGroupingChecks.continuation_uses_actual_cursors
#print axioms Tests.Relativity.DiscoveredGroupingChecks.assembly_uses_stored_suffix
#print axioms Tests.Relativity.DiscoveredGroupingChecks.both_cases_share_the_same_first_production
#print axioms Tests.Relativity.DiscoveredGroupingChecks.fresh_use_is_found
#print axioms Tests.Relativity.DiscoveredGroupingChecks.dependent_exchange_is_refused
#print axioms Tests.Relativity.DiscoveredGroupingChecks.discoveredFreshPort
#print axioms Tests.Relativity.DiscoveredGroupingChecks.discoveredActualEdge
#print axioms Tests.Relativity.DiscoveredGroupingChecks.no_old_port_license
#print axioms Tests.Relativity.DiscoveredGroupingChecks.future_reading_separates_naive_exchange
#print axioms Tests.Relativity.DiscoveredGroupingChecks.future_report_separates_naive_exchange
#print axioms Tests.Relativity.DiscoveredGroupingChecks.accepted_branch_selected
#print axioms Tests.Relativity.DiscoveredGroupingChecks.refused_branch_keeps_execution
/- AXIOM_AUDIT_END -/
