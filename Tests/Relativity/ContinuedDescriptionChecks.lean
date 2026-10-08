import RelationalPerimeter

/-! Closed client: discovered exchange, mixed requests, then actual resumed
continuation. Agreements consume the same stored run, not new producers. -/
set_option genInjectivity false
namespace Tests.Relativity.ContinuedDescriptionChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def arrivals : (source : Cursor) ×' ArrivalPair source :=
  let relayed := (relayExecution input 2).cursor
  let first := perform relayed (.receive .here)
  let emitted := perform first.successor
    (.emit .here (.prior (.prior (.prior (.prior (.prior .here))))))
  let second := perform emitted.successor (.receive .here)
  let earlier := Arrived.inherited second.determination.2
    (Arrived.inherited emitted.determination.2 (arrivalOfProduction first))
  ⟨second.successor, ⟨.prior (.prior .here), .here, .prior (.prior (.prior .here)), .prior .here,
    earlier, arrivalOfProduction second, fun same =>
      fresh_distinct emitted.successor second.determination (.prior .here) same.symm⟩⟩

def actual := produceStoredPair arrivals.1 (Instruction.receive arrivals.2.firstSignal)
  (Instruction.receive (Ref.prior arrivals.2.secondSignal))

theorem exchange_really_found : exchangeFound actual = true := rfl
def found := discoveredExchangeOfFound actual exchange_really_found
def origin : RecurringCursor := .fromCursor actual.cursor

def pair : RecurringPair origin :=
  ⟨.prior .here, .here, .prior (.prior arrivals.2.firstSignal), .prior (.prior arrivals.2.secondSignal),
    .fromCursor (.inherited actual.secondDetermination.2
      (Arrived.ofReception arrivals.1.formation actual.firstDetermination.2)),
    .fromCursor (Arrived.ofReception (arrivals.1.extend actual.firstDetermination).formation
      actual.secondDetermination.2), fun same =>
        fresh_distinct (arrivals.1.extend actual.firstDetermination) actual.secondDetermination .here same.symm⟩

def head := performRecurring origin (.compare pair)
def transportedHead := transportRecurringProduction found.raccord.constitution head
def changed := found.raccord.afterProduction head transportedHead
def one := InteractionAttachment.first head .root
def two := InteractionAttachment.second head .root
def renamed := one.reexpress changed
def partner := two.reexpress changed
def rich := AttachedDescriptionAgreement.reexpression one changed
def site : InteractionSiteAgreement one partner := ⟨changed, rfl⟩

def requests : List RecurringRequest :=
  [.compare one.readingReference.position two.readingReference.position,
   .local (.inspect .signal (one.signalReference.position + 1)),
   .compare 0 0,
   .local (.emit 0 (head.successor.kinds.length - 2 + 1)),
   .local (.receive 0),
   .local (.inspect .reading 0),
   .compare 0 1,
   .compare (one.readingReference.position + 3) (two.readingReference.position + 3)]

/-- Keep the computed history abstract during dependent type elaboration.
Its executable body is unchanged; the equation is proved explicitly below. -/
@[irreducible] def extension := runDescriptionExtension changed requests
def continuedRich := extension.rich rich
def continuedSite := extension.site site
def first := extension.first one
def second := extension.first two
def other := extension.second renamed

def permissions : Outcome RecurringEvent Unit → List Bool
  | .stop _ => []
  | .step _ allowed _ rest => allowed :: permissions rest

theorem extension_is_the_executed_run : extension = runDescriptionExtension changed requests := by
  unfold extension
  rfl

theorem source_execution_exact : extension.execution.first = runRecurringRequests head.successor requests := by
  rw [extension_is_the_executed_run]
  exact (shared_recurring_runners_exact changed requests).1

theorem mixed_admissions_and_refusals : permissions extension.execution.first.report =
    [true, true, false, true, true, true, false, true] := by
  rw [source_execution_exact]
  rfl

theorem mixed_trace_has_four_productions :
    StrongPerimetralTurning.History.length extension.execution.first.history = 4 := by
  rw [source_execution_exact]
  rfl

theorem both_presentations_have_four_productions :
    StrongPerimetralTurning.History.length extension.execution.second.history = 4 := by
  have same := description_extension_history_lengths changed requests
  rw [← extension_is_the_executed_run] at same
  exact same.trans mixed_trace_has_four_productions

theorem requests_are_not_dropped : extension.execution.translated.length = 8 :=
  by rw [extension_is_the_executed_run]; exact description_extension_request_length changed requests

theorem output_reports_match_the_contract :
    extension.execution.first.report = recurringContract.outcome head.successor requests ∧
      extension.execution.second.report = recurringContract.outcome transportedHead.successor extension.execution.translated :=
  by rw [extension_is_the_executed_run]; exact description_extension_reports_exact changed requests

theorem retained_anchor_follows_actual_histories :
    extension.execution.raccord.constitution.references.forward first.anchor = other.anchor :=
  continuedRich.anchorExact

theorem retained_reception_follows_actual_histories :
    extension.execution.raccord.constitution.references.forward first.readingReference = other.readingReference :=
  continuedRich.readingExact

theorem retained_signal_follows_actual_histories :
    extension.execution.raccord.constitution.references.forward first.signalReference = other.signalReference :=
  continuedRich.signalExact

def continuedArrival := other.transportedArrival
def continuedUsedPort := other.usedPort

theorem current_agreement_uses_produced_raccord : continuedRich.raccord = extension.execution.raccord :=
  continued_rich_raccord_is_produced rich extension

theorem interaction_survives_without_rich_identification :
    extension.execution.raccord.constitution.references.forward first.anchor =
      (extension.second partner).anchor := continuedSite.anchorExact

theorem source_receptions_still_distinct : first.readingReference ≠ second.readingReference :=
  fun same => (participants_remain_distinct head DescriptionPath.root)
    ((recurringHistoryTransport extension.execution.first.history).injective _ _
      ((attached_prolong_reading_reference one _).symm.trans
        (same.trans (attached_prolong_reading_reference two _))))

theorem original_effects_still_differ : one.effects ≠ partner.effects := by
  intro same
  have lengths := congrArg (fun record : SignalRecord => record.increments.length) same
  change 2 = 0 at lengths
  cases lengths

theorem continued_site_cannot_give_rich_agreement
    (agreement : AttachedDescriptionAgreement first (extension.second partner)) : False :=
  continued_site_cannot_erase_different_effects site extension original_effects_still_differ agreement

theorem refine_after_continuation {coarse fine} (refines : ReaderRefinement coarse fine) :
    (other.observe fine).restrict coarse = one.observe coarse :=
  continued_refinement_square rich extension refines

theorem all_readers_are_preserved (readers : SignalReaders) :
    first.observe readers = one.observe readers ∧ other.observe readers = one.observe readers :=
  continued_observation_square rich extension readers

theorem old_description_gains_only_executed_productions :
    first.path.producedCount = one.path.producedCount + 4 :=
  (continued_production_counts rich extension).1.trans
    (congrArg (Nat.add one.path.producedCount) mixed_trace_has_four_productions)

def more : List RecurringRequest :=
  [.local (.inspect .signal first.signalReference.position),
   .compare first.readingReference.position second.readingReference.position]
def resumed := extension.resume more
def combined := extension.append resumed
def twice := resumed.first first

theorem resumed_reports_use_actual_endpoints :
    resumed.execution.first.report = recurringContract.outcome extension.execution.first.cursor more ∧
      resumed.execution.second.report = recurringContract.outcome extension.execution.second.cursor resumed.execution.translated :=
  by unfold resumed; exact description_extension_resume_exact extension more

theorem resumed_comparison_is_admitted : permissions resumed.execution.first.report = [true, true] := by
  unfold resumed SharedDescriptionExtension.resume runDescriptionExtension
  rw [(shared_recurring_runners_exact extension.execution.raccord more).1]
  change permissions (runRecurringRequests extension.execution.first.cursor more).report = _
  dsimp only [more, runRecurringRequests]
  rw [recurring_perform_of_admitted extension.execution.first.cursor
    (.local (.inspect .signal first.signalReference.position)) (ReferenceAt.mk first.signalReference rfl)]
  change true :: permissions (runRecurringRequests extension.execution.first.cursor
    [.compare first.readingReference.position second.readingReference.position]).report = _
  dsimp only [runRecurringRequests]
  rw [recurring_perform_of_admitted extension.execution.first.cursor
    (.compare first.readingReference.position second.readingReference.position)
    (RecurringComparisonAdmission.mk
      ⟨⟨first.readingReference, rfl⟩, first.signalReference, first.transportedArrival⟩
      ⟨⟨second.readingReference, rfl⟩, second.signalReference, second.transportedArrival⟩
      source_receptions_still_distinct)]
  rfl

theorem stored_histories_compose :
    combined.execution.first.history = StrongPerimetralTurning.History.append
      extension.execution.first.history resumed.execution.first.history := by unfold combined; rfl

theorem descriptions_compose_on_each_occurrence {kind} (ref : Ref head.successor.kinds kind) :
    (combined.first one).path.reference ref = twice.path.reference ref :=
  by unfold combined; exact appended_description_reference extension resumed one ref

theorem composed_report_is_the_complete_source_future : combined.execution.first.report =
    recurringContract.outcome head.successor (requests ++ more) :=
  by unfold combined resumed; rw [extension_is_the_executed_run]
     exact appended_description_source_report_exact changed requests more

theorem composed_report_is_the_complete_target_future : combined.execution.second.report =
    recurringContract.outcome transportedHead.successor
      (extension.execution.translated ++ resumed.execution.translated) :=
  by unfold combined resumed; rw [extension_is_the_executed_run]
     exact appended_description_target_report_exact changed requests more

theorem all_future_suffixes_keep_the_reference_square (future : List RecurringRequest) {kind}
    (ref : Ref extension.execution.first.cursor.kinds kind) :
    (extension.resume future).execution.raccord.constitution.references.forward
        ((recurringHistoryTransport (extension.resume future).execution.first.history).references ref) =
      (recurringHistoryTransport (extension.resume future).execution.second.history).references
        (extension.execution.raccord.constitution.references.forward ref) :=
  (extension.resume future).referenceSquare ref

theorem all_future_suffixes_keep_reader_refinement (future : List RecurringRequest) {coarse fine}
    (refines : ReaderRefinement coarse fine) :
    (((extension.resume future).second other).observe fine).restrict coarse = first.observe coarse :=
  continued_refinement_square continuedRich (extension.resume future) refines

end Tests.Relativity.ContinuedDescriptionChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ContinuedDescriptionChecks.arrivals
#print axioms Tests.Relativity.ContinuedDescriptionChecks.actual
#print axioms Tests.Relativity.ContinuedDescriptionChecks.exchange_really_found
#print axioms Tests.Relativity.ContinuedDescriptionChecks.found
#print axioms Tests.Relativity.ContinuedDescriptionChecks.pair
#print axioms Tests.Relativity.ContinuedDescriptionChecks.head
#print axioms Tests.Relativity.ContinuedDescriptionChecks.transportedHead
#print axioms Tests.Relativity.ContinuedDescriptionChecks.extension
#print axioms Tests.Relativity.ContinuedDescriptionChecks.continuedRich
#print axioms Tests.Relativity.ContinuedDescriptionChecks.continuedSite
#print axioms Tests.Relativity.ContinuedDescriptionChecks.extension_is_the_executed_run
#print axioms Tests.Relativity.ContinuedDescriptionChecks.source_execution_exact
#print axioms Tests.Relativity.ContinuedDescriptionChecks.mixed_admissions_and_refusals
#print axioms Tests.Relativity.ContinuedDescriptionChecks.mixed_trace_has_four_productions
#print axioms Tests.Relativity.ContinuedDescriptionChecks.both_presentations_have_four_productions
#print axioms Tests.Relativity.ContinuedDescriptionChecks.requests_are_not_dropped
#print axioms Tests.Relativity.ContinuedDescriptionChecks.output_reports_match_the_contract
#print axioms Tests.Relativity.ContinuedDescriptionChecks.retained_anchor_follows_actual_histories
#print axioms Tests.Relativity.ContinuedDescriptionChecks.retained_reception_follows_actual_histories
#print axioms Tests.Relativity.ContinuedDescriptionChecks.retained_signal_follows_actual_histories
#print axioms Tests.Relativity.ContinuedDescriptionChecks.continuedArrival
#print axioms Tests.Relativity.ContinuedDescriptionChecks.continuedUsedPort
#print axioms Tests.Relativity.ContinuedDescriptionChecks.current_agreement_uses_produced_raccord
#print axioms Tests.Relativity.ContinuedDescriptionChecks.interaction_survives_without_rich_identification
#print axioms Tests.Relativity.ContinuedDescriptionChecks.source_receptions_still_distinct
#print axioms Tests.Relativity.ContinuedDescriptionChecks.original_effects_still_differ
#print axioms Tests.Relativity.ContinuedDescriptionChecks.continued_site_cannot_give_rich_agreement
#print axioms Tests.Relativity.ContinuedDescriptionChecks.refine_after_continuation
#print axioms Tests.Relativity.ContinuedDescriptionChecks.all_readers_are_preserved
#print axioms Tests.Relativity.ContinuedDescriptionChecks.old_description_gains_only_executed_productions
#print axioms Tests.Relativity.ContinuedDescriptionChecks.resumed
#print axioms Tests.Relativity.ContinuedDescriptionChecks.combined
#print axioms Tests.Relativity.ContinuedDescriptionChecks.resumed_reports_use_actual_endpoints
#print axioms Tests.Relativity.ContinuedDescriptionChecks.resumed_comparison_is_admitted
#print axioms Tests.Relativity.ContinuedDescriptionChecks.stored_histories_compose
#print axioms Tests.Relativity.ContinuedDescriptionChecks.descriptions_compose_on_each_occurrence
#print axioms Tests.Relativity.ContinuedDescriptionChecks.composed_report_is_the_complete_source_future
#print axioms Tests.Relativity.ContinuedDescriptionChecks.composed_report_is_the_complete_target_future
#print axioms Tests.Relativity.ContinuedDescriptionChecks.all_future_suffixes_keep_the_reference_square
#print axioms Tests.Relativity.ContinuedDescriptionChecks.all_future_suffixes_keep_reader_refinement
/- AXIOM_AUDIT_END -/
