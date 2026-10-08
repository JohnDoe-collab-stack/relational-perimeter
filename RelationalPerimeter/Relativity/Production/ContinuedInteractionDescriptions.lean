import RelationalPerimeter.Relativity.Production.InteractionDescriptionAgreement

/-!
# Attached agreements through an actually shared continuation

The reference square is derived from the executed heads and their histories.
One cached shared run supplies both prolongations and the final exact raccord.
Describing that run does not replay it. Reader restriction remains distinct
from productive extension and licenses no memory erasure or physical meeting.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

theorem recurring_append_reference {source middle target}
    (first : RecurringHistory source middle) (second : RecurringHistory middle target)
    {kind} (ref : Ref source.kinds kind) :
    (recurringHistoryTransport (StrongPerimetralTurning.History.append first second)).references ref =
      (recurringHistoryTransport second).references ((recurringHistoryTransport first).references ref) := by
  induction second with
  | root => rfl
  | extend past step ih => exact congrArg step.transport.references ih

theorem recurring_production_reference_square {source target}
    (raccord : AddressedRecurringRaccord source target) {kind} {action : RecurringAction source kind}
    (one : RecurringProduction source action)
    (two : RecurringProduction target (action.rename raccord.constitution))
    {oldKind} (ref : Ref source.kinds oldKind) :
    (raccord.afterProduction one two).constitution.references.forward
        ((recurringHistoryTransport (recurringProductionHistory one)).references ref) =
      (recurringHistoryTransport (recurringProductionHistory two)).references
        (raccord.constitution.references.forward ref) := by
  cases one with
  | mk first firstSuccessor firstExact =>
    cases firstExact
    cases two with
    | mk second secondSuccessor secondExact =>
      cases secondExact
      cases action with
      | signal instruction =>
        cases first with | mk output role =>
          cases role with | signal localRole =>
            cases second with | mk otherOutput otherRole => cases otherRole; rfl
      | compare pair =>
        cases first with | mk output role =>
          cases role with | compared localRole =>
            cases second with | mk otherOutput otherRole => cases otherRole; rfl

theorem paired_admitted_reference_square {source target}
    (raccord : AddressedRecurringRaccord source target) (request : RecurringRequest)
    (admitted : RecurringAdmission source request) {kind} (ref : Ref source.kinds kind) :
    (pairedRecurringAdmitted raccord request admitted).raccord.constitution.references.forward
        ((recurringHistoryTransport (pairedRecurringAdmitted raccord request admitted).first.history).references ref) =
      (recurringHistoryTransport (pairedRecurringAdmitted raccord request admitted).second.history).references
        (raccord.constitution.references.forward ref) := by
  cases request with
  | «local» request =>
    cases request with
    | emit _ _ => exact recurring_production_reference_square ..
    | relay _ _ => exact recurring_production_reference_square ..
    | receive _ => exact recurring_production_reference_square ..
    | inspect _ _ => rfl
  | compare _ _ => exact recurring_production_reference_square ..

theorem shared_request_reference_square {source target}
    (raccord : AddressedRecurringRaccord source target) (request : RecurringRequest)
    {kind} (ref : Ref source.kinds kind) :
    (sharedRecurringRequest raccord request).raccord.constitution.references.forward
        ((recurringHistoryTransport (sharedRecurringRequest raccord request).first.history).references ref) =
      (recurringHistoryTransport (sharedRecurringRequest raccord request).second.history).references
        (raccord.constitution.references.forward ref) := by
  rw [shared_request_exact]
  unfold pairedRecurringRequest
  cases decideRecurringAdmission source request with
  | inl admitted => exact paired_admitted_reference_square raccord request admitted ref
  | inr _ => rfl

theorem shared_run_reference_square {source target}
    (raccord : AddressedRecurringRaccord source target) (requests : List RecurringRequest)
    {kind} (ref : Ref source.kinds kind) :
    (runSharedRecurring raccord requests).raccord.constitution.references.forward
        ((recurringHistoryTransport (runSharedRecurring raccord requests).first.history).references ref) =
      (recurringHistoryTransport (runSharedRecurring raccord requests).second.history).references
        (raccord.constitution.references.forward ref) := by
  induction requests generalizing source target with
  | nil => rfl
  | cons request rest ih =>
    let head := sharedRecurringRequest raccord request
    let suffix := runSharedRecurring head.raccord rest
    change suffix.raccord.constitution.references.forward
        ((recurringHistoryTransport (StrongPerimetralTurning.History.append head.first.history suffix.first.history)).references ref) =
      (recurringHistoryTransport (StrongPerimetralTurning.History.append head.second.history suffix.second.history)).references
        (raccord.constitution.references.forward ref)
    rw [recurring_append_reference, recurring_append_reference]
    exact (ih head.raccord _).trans
      (congrArg (recurringHistoryTransport suffix.second.history).references
        (shared_request_reference_square raccord request ref))

/-- A cached execution with the reference square needed to prolong descriptions.
This is not a quotient and does not characterize arbitrary equivalent histories. -/
structure SharedDescriptionExtension {source target}
    (initial : AddressedRecurringRaccord source target) where
  execution : CorrespondingRecurringRequests source target
  referenceSquare : ∀ {kind} (ref : Ref source.kinds kind),
    execution.raccord.constitution.references.forward
        ((recurringHistoryTransport execution.first.history).references ref) =
      (recurringHistoryTransport execution.second.history).references
        (initial.constitution.references.forward ref)

def runDescriptionExtension {source target} (initial : AddressedRecurringRaccord source target)
    (requests : List RecurringRequest) : SharedDescriptionExtension initial :=
  let execution := runSharedRecurring initial requests
  ⟨execution, shared_run_reference_square initial requests⟩

theorem description_extension_is_shared_run {source target}
    (initial : AddressedRecurringRaccord source target) (requests : List RecurringRequest) :
    (runDescriptionExtension initial requests).execution = runSharedRecurring initial requests := rfl

def SharedDescriptionExtension.first {source target} {initial : AddressedRecurringRaccord source target}
    (extension : SharedDescriptionExtension initial) {origin pair head}
    (attached : @InteractionAttachment origin pair head source) :
    InteractionAttachment head extension.execution.first.cursor :=
  attached.prolong extension.execution.first.history

def SharedDescriptionExtension.second {source target} {initial : AddressedRecurringRaccord source target}
    (extension : SharedDescriptionExtension initial) {origin pair head}
    (attached : @InteractionAttachment origin pair head target) :
    InteractionAttachment head extension.execution.second.cursor :=
  attached.prolong extension.execution.second.history

def SharedDescriptionExtension.site {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : InteractionSiteAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) :
    InteractionSiteAgreement (extension.first one) (extension.second two) :=
  ⟨extension.execution.raccord,
    (congrArg extension.execution.raccord.constitution.references.forward
      (attached_prolong_anchor one extension.execution.first.history)).trans
      ((extension.referenceSquare one.anchor).trans
        ((congrArg (recurringHistoryTransport extension.execution.second.history).references agreement.anchorExact).trans
          (attached_prolong_anchor two extension.execution.second.history).symm))⟩

theorem attached_prolong_reading_reference {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target) :
    (attached.prolong history).readingReference =
      (recurringHistoryTransport history).references attached.readingReference :=
  attached.path.prolong_reference history _

theorem attached_prolong_signal_reference {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target) :
    (attached.prolong history).signalReference =
      (recurringHistoryTransport history).references attached.signalReference :=
  attached.path.prolong_reference history _

def SharedDescriptionExtension.rich {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : AttachedDescriptionAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) :
    AttachedDescriptionAgreement (extension.first one) (extension.second two) :=
  ⟨extension.execution.raccord, (extension.site agreement.site).anchorExact,
    (congrArg extension.execution.raccord.constitution.references.forward
      (attached_prolong_reading_reference one extension.execution.first.history)).trans
      ((extension.referenceSquare one.readingReference).trans
        ((congrArg (recurringHistoryTransport extension.execution.second.history).references agreement.readingExact).trans
          (attached_prolong_reading_reference two extension.execution.second.history).symm)),
    (congrArg extension.execution.raccord.constitution.references.forward
      (attached_prolong_signal_reference one extension.execution.first.history)).trans
      ((extension.referenceSquare one.signalReference).trans
        ((congrArg (recurringHistoryTransport extension.execution.second.history).references agreement.signalExact).trans
          (attached_prolong_signal_reference two extension.execution.second.history).symm))⟩

theorem continued_rich_raccord_is_produced {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : AttachedDescriptionAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) :
    (extension.rich agreement).raccord = extension.execution.raccord := rfl

theorem continued_observation_square {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : AttachedDescriptionAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) (readers : SignalReaders) :
    (extension.first one).observe readers = one.observe readers ∧
      (extension.second two).observe readers = one.observe readers :=
  ⟨attached_observation_prolong one _ readers,
    (attached_observation_prolong two _ readers).trans (attached_agreement_observations agreement readers)⟩

theorem continued_refinement_square {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : AttachedDescriptionAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) {coarse fine}
    (refinement : ReaderRefinement coarse fine) :
    ((extension.second two).observe fine).restrict coarse = one.observe coarse :=
  (attached_observation_restrict _ refinement).trans (continued_observation_square agreement extension coarse).2

theorem continued_production_counts {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : AttachedDescriptionAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) :
    (extension.first one).path.producedCount = one.path.producedCount +
        StrongPerimetralTurning.History.length extension.execution.first.history ∧
      (extension.second two).path.producedCount = two.path.producedCount +
        StrongPerimetralTurning.History.length extension.execution.second.history :=
  ⟨one.path.prolong_count _, two.path.prolong_count _⟩

def SharedDescriptionExtension.resume {source target} {initial : AddressedRecurringRaccord source target}
    (prior : SharedDescriptionExtension initial) (requests : List RecurringRequest) :
    SharedDescriptionExtension prior.execution.raccord := runDescriptionExtension prior.execution.raccord requests

/-- Unit has no terminal observation to retain at the intermediate join.
All prefix events and admission bits remain in this executable report splice. -/
def appendRecurringReport (first second : Outcome RecurringEvent Unit) : Outcome RecurringEvent Unit :=
  match first with
  | .stop _ => second
  | .step observed allowed event rest => .step observed allowed event (appendRecurringReport rest second)
termination_by structural first

def SharedDescriptionExtension.append {source target} {initial : AddressedRecurringRaccord source target}
    (first : SharedDescriptionExtension initial) (second : SharedDescriptionExtension first.execution.raccord) :
    SharedDescriptionExtension initial :=
  ⟨⟨⟨second.execution.first.cursor,
        StrongPerimetralTurning.History.append first.execution.first.history second.execution.first.history,
        appendRecurringReport first.execution.first.report second.execution.first.report⟩,
      ⟨second.execution.second.cursor,
        StrongPerimetralTurning.History.append first.execution.second.history second.execution.second.history,
        appendRecurringReport first.execution.second.report second.execution.second.report⟩,
      first.execution.translated ++ second.execution.translated, second.execution.raccord,
      by rw [first.execution.reportExact, second.execution.reportExact]⟩,
    fun ref => by
      rw [recurring_append_reference, recurring_append_reference]
      exact (second.referenceSquare _).trans
        (congrArg (recurringHistoryTransport second.execution.second.history).references (first.referenceSquare ref))⟩

theorem description_extension_reports_exact {source target}
    (initial : AddressedRecurringRaccord source target) (requests : List RecurringRequest) :
    (runDescriptionExtension initial requests).execution.first.report = recurringContract.outcome source requests ∧
      (runDescriptionExtension initial requests).execution.second.report =
        recurringContract.outcome target (runDescriptionExtension initial requests).execution.translated := by
  have exactRunners := shared_recurring_runners_exact initial requests
  exact ⟨(congrArg RecurringRequestedExecution.report exactRunners.1).trans (recurring_all_futures_exact ..),
    (congrArg RecurringRequestedExecution.report exactRunners.2).trans (recurring_all_futures_exact ..)⟩

theorem description_extension_history_lengths {source target}
    (initial : AddressedRecurringRaccord source target) (requests : List RecurringRequest) :
    StrongPerimetralTurning.History.length (runDescriptionExtension initial requests).execution.second.history =
      StrongPerimetralTurning.History.length (runDescriptionExtension initial requests).execution.first.history := by
  change StrongPerimetralTurning.History.length (runSharedRecurring initial requests).second.history =
    StrongPerimetralTurning.History.length (runSharedRecurring initial requests).first.history
  rw [shared_run_exact]
  exact corresponding_recurring_history_lengths initial requests

theorem description_extension_request_length {source target}
    (initial : AddressedRecurringRaccord source target) (requests : List RecurringRequest) :
    (runDescriptionExtension initial requests).execution.translated.length = requests.length := by
  change (runSharedRecurring initial requests).translated.length = requests.length
  rw [shared_run_exact]
  exact recurring_translated_length initial requests

theorem description_extension_resume_exact {source target} {initial : AddressedRecurringRaccord source target}
    (prior : SharedDescriptionExtension initial) (requests : List RecurringRequest) :
    (prior.resume requests).execution.first.report = recurringContract.outcome prior.execution.first.cursor requests ∧
      (prior.resume requests).execution.second.report = recurringContract.outcome prior.execution.second.cursor
        (prior.resume requests).execution.translated := description_extension_reports_exact prior.execution.raccord requests

theorem appended_description_reference {source target} {initial : AddressedRecurringRaccord source target}
    (first : SharedDescriptionExtension initial) (second : SharedDescriptionExtension first.execution.raccord)
    {origin pair head} (attached : @InteractionAttachment origin pair head source) {kind}
    (ref : Ref head.successor.kinds kind) :
    ((first.append second).first attached).path.reference ref =
      (second.first (first.first attached)).path.reference ref := by
  change (attached.path.prolong (StrongPerimetralTurning.History.append
      first.execution.first.history second.execution.first.history)).reference ref =
    ((attached.path.prolong first.execution.first.history).prolong second.execution.first.history).reference ref
  rw [DescriptionPath.prolong_reference, recurring_append_reference, DescriptionPath.prolong_reference,
    DescriptionPath.prolong_reference]

theorem recurring_contract_report_append (source : RecurringCursor) (earlier suffix : List RecurringRequest) :
    recurringContract.outcome source (earlier ++ suffix) = appendRecurringReport
      (recurringContract.outcome source earlier)
      (recurringContract.outcome
        (ConstitutiveSearch.Grouping.Continuation.run recurringContract.next source earlier) suffix) := by
  induction earlier generalizing source with
  | nil => rfl
  | cons request rest ih => exact congrArg (Outcome.step () (recurringContract.enabled source request)
      (recurringContract.event source request)) (ih (recurringContract.next source request))

theorem appended_description_source_report_exact {source target}
    (initial : AddressedRecurringRaccord source target) (earlier suffix : List RecurringRequest) :
    let first := runDescriptionExtension initial earlier
    let second := first.resume suffix
    (first.append second).execution.first.report = recurringContract.outcome source (earlier ++ suffix) := by
  let first := runDescriptionExtension initial earlier
  let second := first.resume suffix
  have reports := description_extension_reports_exact initial earlier
  have tailReports := description_extension_resume_exact first suffix
  have endpoint : first.execution.first.cursor =
      ConstitutiveSearch.Grouping.Continuation.run recurringContract.next source earlier :=
    (congrArg RecurringRequestedExecution.cursor (shared_recurring_runners_exact initial earlier).1).trans
      (recurring_final_cursor_exact source earlier)
  change appendRecurringReport first.execution.first.report second.execution.first.report = _
  have spliced : appendRecurringReport first.execution.first.report second.execution.first.report =
      appendRecurringReport (recurringContract.outcome source earlier)
        (recurringContract.outcome first.execution.first.cursor suffix) := by rw [reports.1, tailReports.1]
  exact (spliced.trans
    (congrArg (fun cursor => appendRecurringReport (recurringContract.outcome source earlier)
      (recurringContract.outcome cursor suffix)) endpoint)).trans (recurring_contract_report_append source earlier suffix).symm

theorem appended_description_target_report_exact {source target}
    (initial : AddressedRecurringRaccord source target) (earlier suffix : List RecurringRequest) :
    let first := runDescriptionExtension initial earlier
    let second := first.resume suffix
    (first.append second).execution.second.report = recurringContract.outcome target
      (first.execution.translated ++ second.execution.translated) := by
  let first := runDescriptionExtension initial earlier
  let second := first.resume suffix
  have reports := description_extension_reports_exact initial earlier
  have tailReports := description_extension_resume_exact first suffix
  have endpoint : first.execution.second.cursor =
      ConstitutiveSearch.Grouping.Continuation.run recurringContract.next target first.execution.translated :=
    (congrArg RecurringRequestedExecution.cursor (shared_recurring_runners_exact initial earlier).2).trans
      (recurring_final_cursor_exact target first.execution.translated)
  change appendRecurringReport first.execution.second.report second.execution.second.report = _
  have spliced : appendRecurringReport first.execution.second.report second.execution.second.report =
      appendRecurringReport (recurringContract.outcome target first.execution.translated)
        (recurringContract.outcome first.execution.second.cursor second.execution.translated) := by
    rw [reports.2, tailReports.2]
  exact (spliced.trans
    (congrArg (fun cursor => appendRecurringReport (recurringContract.outcome target first.execution.translated)
      (recurringContract.outcome cursor second.execution.translated)) endpoint)).trans
        (recurring_contract_report_append target first.execution.translated second.execution.translated).symm

theorem continued_site_cannot_erase_different_effects {origin pair head source target}
    {one : @InteractionAttachment origin pair head source}
    {two : @InteractionAttachment origin pair head target} (agreement : InteractionSiteAgreement one two)
    (extension : SharedDescriptionExtension agreement.raccord) (different : one.effects ≠ two.effects)
    (rich : AttachedDescriptionAgreement (extension.first one) (extension.second two)) : False := by
  apply different
  exact (attached_prolong_effects one _).symm.trans
    ((attached_agreement_effects rich).symm.trans (attached_prolong_effects two _))

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.recurring_append_reference
#print axioms RelationalPerimeter.Relativity.Production.recurring_production_reference_square
#print axioms RelationalPerimeter.Relativity.Production.paired_admitted_reference_square
#print axioms RelationalPerimeter.Relativity.Production.shared_request_reference_square
#print axioms RelationalPerimeter.Relativity.Production.shared_run_reference_square
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension
#print axioms RelationalPerimeter.Relativity.Production.runDescriptionExtension
#print axioms RelationalPerimeter.Relativity.Production.description_extension_is_shared_run
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension.first
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension.second
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension.site
#print axioms RelationalPerimeter.Relativity.Production.attached_prolong_reading_reference
#print axioms RelationalPerimeter.Relativity.Production.attached_prolong_signal_reference
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension.rich
#print axioms RelationalPerimeter.Relativity.Production.continued_rich_raccord_is_produced
#print axioms RelationalPerimeter.Relativity.Production.continued_observation_square
#print axioms RelationalPerimeter.Relativity.Production.continued_refinement_square
#print axioms RelationalPerimeter.Relativity.Production.continued_production_counts
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension.resume
#print axioms RelationalPerimeter.Relativity.Production.appendRecurringReport
#print axioms RelationalPerimeter.Relativity.Production.SharedDescriptionExtension.append
#print axioms RelationalPerimeter.Relativity.Production.description_extension_reports_exact
#print axioms RelationalPerimeter.Relativity.Production.description_extension_history_lengths
#print axioms RelationalPerimeter.Relativity.Production.description_extension_request_length
#print axioms RelationalPerimeter.Relativity.Production.description_extension_resume_exact
#print axioms RelationalPerimeter.Relativity.Production.appended_description_reference
#print axioms RelationalPerimeter.Relativity.Production.recurring_contract_report_append
#print axioms RelationalPerimeter.Relativity.Production.appended_description_source_report_exact
#print axioms RelationalPerimeter.Relativity.Production.appended_description_target_report_exact
#print axioms RelationalPerimeter.Relativity.Production.continued_site_cannot_erase_different_effects
/- AXIOM_AUDIT_END -/
