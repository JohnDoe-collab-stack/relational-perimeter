import RelationalPerimeter

/-! Public client of the new declared coupling law, not another production
root. Local availability, common encounter and different path effects are
tested separately. The full future contract is not a spacetime metric. -/
set_option genInjectivity false
namespace Tests.Relativity.EncounterChecks
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Continuation.Encounter
open ConstitutiveSearch.Resources

def agreement := Example.agreement
def historicalAgreement := Example.continuedAgreement

theorem admitted : encounterEnabled Example.ready = true := Example.admission_is_real
theorem archive_is_not_available : encounterEnabled Example.initial = false := Example.no_archived_admission
theorem missing_port_is_refused : encounterEnabled Example.left.next = false := Example.one_port_refused
theorem consumed_is_not_available : encounterEnabled Example.produced.next = false := Example.consumed_refused
theorem same_reading : Example.produced.effects.1.reading = Example.produced.effects.2.reading := Example.equal_readings
theorem different_paths : Example.produced.effects.1 ≠ Example.produced.effects.2 := Example.different_effects
theorem different_sources : Example.produced.first.readingReference ≠ Example.produced.second.readingReference :=
  Example.sources_remain_distinct

theorem finite_futures_exact (requests : List Request) :
    (Example.execution requests).continuation.report = contract.outcome Example.produced.next requests :=
  encounter_continuation_exact _ _ requests

theorem future_independent_head (one two : List Request) :
    (Example.execution one).production = (Example.execution two).production := head_independent _ _ one two

theorem actual_resume (source : State) (one two : List Request) :
    (run source (one ++ two)).state = (run (run source one).state two).state := run_append_state ..

theorem future_separates_paths (requests : List Request) :
    (run (Example.execution requests).continuation.state
      [.local (.inspect .signal (Example.execution requests).first.attachment.signalReference.position)]).report ≠
    (run (Example.execution requests).continuation.state
      [.local (.inspect .signal (Example.execution requests).second.attachment.signalReference.position)]).report :=
  Example.every_suffix_reveals_the_difference requests

theorem same_request_prevents_rich_grouping (requests : List Request) :
    ¬ ConstitutiveSearch.ContinuationSignatures.FutureEquivalent (readerContract Example.produced)
      (Example.richFirst requests) (Example.richSecond requests) := Example.same_request_forbids_rich_grouping requests

theorem equal_archive_is_insufficient (attempt : EncounterAdmission Example.initial) : False :=
  Example.equal_archive_cannot_admit attempt

theorem not_one_event : commonEncounterLocation Example.again ≠
    Example.nextEncounterHistory.transport.references (commonEncounterLocation Example.produced) :=
  Example.different_encounter_occurrences

theorem exact_return {current target} {source admitted production}
    (presentation : @LocalizedPresentation source admitted production current)
    (raccord : AddressedRecurringRaccord current target) :
    ((presentation.reexpress raccord).reexpress raccord.reverse).location = presentation.location :=
  localized_return_location presentation raccord

#guard encounterEnabled Example.initial == false
#guard encounterEnabled Example.ready == true
#guard encounterEnabled Example.produced.next == false

end Tests.Relativity.EncounterChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.EncounterChecks.agreement
#print axioms Tests.Relativity.EncounterChecks.historicalAgreement
#print axioms Tests.Relativity.EncounterChecks.admitted
#print axioms Tests.Relativity.EncounterChecks.archive_is_not_available
#print axioms Tests.Relativity.EncounterChecks.missing_port_is_refused
#print axioms Tests.Relativity.EncounterChecks.consumed_is_not_available
#print axioms Tests.Relativity.EncounterChecks.same_reading
#print axioms Tests.Relativity.EncounterChecks.different_paths
#print axioms Tests.Relativity.EncounterChecks.different_sources
#print axioms Tests.Relativity.EncounterChecks.finite_futures_exact
#print axioms Tests.Relativity.EncounterChecks.future_independent_head
#print axioms Tests.Relativity.EncounterChecks.actual_resume
#print axioms Tests.Relativity.EncounterChecks.future_separates_paths
#print axioms Tests.Relativity.EncounterChecks.same_request_prevents_rich_grouping
#print axioms Tests.Relativity.EncounterChecks.equal_archive_is_insufficient
#print axioms Tests.Relativity.EncounterChecks.not_one_event
#print axioms Tests.Relativity.EncounterChecks.exact_return
/- AXIOM_AUDIT_END -/
