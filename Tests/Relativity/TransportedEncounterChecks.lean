import RelationalPerimeter

/-! Closed nonidentity client: the second description reorders cached
independent determinations, then all requests use the evolving coupling
raccord. Executability checks are smoke tests, not physical measurements. -/
set_option genInjectivity false
namespace Tests.Relativity.TransportedEncounterChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Continuation.Encounter
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def source : Cursor := emittedCursor input
def first : Instruction source.kinds .signal := .relay .here (.prior (.prior (.prior .here)))
def second : Instruction source.kinds .reading := .receive .here
def original := produceIndependentPair source first second
def reversed := original.exchangeStored
def resources := independentRecurringPair original reversed
def instrument : Ref original.cursor.kinds .calibration := .prior (.prior (.prior (.prior (.prior .here))))
def initial := StateRaccord.attached instrument resources

theorem different_presentations : initial.resources.addresses.forward 0 = 1 ∧
    initial.resources.addresses.forward 1 = 0 := ⟨rfl, rfl⟩

def requests : List Request :=
  [.deliver .left 1, .deliver .left 2, .encounter, .local (.inspect .signal 2),
    .local (.receive 2), .deliver .right 3, .encounter, .encounter,
    .local (.emit 0 8), .local (.relay 0 10), .local (.receive 0),
    .local (.inspect .signal 0), .local (.inspect .reading 0), .local (.receive 100)]

def paired := runSharedCoupling initial requests

def permissions : Outcome Event Unit → List Bool
  | .stop _ => []
  | .step _ allowed _ rest => allowed :: permissions rest

theorem admissions_and_refusals : permissions paired.first.report =
    [true, false, false, true, true, true, true, false, true, true, true, false, true, false] := rfl

theorem existing_source_runner : paired.first = run (attach original.cursor instrument) requests :=
  shared_run_source_exact initial requests

theorem existing_target_runner : paired.second = run
    (attach reversed.cursor (resources.constitution.references.forward instrument)) paired.translated :=
  shared_run_target_exact initial requests

theorem both_reports_exact : paired.second.report = paired.first.report := paired.reportExact

theorem all_finite_requests (future : List Request) :
    contract.outcome (attach reversed.cursor (resources.constitution.references.forward instrument))
      (runSharedCoupling initial future).translated =
    contract.outcome (attach original.cursor instrument) future := transported_all_futures initial future

theorem reverse_all_finite_requests (future : List Request) :
    contract.outcome (attach original.cursor instrument) (runSharedCoupling initial.reverse future).translated =
    contract.outcome (attach reversed.cursor (resources.constitution.references.forward instrument)) future :=
  transported_all_futures initial.reverse future

theorem exact_resume (future : List Request) :
    contract.outcome paired.second.state (paired.continue future).translated =
      contract.outcome paired.first.state future := continued_full_contract_exact paired future

theorem no_request_removed : paired.translated.length = requests.length := translated_length initial requests

def dynamic : List Request := [.deliver .left 1, .local (.receive 2)]
def dynamicPair := runSharedCoupling initial dynamic

theorem current_addresses_not_initial_addresses :
    dynamicPair.translated = [.deliver .left 0, .local (.receive 1)] := rfl

theorem frozen_mapping_is_not_a_contract_transport :
    contract.outcome (attach reversed.cursor (resources.constitution.references.forward instrument))
      (dynamic.map (Request.rename initial.resources.addresses.forward)) ≠
    contract.outcome (attach original.cursor instrument) dynamic := by
  intro same
  have allowed := congrArg (fun report => match report with
    | .stop _ => false
    | .step _ _ _ tail => match tail with
      | .stop _ => false
      | .step _ admitted _ _ => admitted) same
  change false = true at allowed
  cases allowed

theorem cached_exchange_outputs : reversed.firstDetermination.1 = original.secondDetermination.1 ∧
    reversed.secondDetermination.1 = original.firstDetermination.1 := exchanged_outputs_are_cached original

#guard permissions paired.first.report == permissions paired.second.report
#guard paired.translated.length == 14

end Tests.Relativity.TransportedEncounterChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.TransportedEncounterChecks.different_presentations
#print axioms Tests.Relativity.TransportedEncounterChecks.paired
#print axioms Tests.Relativity.TransportedEncounterChecks.admissions_and_refusals
#print axioms Tests.Relativity.TransportedEncounterChecks.existing_source_runner
#print axioms Tests.Relativity.TransportedEncounterChecks.existing_target_runner
#print axioms Tests.Relativity.TransportedEncounterChecks.both_reports_exact
#print axioms Tests.Relativity.TransportedEncounterChecks.all_finite_requests
#print axioms Tests.Relativity.TransportedEncounterChecks.reverse_all_finite_requests
#print axioms Tests.Relativity.TransportedEncounterChecks.exact_resume
#print axioms Tests.Relativity.TransportedEncounterChecks.no_request_removed
#print axioms Tests.Relativity.TransportedEncounterChecks.current_addresses_not_initial_addresses
#print axioms Tests.Relativity.TransportedEncounterChecks.frozen_mapping_is_not_a_contract_transport
#print axioms Tests.Relativity.TransportedEncounterChecks.cached_exchange_outputs
/- AXIOM_AUDIT_END -/
