import RelationalPerimeter

/-! Closed agreements after an actually discovered exchange and a cached
comparison. Interaction agreement is not rich agreement or physical colocation. -/
set_option genInjectivity false
namespace Tests.Relativity.InteractionDescriptionAgreementChecks
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

def firstInstruction : Instruction arrivals.1.kinds .reading := .receive arrivals.2.firstSignal
def secondInstruction : Instruction (.reading :: arrivals.1.kinds) .reading := .receive (.prior arrivals.2.secondSignal)
def actual := produceStoredPair arrivals.1 firstInstruction secondInstruction

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
def rich := AttachedDescriptionAgreement.reexpression one changed
def sharedSite := InteractionSiteAgreement.participants head DescriptionPath.root

theorem head_output_is_shared : transportedHead.determination.1 = head.determination.1 := rfl

theorem transported_head_matches_reference : transportedHead = performRecurring
    (.fromCursor found.exchanged.cursor) (.compare (pair.rename found.raccord.constitution)) :=
  transported_production_exact found.raccord.constitution head

theorem actual_reference_is_transported :
    one.readingReference.position = 2 ∧ renamed.readingReference.position = 1 := ⟨rfl, rfl⟩

def renamedReception := renamed.transportedArrival
def renamedUsedPort := renamed.usedPort

theorem cached_interaction_is_preserved :
    changed.constitution.references.forward one.anchor = renamed.anchor := rich.anchorExact

theorem rich_effects_are_preserved : renamed.effects = one.effects := attached_agreement_effects rich

theorem actual_records_differ : one.effects ≠ two.effects := by
  intro same
  have lengths := congrArg (fun record : SignalRecord => record.increments.length) same
  change 2 = 0 at lengths
  cases lengths

theorem interaction_agrees_without_identifying_sources :
    one.anchor = two.anchor ∧ one.readingReference ≠ two.readingReference :=
  ⟨sharedSite.anchorExact, participants_remain_distinct head .root⟩

theorem site_agreement_is_not_rich_agreement
    (agreement : AttachedDescriptionAgreement one two) : False :=
  differing_effects_refute_rich_agreement one two actual_records_differ agreement

def simpleReaders : SignalReaders := ⟨true, true, false⟩
def pathReaders : SignalReaders := ⟨false, false, true⟩

theorem complementary_readers_are_full : simpleReaders.join pathReaders = SignalReaders.full := rfl

theorem limited_observations_agree : one.observe simpleReaders = two.observe simpleReaders := rfl

theorem full_observations_still_differ : one.observe .full ≠ two.observe .full :=
  fun same => actual_records_differ ((attached_joint_observations_exact one two).mp same)

theorem rich_agreement_preserves_every_reader (readers : SignalReaders) :
    renamed.observe readers = one.observe readers := attached_agreement_observations rich readers

theorem common_refinement_keeps_both_readings :
    (renamed.observe (simpleReaders.join pathReaders)).restrict simpleReaders = renamed.observe simpleReaders ∧
      (renamed.observe (simpleReaders.join pathReaders)).restrict pathReaders = renamed.observe pathReaders :=
  attached_observation_common_refinement renamed simpleReaders pathReaders

def returnAgreement := rich.compose rich.reverse
def threeChanges := (rich.compose rich.reverse).compose rich

theorem reverse_returns_every_occurrence {kind} (ref : Ref head.successor.kinds kind) :
    returnAgreement.raccord.constitution.references.forward ref = ref := attached_rich_return_reference rich ref

theorem composition_has_the_actual_signal :
    threeChanges.raccord.constitution.references.forward one.signalReference = renamed.signalReference :=
  threeChanges.signalExact

theorem composition_is_associative_on_occurrences {kind} (ref : Ref head.successor.kinds kind) :
    ((rich.raccord.compose rich.reverse.raccord).compose rich.raccord).constitution.references.forward ref =
      (rich.raccord.compose (rich.reverse.raccord.compose rich.raccord)).constitution.references.forward ref :=
  addressed_composition_associates rich.raccord rich.reverse.raccord rich.raccord ref

theorem future_inspections_still_reveal_the_paths :
    (runRecurringRequests head.successor [.local (.inspect .signal one.signalReference.position)]).report ≠
      (runRecurringRequests head.successor [.local (.inspect .signal two.signalReference.position)]).report := by
  rw [recurring_all_futures_exact, recurring_all_futures_exact]
  exact attached_effects_separate_inspections one two actual_records_differ

def suffix (requests : List RecurringRequest) := runRecurringRequests transportedHead.successor requests
def extended (requests : List RecurringRequest) := renamed.prolong (suffix requests).history

theorem every_suffix_still_matches_the_contract (requests : List RecurringRequest) :
    (suffix requests).report = recurringContract.outcome transportedHead.successor requests :=
  recurring_all_futures_exact ..

theorem rich_agreement_preserves_all_translated_futures (requests : List RecurringRequest) :
    recurringContract.outcome transportedHead.successor (runSharedRecurring rich.raccord requests).translated =
      recurringContract.outcome head.successor requests := attached_agreement_all_futures rich requests

theorem every_suffix_retains_the_original_effects (requests : List RecurringRequest) :
    (extended requests).effects = one.effects :=
  (attached_prolong_effects renamed _).trans rich_effects_are_preserved

theorem refine_then_continue_or_continue_then_refine (requests : List RecurringRequest) :
    ((extended requests).observe .full).restrict simpleReaders = one.observe simpleReaders :=
  (attached_observation_restrict (extended requests) ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩).trans
    ((attached_observation_prolong renamed _ simpleReaders).trans
      (attached_agreement_observations rich simpleReaders))

/-- Two receptions of the exact same signal still constitute different
participants, even when all record readers agree. -/
def equalActual := produceStoredPair arrivals.1 firstInstruction
  (Instruction.receive (Ref.prior arrivals.2.firstSignal))

def equalOrigin : RecurringCursor := .fromCursor equalActual.cursor

def equalPair : RecurringPair equalOrigin :=
  ⟨.prior .here, .here, .prior (.prior arrivals.2.firstSignal), .prior (.prior arrivals.2.firstSignal),
    .fromCursor (.inherited equalActual.secondDetermination.2
      (Arrived.ofReception arrivals.1.formation equalActual.firstDetermination.2)),
    .fromCursor (Arrived.ofReception (arrivals.1.extend equalActual.firstDetermination).formation
      equalActual.secondDetermination.2), fun same =>
        fresh_distinct (arrivals.1.extend equalActual.firstDetermination)
          equalActual.secondDetermination .here same.symm⟩

def equalHead := performRecurring equalOrigin (.compare equalPair)
def equalOne := InteractionAttachment.first equalHead .root
def equalTwo := InteractionAttachment.second equalHead .root

theorem equal_records_do_not_identify_receptions :
    equalOne.observe .full = equalTwo.observe .full ∧ equalOne.readingReference ≠ equalTwo.readingReference :=
  ⟨rfl, participants_remain_distinct equalHead .root⟩

theorem equal_records_cannot_supply_identity_rich_agreement
    (agreement : AttachedDescriptionAgreement equalOne equalTwo)
    (unchanged : agreement.raccord = AddressedRecurringRaccord.identity equalHead.successor) : False := by
  have reading := agreement.readingExact
  rw [unchanged] at reading
  exact equal_records_do_not_identify_receptions.2 reading

end Tests.Relativity.InteractionDescriptionAgreementChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.arrivals
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.actual
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.exchange_really_found
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.found
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.pair
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.head
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.transportedHead
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.changed
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.rich
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.sharedSite
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.head_output_is_shared
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.transported_head_matches_reference
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.actual_reference_is_transported
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.renamedReception
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.renamedUsedPort
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.cached_interaction_is_preserved
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.rich_effects_are_preserved
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.actual_records_differ
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.interaction_agrees_without_identifying_sources
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.site_agreement_is_not_rich_agreement
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.complementary_readers_are_full
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.limited_observations_agree
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.full_observations_still_differ
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.rich_agreement_preserves_every_reader
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.common_refinement_keeps_both_readings
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.returnAgreement
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.threeChanges
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.reverse_returns_every_occurrence
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.composition_has_the_actual_signal
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.composition_is_associative_on_occurrences
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.future_inspections_still_reveal_the_paths
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.every_suffix_still_matches_the_contract
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.rich_agreement_preserves_all_translated_futures
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.every_suffix_retains_the_original_effects
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.refine_then_continue_or_continue_then_refine
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.equalActual
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.equalPair
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.equalHead
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.equal_records_do_not_identify_receptions
#print axioms Tests.Relativity.InteractionDescriptionAgreementChecks.equal_records_cannot_supply_identity_rich_agreement
/- AXIOM_AUDIT_END -/
