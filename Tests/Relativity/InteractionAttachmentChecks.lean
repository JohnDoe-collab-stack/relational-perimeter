import RelationalPerimeter

/-! A closed client on the same instrumental family. Joint participation is
not a physical meeting assertion. The two path records remain exposed by the
unchanged recurring contract even when their readings and interaction agree. -/
set_option genInjectivity false
namespace Tests.Relativity.InteractionAttachmentChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def arrivals : (source : Cursor) ×' ArrivalPair source :=
  let emitted := perform (.received input) emission
  let once := perform emitted.successor (.relay .here (.prior (.prior (.prior .here))))
  let twice := perform once.successor (.relay .here (.prior (.prior (.prior (.prior .here)))))
  let first := perform twice.successor (.receive .here)
  let reemitted := perform first.successor
    (.emit .here (.prior (.prior (.prior (.prior (.prior .here))))))
  let second := perform reemitted.successor (.receive .here)
  let earlier := Arrived.inherited second.determination.2
    (Arrived.inherited reemitted.determination.2 (arrivalOfProduction first))
  ⟨second.successor, ⟨.prior (.prior .here), .here, .prior (.prior (.prior .here)), .prior .here,
    earlier, arrivalOfProduction second, fun same =>
      fresh_distinct reemitted.successor second.determination (.prior .here) same.symm⟩⟩

def source := RecurringCursor.fromCursor arrivals.1

def pair : RecurringPair source :=
  ⟨arrivals.2.first, arrivals.2.second, arrivals.2.firstSignal, arrivals.2.secondSignal,
    .fromCursor arrivals.2.firstArrival, .fromCursor arrivals.2.secondArrival, arrivals.2.distinct⟩

def interaction := runAttachedComparison source pair []
def first := interaction.first
def second := interaction.second

theorem same_payload : first.effects.payload = second.effects.payload := rfl
theorem same_reading : first.effects.reading = second.effects.reading := rfl
theorem first_path_retained : first.effects.increments = [Rational.one, Rational.one] := rfl
theorem second_path_retained : second.effects.increments = [] := rfl

theorem actual_paths_differ : first.effects ≠ second.effects := by
  intro same
  have lengths := congrArg (fun record : SignalRecord => record.increments.length) same
  change 2 = 0 at lengths
  cases lengths

theorem interaction_output_zero : interaction.head.determination.1 = Rational.zero := by
  change Rational.sub pair.secondArrival.measure pair.firstArrival.measure = _
  change Rational.sub pair.firstArrival.measure pair.firstArrival.measure = _
  exact Rational.sub_self _

theorem comparison_request_is_really_admitted :
    recurringEnabled source (.compare pair.first.position pair.second.position) = true :=
  recurring_pair_request_enabled pair

theorem shared_interaction : first.anchor = second.anchor := participants_share_anchor _ _
theorem received_sources_distinct : first.readingReference ≠ second.readingReference :=
  participants_remain_distinct _ _

theorem actual_signal_sources_distinct : pair.firstSignal ≠ pair.secondSignal := by
  intro same
  have positions := congrArg Ref.position same
  change 3 = 1 at positions
  exact Nat.noConfusion (Nat.succ.inj positions)

theorem attached_signal_sources_distinct : first.signalReference ≠ second.signalReference :=
  attached_signal_distinction _ _ actual_signal_sources_distinct

theorem new_interaction_is_not_a_received_source : first.anchor ≠ first.readingReference :=
  attached_anchor_not_arrival _

def firstReception := first.transportedArrival
def secondReception := second.transportedArrival
def firstPortUsed := first.usedPort
def secondPortUsed := second.usedPort

theorem anchor_is_not_a_reception {signal : Ref interaction.continuation.cursor.kinds .signal}
    (arrival : RecurringArrival interaction.continuation.cursor.formation first.anchor signal) : False :=
  recurring_comparison_not_reception source pair arrival

theorem permitted_inspections_reveal_the_paths :
    (runRecurringRequests interaction.continuation.cursor
      [.local (.inspect .signal first.signalReference.position)]).report ≠
    (runRecurringRequests interaction.continuation.cursor
      [.local (.inspect .signal second.signalReference.position)]).report := by
  rw [recurring_all_futures_exact, recurring_all_futures_exact]
  exact attached_effects_separate_inspections first second actual_paths_differ

def continued (requests : List RecurringRequest) := runAttachedComparison source pair requests

theorem all_suffixes_have_the_same_head (requests : List RecurringRequest) :
    (continued requests).head = interaction.head := attached_head_independent source pair requests []

theorem every_suffix_matches_the_existing_contract (requests : List RecurringRequest) :
    (continued requests).continuation.report = recurringContract.outcome interaction.head.successor requests :=
  attached_continuation_exact source pair requests

theorem every_suffix_keeps_the_first_record (requests : List RecurringRequest) :
    (continued requests).first.effects = first.effects :=
  (attached_effects_exact _).trans (attached_effects_exact first).symm

theorem every_suffix_keeps_the_second_record (requests : List RecurringRequest) :
    (continued requests).second.effects = second.effects :=
  (attached_effects_exact _).trans (attached_effects_exact second).symm

theorem every_suffix_keeps_joint_participation (requests : List RecurringRequest) :
    (continued requests).first.anchor = (continued requests).second.anchor := participants_share_anchor _ _

theorem every_suffix_keeps_distinct_receptions (requests : List RecurringRequest) :
    (continued requests).first.readingReference ≠ (continued requests).second.readingReference :=
  participants_remain_distinct _ _

def continuedFirstPort (requests : List RecurringRequest) := (continued requests).first.usedPort
def continuedSecondArrival (requests : List RecurringRequest) := (continued requests).second.transportedArrival

def repeatedPair := pair.transport (recurringProductionHistory interaction.head)
def repeated := performRecurring interaction.head.successor (.compare repeatedPair)
def oldAnchor := (comparisonExtension repeated).references (comparisonAnchor interaction.head)

theorem repeated_output_is_equal : repeated.determination.1 = interaction.head.determination.1 := by
  have firstMeasure := recurring_history_arrival_measure (recurringProductionHistory interaction.head) pair.firstArrival
  have secondMeasure := recurring_history_arrival_measure (recurringProductionHistory interaction.head) pair.secondArrival
  exact (comparison_output_uses_arrivals repeated).trans
    ((congrArg (fun reading => Rational.sub reading repeatedPair.firstArrival.measure) secondMeasure).trans
      ((congrArg (Rational.sub pair.secondArrival.measure) firstMeasure).trans
        (comparison_output_uses_arrivals interaction.head).symm))

theorem equal_results_are_different_interactions :
    repeated.successor.read (comparisonAnchor repeated) = repeated.successor.read oldAnchor ∧
      comparisonAnchor repeated ≠ oldAnchor := by
  constructor
  · exact (comparison_anchor_output repeated).trans (repeated_output_is_equal.trans
      (((comparisonExtension repeated).reads (comparisonAnchor interaction.head)).trans
        (comparison_anchor_output interaction.head)).symm)
  · exact comparison_anchor_fresh repeated _

def oldDescription := InteractionAttachment.first interaction.head
  (DescriptionPath.root.prolong (recurringProductionHistory repeated))

theorem old_interaction_reference_is_preserved : oldDescription.anchor = oldAnchor :=
  attached_prolong_anchor (InteractionAttachment.first interaction.head .root) _

theorem presentation_return_keeps_the_anchor {target : RecurringCursor}
    (raccord : AddressedRecurringRaccord interaction.continuation.cursor target) :
    ((first.reexpress raccord).reexpress raccord.reverse).anchor = first.anchor :=
  attached_reexpress_return_anchor first raccord

end Tests.Relativity.InteractionAttachmentChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.InteractionAttachmentChecks.arrivals
#print axioms Tests.Relativity.InteractionAttachmentChecks.pair
#print axioms Tests.Relativity.InteractionAttachmentChecks.interaction
#print axioms Tests.Relativity.InteractionAttachmentChecks.same_payload
#print axioms Tests.Relativity.InteractionAttachmentChecks.same_reading
#print axioms Tests.Relativity.InteractionAttachmentChecks.first_path_retained
#print axioms Tests.Relativity.InteractionAttachmentChecks.second_path_retained
#print axioms Tests.Relativity.InteractionAttachmentChecks.actual_paths_differ
#print axioms Tests.Relativity.InteractionAttachmentChecks.interaction_output_zero
#print axioms Tests.Relativity.InteractionAttachmentChecks.comparison_request_is_really_admitted
#print axioms Tests.Relativity.InteractionAttachmentChecks.shared_interaction
#print axioms Tests.Relativity.InteractionAttachmentChecks.received_sources_distinct
#print axioms Tests.Relativity.InteractionAttachmentChecks.actual_signal_sources_distinct
#print axioms Tests.Relativity.InteractionAttachmentChecks.attached_signal_sources_distinct
#print axioms Tests.Relativity.InteractionAttachmentChecks.new_interaction_is_not_a_received_source
#print axioms Tests.Relativity.InteractionAttachmentChecks.firstReception
#print axioms Tests.Relativity.InteractionAttachmentChecks.secondReception
#print axioms Tests.Relativity.InteractionAttachmentChecks.firstPortUsed
#print axioms Tests.Relativity.InteractionAttachmentChecks.secondPortUsed
#print axioms Tests.Relativity.InteractionAttachmentChecks.anchor_is_not_a_reception
#print axioms Tests.Relativity.InteractionAttachmentChecks.permitted_inspections_reveal_the_paths
#print axioms Tests.Relativity.InteractionAttachmentChecks.all_suffixes_have_the_same_head
#print axioms Tests.Relativity.InteractionAttachmentChecks.every_suffix_matches_the_existing_contract
#print axioms Tests.Relativity.InteractionAttachmentChecks.every_suffix_keeps_the_first_record
#print axioms Tests.Relativity.InteractionAttachmentChecks.every_suffix_keeps_the_second_record
#print axioms Tests.Relativity.InteractionAttachmentChecks.every_suffix_keeps_joint_participation
#print axioms Tests.Relativity.InteractionAttachmentChecks.every_suffix_keeps_distinct_receptions
#print axioms Tests.Relativity.InteractionAttachmentChecks.continuedFirstPort
#print axioms Tests.Relativity.InteractionAttachmentChecks.continuedSecondArrival
#print axioms Tests.Relativity.InteractionAttachmentChecks.repeated_output_is_equal
#print axioms Tests.Relativity.InteractionAttachmentChecks.equal_results_are_different_interactions
#print axioms Tests.Relativity.InteractionAttachmentChecks.old_interaction_reference_is_preserved
#print axioms Tests.Relativity.InteractionAttachmentChecks.presentation_return_keeps_the_anchor
/- AXIOM_AUDIT_END -/
