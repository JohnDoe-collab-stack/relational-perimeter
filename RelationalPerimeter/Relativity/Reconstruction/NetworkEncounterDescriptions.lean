import RelationalPerimeter.Relativity.Production.NetworkEncounterPassages
import RelationalPerimeter.Relativity.Reconstruction.EncounterReadingConstraints

/-!
# Local descriptions consuming actual network couplings

The agreement concerns the participants of one admitted stored interaction.
Its rich effects and its transported old occurrence remain readable. A used
passage to another coupling does not supply an agreement of its endpoints.
This module supplies neither continuous physical points nor their coverage.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production

def networkFirst {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted)
    {target} (history : Network.History production.next target) :=
  InteractionAttachment.first production.head (DescriptionPath.root.prolong history.resources)

def networkSecond {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted)
    {target} (history : Network.History production.next target) :=
  InteractionAttachment.second production.head (DescriptionPath.root.prolong history.resources)

def networkEncounterAgreement {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted)
    {target} (history : Network.History production.next target) :
    InteractionSiteAgreement (networkFirst production history) (networkSecond production history) :=
  .participants production.head (DescriptionPath.root.prolong history.resources)

theorem network_participants_stay_distinct {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted)
    {target} (history : Network.History production.next target) :
    (networkFirst production history).readingReference ≠ (networkSecond production history).readingReference :=
  participants_remain_distinct production.head (DescriptionPath.root.prolong history.resources)

theorem network_keeps_both_effects {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted)
    {target} (history : Network.History production.next target) :
    (networkFirst production history).effects = source.cursor.read admitted.pair.firstSignal ∧
      (networkSecond production history).effects = source.cursor.read admitted.pair.secondSignal :=
  ⟨attached_effects_exact _, attached_effects_exact _⟩

def networkAnchorConstraints {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted) {target}
    (history : Network.History production.next target) :
    (windows : List ReadingWindow) →
    CertifiedReadingConstraints (networkFirst production history) (locationClauses windows) →
    CertifiedReadingConstraints (networkSecond production history) (locationClauses windows)
  | [], .nil => .nil
  | _ :: rest, .cons reading tail =>
    .cons ⟨reading.value,
      reading.valueExact.trans (site_agreement_anchor_reading (networkEncounterAgreement production history)).symm,
      reading.inside⟩ (networkAnchorConstraints production history rest tail)

theorem network_anchor_constraints_keep_values {count source cell admitted}
    (production : @Network.EncounterProduction count source cell admitted) {target}
    (history : Network.History production.next target) (windows : List ReadingWindow)
    (readings : CertifiedReadingConstraints (networkFirst production history) (locationClauses windows)) :
    (networkAnchorConstraints production history windows readings).values = readings.values := by
  induction windows with
  | nil => cases readings; rfl
  | cons window rest ih => cases readings with
    | cons reading tail => exact congrArg (List.cons reading.value) (ih tail)

theorem network_passage_keeps_distinct_anchors {count source cell admitted origin destination payload empty}
    (heads : @Network.PassageHeads count source cell admitted origin destination payload empty) :
    (networkFirst heads.produced .root).anchor ≠ (networkFirst origin heads.history).anchor :=
  Network.passage_keeps_distinct_occurrences heads

theorem network_passage_first_record_exact {count source cell admitted origin destination payload empty}
    (heads : @Network.PassageHeads count source cell admitted origin destination payload empty) :
    (networkFirst heads.produced .root).effects =
      SignalRecord.emit origin.head.determination.1 (origin.next.cursor.read payload) := by
  have signalExact := Network.right_pair_signal_is_carried (Encounter.Held.received heads.filled.first.head)
    heads.filled.second.head
  have firstRead := (recurringHistoryTransport (recurringProductionHistory heads.filled.first.head)).reads
    (Network.freshSignal heads.emitted)
  have receivedSignal := Network.held_received_signal_is_carried heads.filled.first.head
  have firstRecord := (congrArg heads.filled.first.next.cursor.read receivedSignal).trans firstRead
  have secondRead := (recurringHistoryTransport (recurringProductionHistory heads.filled.second.head)).reads
    (Encounter.Held.received heads.filled.first.head).signal
  have emission := Network.emission_record_exact heads.emitted
  have output := emission.trans (congrArg (fun reading => SignalRecord.emit reading (origin.next.cursor.read payload))
    (comparison_anchor_output origin.head))
  exact (attached_effects_exact (networkFirst heads.produced .root)).trans
    ((congrArg heads.filled.second.next.cursor.read signalExact).trans
      (secondRead.trans (firstRecord.trans output)))

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.networkFirst
#print axioms RelationalPerimeter.Relativity.Reconstruction.networkSecond
#print axioms RelationalPerimeter.Relativity.Reconstruction.networkEncounterAgreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.network_participants_stay_distinct
#print axioms RelationalPerimeter.Relativity.Reconstruction.network_keeps_both_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.networkAnchorConstraints
#print axioms RelationalPerimeter.Relativity.Reconstruction.network_anchor_constraints_keep_values
#print axioms RelationalPerimeter.Relativity.Reconstruction.network_passage_keeps_distinct_anchors
#print axioms RelationalPerimeter.Relativity.Reconstruction.network_passage_first_record_exact
/- AXIOM_AUDIT_END -/
