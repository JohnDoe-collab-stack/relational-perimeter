import RelationalPerimeter

/-! Public-client checks of positive encounter precision and reading coverage.
The closed used-passage example also checks that this basis is not silently
promoted to a recognizer of encounter occurrences or physical points. -/
set_option genInjectivity false
namespace Tests.Relativity.EncounterPrecisionChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Continuation.Encounter
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

def first := localizeParticipant Example.produced .left
def second := localizeParticipant Example.produced .right
def neighborhood := first.readoutNeighborhood Precision.unit
def original := first.realizeReadoutNeighborhood Precision.unit
def requests : List Precision := [Precision.unit, Precision.unit.half, Precision.unit.half.half]
def descriptions := runEncounterPrecisions neighborhood.windows original requests

theorem all_requested_bounds : ∀ precision, precision ∈ requests →
    ReadingSpansBounded precision (locationClauses descriptions.windows) :=
  encounter_precision_run_bounds neighborhood.windows original requests

theorem exact_return : descriptions.readings.restrict descriptions.refinement = original :=
  encounter_precision_run_returns ..

theorem shared_resumption (initial later : List Precision) :
    (runEncounterPrecisions neighborhood.windows original initial).resume later =
      runEncounterPrecisions neighborhood.windows original (initial ++ later) := encounter_precision_run_append ..

theorem transported_precision (precision : Precision) :
    Example.agreement.transportPrecision (refineEncounterPrecision neighborhood.windows original precision) =
      refineEncounterPrecision neighborhood.windows
        (Example.agreement.transportConstraints neighborhood.windows original) precision :=
  location_precision_transport_square ..

theorem transported_whole_course (requests : List Precision) :
    Example.agreement.transportPrecision (runEncounterPrecisions neighborhood.windows original requests) =
      runEncounterPrecisions neighborhood.windows
        (Example.agreement.transportConstraints neighborhood.windows original) requests :=
  location_precision_run_transport_square ..

theorem all_certified_values_are_the_original_readings : descriptions.readings.values = original.values :=
  encounter_precision_run_keeps_values ..

def otherCourse := runEncounterPrecisions neighborhood.windows original [Precision.unit.half]
def common := commonEncounterPrecisions descriptions otherCourse

theorem compatible_courses_return_both_certificates :
    common.readings.restrict common.alignment.left = descriptions.readings ∧
      common.readings.restrict common.alignment.right = otherCourse.readings := common_encounter_precisions_return_both ..

def secondMembership := Example.agreement.transportNeighborhood neighborhood original
def intersected := meetEncounterReadouts neighborhood neighborhood original original
def cover := InstrumentalConstraintCover.identity (locationClauses neighborhood.windows)
def selected := selectEncounterReadoutCover neighborhood cover original

theorem realized_finite_meet :
    ReadingConstraintsSatisfied first.attachment (locationClauses (neighborhood.meet neighborhood).windows) :=
  intersected.satisfied

theorem cover_returns_same_positive_certificate : selected.restrict = original := encountered_cover_returns_realization ..

theorem local_agreement_does_not_erase_rich_effects : AttachedEffects first ≠ AttachedEffects second :=
  Example.different_effects

def payload : Ref Example.produced.next.cursor.kinds .payload :=
  .prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior .here)))))))))
def link := produceLinkedEncounter Example.produced payload

theorem closed_passage_boundary :
    (∀ neighborhood : EncounterReadoutNeighborhood,
      neighborhood.admitted (localizeParticipant link.production .left) = neighborhood.admitted (priorEncounterLeft link)) ∧
      (localizeParticipant link.production .left).location ≠ (priorEncounterLeft link).location :=
  passage_readouts_do_not_determine_occurrence link (by rfl)

/-- Same local law, genuinely different produced interaction reading. -/
def relayed := performSignal Example.produced.next
  (.relay (.prior Example.admission.pair.secondSignal) Example.produced.next.formation.instrument)
def deliveredLeft := performDelivery relayed.next .left
  (.prior (.prior Example.admission.pair.firstSignal)) (.empty .left)
def deliveredRight := performDelivery deliveredLeft.next .right (.prior .here) .right
def differentAdmission : EncounterAdmission deliveredRight.next :=
  ⟨rightPair (Held.received deliveredLeft.head) deliveredRight.head, rfl⟩
def differentEncounter := performEncounter deliveredRight.next differentAdmission
def different := localizeParticipant differentEncounter .left

theorem different_produced_reading : first.reading ≠ different.reading := by decide
def separation := separateEncounterReadouts first different different_produced_reading

theorem separating_reader_is_actually_admitted_and_refused :
    numericWindowAdmitted first.attachment .interaction separation.window = true ∧
      numericWindowAdmitted different.attachment .interaction separation.window = false := numeric_separator_admissions separation

theorem distinct_readouts_have_different_neighborhoods :
    ¬ (∀ neighborhood : EncounterReadoutNeighborhood, neighborhood.admitted first = neighborhood.admitted different) :=
  fun agree => different_produced_reading ((encounter_readout_neighborhoods_determine_reading first different).mp agree)

#guard descriptions.windows.length == 1
#guard neighborhood.admitted first == true
#guard numericWindowAdmitted first.attachment .interaction separation.window == true
#guard numericWindowAdmitted different.attachment .interaction separation.window == false

end Tests.Relativity.EncounterPrecisionChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.EncounterPrecisionChecks.descriptions
#print axioms Tests.Relativity.EncounterPrecisionChecks.all_requested_bounds
#print axioms Tests.Relativity.EncounterPrecisionChecks.exact_return
#print axioms Tests.Relativity.EncounterPrecisionChecks.shared_resumption
#print axioms Tests.Relativity.EncounterPrecisionChecks.transported_precision
#print axioms Tests.Relativity.EncounterPrecisionChecks.transported_whole_course
#print axioms Tests.Relativity.EncounterPrecisionChecks.all_certified_values_are_the_original_readings
#print axioms Tests.Relativity.EncounterPrecisionChecks.compatible_courses_return_both_certificates
#print axioms Tests.Relativity.EncounterPrecisionChecks.realized_finite_meet
#print axioms Tests.Relativity.EncounterPrecisionChecks.cover_returns_same_positive_certificate
#print axioms Tests.Relativity.EncounterPrecisionChecks.local_agreement_does_not_erase_rich_effects
#print axioms Tests.Relativity.EncounterPrecisionChecks.closed_passage_boundary
#print axioms Tests.Relativity.EncounterPrecisionChecks.differentEncounter
#print axioms Tests.Relativity.EncounterPrecisionChecks.different_produced_reading
#print axioms Tests.Relativity.EncounterPrecisionChecks.separation
#print axioms Tests.Relativity.EncounterPrecisionChecks.separating_reader_is_actually_admitted_and_refused
#print axioms Tests.Relativity.EncounterPrecisionChecks.distinct_readouts_have_different_neighborhoods
/- AXIOM_AUDIT_END -/
