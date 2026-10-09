import RelationalPerimeter

/-! Public clients of the finite assembly law. Two attachments sharing a
calibration have independent present ports. This is not evidence that they
are separated in space. The master computation is not replaced by this test. -/
set_option genInjectivity false
namespace Tests.Relativity.CouplingNetworkChecks
open ConstitutiveSearch.Resources
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Reconstruction

def firstCell : Fin 2 := ⟨0, by decide⟩
def secondCell : Fin 2 := ⟨1, by decide⟩
theorem cells_different : secondCell ≠ firstCell := by decide

def received := Cursor.received ⟨Rational.zero, 7, Calibration.unit⟩
def initial := Network.attach received (count := 2) (fun _ => .prior (.prior .here))
def emitted := Network.performSignal initial (.emit .here (.prior .here))
def filled := Network.performFill emitted.next firstCell (Network.freshSignal emitted) rfl
def produced := Network.performEncounter filled.second.next firstCell filled.admitted

theorem other_remains_empty : filled.second.next.cells.phase secondCell = .empty :=
  Network.delivery_keeps_other_empty filled.second cells_different
    (Network.delivery_keeps_other_empty filled.first cells_different rfl)

def bothFilled := Network.performFill filled.second.next secondCell
  (Network.carriedSignal filled.second (Network.carriedSignal filled.first (Network.freshSignal emitted)))
  other_remains_empty

def firstStillAdmitted : Network.Admission bothFilled.second.next firstCell :=
  Network.Admission.afterOtherDelivery bothFilled.second (fun same => cells_different same.symm)
    (Network.Admission.afterOtherDelivery bothFilled.first (fun same => cells_different same.symm) filled.admitted)

def consumedFirst := Network.performEncounter bothFilled.second.next firstCell firstStillAdmitted
def secondStillAdmitted := Network.Admission.afterOtherEncounter consumedFirst cells_different bothFilled.admitted
def consumedSecond := Network.performEncounter consumedFirst.next secondCell secondStillAdmitted

theorem selected_is_consumed : Network.enabled consumedFirst.next firstCell = false :=
  Network.consumed_refuses consumedFirst
theorem other_admission_survives : Network.enabled consumedFirst.next secondCell = true :=
  Network.admission_enabled secondStillAdmitted
theorem second_is_consumed : Network.enabled consumedSecond.next secondCell = false :=
  Network.consumed_refuses consumedSecond

theorem produced_empty_cells : ∀ cell, produced.next.cells.phase cell = .empty := by
  intro cell
  cases decEq cell firstCell with
  | isTrue same => cases same; exact Network.consumed_selected produced
  | isFalse different =>
    exact Network.encounter_keeps_other_empty produced different
      (Network.delivery_keeps_other_empty filled.second different
        (Network.delivery_keeps_other_empty filled.first different rfl))

def payload : Ref produced.next.cursor.kinds .payload := .prior (.prior (.prior (.prior (.prior .here))))
def passage := Network.producePassageHeads produced secondCell payload (produced_empty_cells secondCell)
def course := Network.startCourse produced payload produced_empty_cells
def threePassages := course.extend [secondCell, firstCell, secondCell]

def actualUsedPath := passage.used
def localAgreement := networkEncounterAgreement passage.produced .root
def priorDescription := networkFirst produced passage.history

theorem separate_sources : (networkFirst passage.produced .root).readingReference ≠
    (networkSecond passage.produced .root).readingReference := network_participants_stay_distinct _ _
theorem different_occurrences : (networkFirst passage.produced .root).anchor ≠ priorDescription.anchor :=
  network_passage_keeps_distinct_anchors passage
theorem keeps_effects :
    (networkFirst produced passage.history).effects = filled.second.next.cursor.read filled.admitted.pair.firstSignal ∧
      (networkSecond produced passage.history).effects = filled.second.next.cursor.read filled.admitted.pair.secondSignal :=
  network_keeps_both_effects produced passage.history
theorem repeated_actual_production : threePassages.links = 3 := by
  exact Network.course_requested_length course [secondCell, firstCell, secondCell]
theorem resume_without_replay (one two : List (Fin 2)) :
    course.extend (one ++ two) = (course.extend one).extend two := Network.course_resume_exact course one two

theorem real_head_horizon_independence :
    (Network.runContinuedPassage produced secondCell payload (produced_empty_cells secondCell) .emitOutput).heads =
      (Network.runContinuedPassage produced secondCell payload (produced_empty_cells secondCell) .receiveFirstRecord).heads :=
  Network.passage_head_independent _ _ _ _ .emitOutput .receiveFirstRecord

def copiedRecord : SignalRecord := passage.produced.head.successor.read
  (networkFirst passage.produced .root).signalReference
def sourceReading : Rational := produced.head.successor.read (comparisonAnchor produced.head)
theorem passage_copies_actual_source : copiedRecord.reading = sourceReading :=
  (congrArg SignalRecord.reading (network_passage_first_record_exact passage)).trans
    (comparison_anchor_output produced.head).symm

#guard Network.enabled initial firstCell == false
#guard Network.enabled initial secondCell == false
#guard Network.enabled consumedFirst.next firstCell == false
#guard Network.enabled consumedFirst.next secondCell == true
#guard Network.enabled consumedSecond.next secondCell == false
#guard threePassages.links == 3

end Tests.Relativity.CouplingNetworkChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.CouplingNetworkChecks.cells_different
#print axioms Tests.Relativity.CouplingNetworkChecks.other_remains_empty
#print axioms Tests.Relativity.CouplingNetworkChecks.firstStillAdmitted
#print axioms Tests.Relativity.CouplingNetworkChecks.secondStillAdmitted
#print axioms Tests.Relativity.CouplingNetworkChecks.selected_is_consumed
#print axioms Tests.Relativity.CouplingNetworkChecks.other_admission_survives
#print axioms Tests.Relativity.CouplingNetworkChecks.second_is_consumed
#print axioms Tests.Relativity.CouplingNetworkChecks.produced_empty_cells
#print axioms Tests.Relativity.CouplingNetworkChecks.actualUsedPath
#print axioms Tests.Relativity.CouplingNetworkChecks.localAgreement
#print axioms Tests.Relativity.CouplingNetworkChecks.separate_sources
#print axioms Tests.Relativity.CouplingNetworkChecks.different_occurrences
#print axioms Tests.Relativity.CouplingNetworkChecks.keeps_effects
#print axioms Tests.Relativity.CouplingNetworkChecks.repeated_actual_production
#print axioms Tests.Relativity.CouplingNetworkChecks.resume_without_replay
#print axioms Tests.Relativity.CouplingNetworkChecks.real_head_horizon_independence
#print axioms Tests.Relativity.CouplingNetworkChecks.passage_copies_actual_source
/- AXIOM_AUDIT_END -/
