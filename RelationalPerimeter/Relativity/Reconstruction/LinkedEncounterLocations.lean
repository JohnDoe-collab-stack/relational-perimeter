import RelationalPerimeter.Relativity.Production.EncounterPassages
import RelationalPerimeter.Relativity.Reconstruction.EncounterReadingConstraints

/-!
# Local descriptions along actual encounter passages

The prior encounter is carried through the used passage; the new encounter
has its own local agreement. Their locations are provably distinct even when
their readings agree. A used passage is not an agreement identifying its
endpoints. All rich effects of the prior participants remain accessible.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter

def priorEncounterLeft {source admitted origin} (link : @LinkedEncounter source admitted origin) :=
  (localizeParticipant origin .left).prolong link.history

def priorEncounterRight {source admitted origin} (link : @LinkedEncounter source admitted origin) :=
  (localizeParticipant origin .right).prolong link.history

def LinkedEncounter.priorAgreement {source admitted origin} (link : @LinkedEncounter source admitted origin) :
    LocationAgreement origin (priorEncounterLeft link) (priorEncounterRight link) := continuedLocationAgreement origin link.history

def LinkedEncounter.newAgreement {source admitted origin} (link : @LinkedEncounter source admitted origin) :=
  producedLocationAgreement link.production

theorem passage_does_not_identify_locations {source admitted origin}
    (link : @LinkedEncounter source admitted origin) :
    (localizeParticipant link.production .left).location ≠ (priorEncounterLeft link).location := by
  intro same
  have carried := localized_prolong_location (current := origin.next)
    (localizeParticipant origin .left) link.history
  exact linked_encounters_are_distinct link (same.trans carried)

theorem passage_keeps_prior_effects {source admitted origin} (link : @LinkedEncounter source admitted origin) :
    AttachedEffects (priorEncounterLeft link) = origin.effects.1 ∧ AttachedEffects (priorEncounterRight link) = origin.effects.2 :=
  ⟨localized_prolong_effects _ link.history, localized_prolong_effects _ link.history⟩

def EncounterCourse.priorAgreement {source admitted origin} (course : @EncounterCourse source admitted origin) :=
  continuedLocationAgreement origin course.history

def EncounterCourse.lastAgreement {source admitted origin} (course : @EncounterCourse source admitted origin) :=
  producedLocationAgreement course.last

theorem nonempty_course_keeps_distinct_locations {source admitted origin}
    (course : @EncounterCourse source admitted origin) (positive : 0 < course.links) :
    (localizeParticipant course.last .left).location ≠
      ((localizeParticipant origin .left).prolong course.history).location := by
  intro same
  have carried := localized_prolong_location (current := origin.next)
    (localizeParticipant origin .left) course.history
  have anchors := same.trans carried
  have strict := (course.formation.used positive).position_decreases
  change (comparisonAnchor course.last.head).position <
    (course.history.transport.references (comparisonAnchor origin.head)).position at strict
  change comparisonAnchor course.last.head = course.history.transport.references (comparisonAnchor origin.head) at anchors
  rw [anchors] at strict
  exact Nat.lt_irrefl _ strict

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.LinkedEncounter.priorAgreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.LinkedEncounter.newAgreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.passage_does_not_identify_locations
#print axioms RelationalPerimeter.Relativity.Reconstruction.passage_keeps_prior_effects
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterCourse.priorAgreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.EncounterCourse.lastAgreement
#print axioms RelationalPerimeter.Relativity.Reconstruction.nonempty_course_keeps_distinct_locations
/- AXIOM_AUDIT_END -/
