import RelationalPerimeter

/-! Encounter-local reading covers and arbitrary finite actual used courses.
Reading covers are not asserted to cover a physical spacetime. -/
set_option genInjectivity false
namespace Tests.Relativity.LocatedEncounterChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Continuation.Encounter
open ConstitutiveSearch.Resources

def window : ReadingWindow := ⟨Rational.neg (Rational.ofNat 2), Rational.ofNat 2⟩
def split : OverlappingWindowSplit window :=
  ⟨Rational.neg Rational.one, Rational.one, by decide, by decide, by decide⟩
def cover : InstrumentalConstraintCover (locationClauses [window, window]) :=
  .cons (.split split (.identity _) (.identity _)) (.cons (.split split (.identity _) (.identity _)) .nil)
def first := localizeParticipant Example.produced .left
def second := localizeParticipant Example.produced .right
def readings := certifiedReadingConstraintsOfAdmitted first.attachment (locationClauses [window, window]) (by rfl)
def choice := Example.agreement.selectCover [window, window] cover readings

theorem local_constraints_follow_actual_contact :
    ReadingConstraintsSatisfied second.attachment (locationClauses [window, window]) :=
  (Example.agreement.transportConstraints [window, window] readings).satisfied

theorem actual_reading_selects_each_leaf : choice.paths = [[true], [true]] := rfl
theorem all_values_are_the_produced_values : choice.refined.values = readings.values :=
  located_cover_uses_recorded_values Example.agreement [window, window] cover readings
theorem coarse_certificates_return : choice.restrict =
    Example.agreement.transportConstraints [window, window] readings := selected_joint_cover_restricts ..
theorem constraint_refinement_does_not_remove_effects :
    (choice.refined.restrict choice.refinement).values = choice.refined.values ∧
      AttachedEffects second = second.attachment.effects := location_refinement_keeps_effects second ..

def payload : Ref Example.produced.next.cursor.kinds .payload :=
  .prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior (.prior .here)))))))))
def linked := produceLinkedEncounter Example.produced payload
def initialCourse := startEncounterCourse Example.produced payload
def course (count : Nat) := initialCourse.extend count

theorem later_encounter_is_not_the_prior_location :
    (localizeParticipant linked.production .left).location ≠ (priorEncounterLeft linked).location :=
  passage_does_not_identify_locations linked

theorem equal_values_do_not_identify_encounters :
    linked.production.head.determination.1 = Example.produced.head.determination.1 := rfl

theorem rich_effects_remain_attached :
    AttachedEffects (priorEncounterLeft linked) = Example.produced.effects.1 ∧
      AttachedEffects (priorEncounterRight linked) = Example.produced.effects.2 := passage_keeps_prior_effects linked

def priorAgreement := LinkedEncounter.priorAgreement linked
def newAgreement := LinkedEncounter.newAgreement linked

theorem rich_constraints_follow_actual_passage (clauses : List AttachedReadingConstraint) :
    ReadingConstraintsSatisfied (priorEncounterLeft linked).attachment clauses ↔
      ReadingConstraintsSatisfied first.attachment clauses := by
  with_unfolding_all
    exact located_constraints_prolong (current := Example.produced.next) first linked.history clauses

theorem arbitrary_finite_course_length (count : Nat) : (course count).links = count :=
  (encounter_course_length initialCourse count).trans (Nat.zero_add count)

theorem arbitrary_nonempty_course_has_distinct_endpoints (count : Nat) (positive : 0 < count) :
    (localizeParticipant (course count).last .left).location ≠
      ((localizeParticipant Example.produced .left).prolong (course count).history).location :=
  nonempty_course_keeps_distinct_locations (course count) (by rw [arbitrary_finite_course_length]; exact positive)

def usedCourse (count : Nat) (positive : 0 < count) :=
  (course count).formation.used (by rw [arbitrary_finite_course_length]; exact positive)

#guard (course 3).links == 3
#guard encounterEnabled linked.production.next == false

end Tests.Relativity.LocatedEncounterChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.LocatedEncounterChecks.choice
#print axioms Tests.Relativity.LocatedEncounterChecks.local_constraints_follow_actual_contact
#print axioms Tests.Relativity.LocatedEncounterChecks.actual_reading_selects_each_leaf
#print axioms Tests.Relativity.LocatedEncounterChecks.all_values_are_the_produced_values
#print axioms Tests.Relativity.LocatedEncounterChecks.coarse_certificates_return
#print axioms Tests.Relativity.LocatedEncounterChecks.constraint_refinement_does_not_remove_effects
#print axioms Tests.Relativity.LocatedEncounterChecks.linked
#print axioms Tests.Relativity.LocatedEncounterChecks.later_encounter_is_not_the_prior_location
#print axioms Tests.Relativity.LocatedEncounterChecks.equal_values_do_not_identify_encounters
#print axioms Tests.Relativity.LocatedEncounterChecks.rich_effects_remain_attached
#print axioms Tests.Relativity.LocatedEncounterChecks.priorAgreement
#print axioms Tests.Relativity.LocatedEncounterChecks.newAgreement
#print axioms Tests.Relativity.LocatedEncounterChecks.rich_constraints_follow_actual_passage
#print axioms Tests.Relativity.LocatedEncounterChecks.arbitrary_finite_course_length
#print axioms Tests.Relativity.LocatedEncounterChecks.arbitrary_nonempty_course_has_distinct_endpoints
#print axioms Tests.Relativity.LocatedEncounterChecks.usedCourse
/- AXIOM_AUDIT_END -/
