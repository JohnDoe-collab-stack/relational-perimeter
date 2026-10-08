import RelationalPerimeter.Relativity.Production.ReadingCompatibility
import RelationalPerimeter.Relativity.Production.ContinuedReadingCovers

/-!
# Restricting realized intersections to recorded cover choices

A more precise description and an already selected cover give a positively
realized intersection. Returning its certificates follows the stored leaves;
it does not reselect the prefix. This matters for a valid noncanonical choice
in an overlap. Further substitutions and finite courses consume that returned
choice. Only descriptive stability is established: no physical location,
memory erasure or new instrumental production is supplied by this operation.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production

/-- Reattach received certificates to the same positive leaves. The input
list is indexed by the fine constraints of those leaves, not a free list. -/
def CoveredReadingConstraints.withReadings {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    CertifiedReadingConstraints attached chosen.fine → CoveredReadingConstraints attached cover :=
  match chosen with
  | .nil => fun readings => match readings with | .nil => .nil
  | .cons localReading suffix => fun readings => match readings with
    | .cons reading rest =>
        .cons ⟨localReading.window, localReading.leaf, reading⟩ (suffix.withReadings rest)
termination_by structural chosen

theorem received_certificates_return_the_whole_choice {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (readings : CertifiedReadingConstraints attached chosen.fine) : chosen.withReadings readings = chosen := by
  induction chosen with
  | nil => cases readings; rfl
  | cons localReading suffix ih => cases readings with
    | cons reading rest =>
      have same := certified_numeric_reading_ext reading localReading.reading
        (reading.valueExact.trans localReading.reading.valueExact.symm)
      change CoveredReadingConstraints.cons
        (CoveredNumericReading.mk localReading.window localReading.leaf reading) _ = _
      rw [same, ih rest]

theorem received_certificates_keep_every_path {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (readings : CertifiedReadingConstraints attached chosen.fine) :
    (chosen.withReadings readings).paths = chosen.paths :=
  congrArg CoveredReadingConstraints.paths (received_certificates_return_the_whole_choice chosen readings)

def CoveredReadingConstraints.realized {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    RealizedReadingRefinement attached clauses := ⟨chosen.fine, chosen.refinement, chosen.refined⟩

theorem recorded_cover_realization_returns_its_source {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    chosen.realized.readings.restrict chosen.realized.refinement = chosen.restrict :=
  joint_refined_restriction chosen

/-- The existing common-refinement producer consumes both actual realized
descriptions. No selector, admission guess or prescribed intersection is used. -/
def CoveredReadingConstraints.intersect {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    CommonReadingRefinement attached chosen.fine fine.fine := chosen.realized.common fine

theorem recorded_intersection_returns_both_certificates {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    let common := chosen.intersect fine
    common.readings.restrict common.alignment.left = chosen.refined ∧
      common.readings.restrict common.alignment.right = fine.readings :=
  realized_common_returns chosen.realized fine

theorem recorded_intersection_returns_both_coarse_sources {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    let common := chosen.intersect fine
    common.readings.restrict (chosen.refinement.compose common.alignment.left) = chosen.restrict ∧
      common.readings.restrict (fine.refinement.compose common.alignment.right) = fine.readings.restrict fine.refinement := by
  have returns := realized_common_coarse_returns chosen.realized fine
  rw [recorded_cover_realization_returns_its_source] at returns
  exact returns

/-- Consume an intersection that has already been formed. Neither its
construction nor the old cover selection is repeated. -/
def CoveredReadingConstraints.recoverFromIntersection {source pair head current attached clauses cover other}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) : CoveredReadingConstraints attached cover :=
  chosen.withReadings (common.readings.restrict common.alignment.left)

theorem received_intersection_return_consumes_its_certificates {source pair head current attached clauses cover other}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) :
    chosen.recoverFromIntersection common = chosen.withReadings (common.readings.restrict common.alignment.left) := rfl

theorem received_intersection_recovers_the_recorded_choice {source pair head current attached clauses cover other}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) : chosen.recoverFromIntersection common = chosen :=
  received_certificates_return_the_whole_choice chosen (common.readings.restrict common.alignment.left)

def CoveredReadingConstraints.recoverIntersection {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) : CoveredReadingConstraints attached cover :=
  let common := chosen.intersect fine
  chosen.recoverFromIntersection common

theorem intersection_return_consumes_the_produced_certificates {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    chosen.recoverIntersection fine =
      let common := chosen.intersect fine
      chosen.withReadings (common.readings.restrict common.alignment.left) := rfl

theorem intersection_recovers_the_recorded_choice {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) : chosen.recoverIntersection fine = chosen :=
  received_intersection_recovers_the_recorded_choice chosen (chosen.intersect fine)

theorem intersection_return_keeps_every_path {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    (chosen.recoverIntersection fine).paths = chosen.paths :=
  congrArg CoveredReadingConstraints.paths (intersection_recovers_the_recorded_choice chosen fine)

def ConstraintCoverSubstitution.resumeAfterIntersection {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    CoveredReadingConstraints attached substitution.flatten :=
  let returned := chosen.recoverIntersection fine
  substitution.resume returned

def ConstraintCoverSubstitution.resumeFromIntersection {source pair head current attached clauses cover other}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) :
    CoveredReadingConstraints attached substitution.flatten :=
  let returned := chosen.recoverFromIntersection common
  substitution.resume returned

theorem stored_intersection_resumption_is_exact {source pair head current attached clauses cover other}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) :
    substitution.resumeFromIntersection chosen common = substitution.resume chosen := by
  unfold ConstraintCoverSubstitution.resumeFromIntersection
  rw [received_intersection_recovers_the_recorded_choice]

theorem resumed_intersection_consumes_the_returned_choice {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    substitution.resumeAfterIntersection chosen fine =
      let returned := chosen.recoverIntersection fine
      substitution.resume returned := rfl

theorem intersection_resumption_is_exact {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    substitution.resumeAfterIntersection chosen fine = substitution.resume chosen := by
  unfold ConstraintCoverSubstitution.resumeAfterIntersection
  rw [intersection_recovers_the_recorded_choice]

theorem intersection_resumption_returns_the_source {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    (substitution.resumeAfterIntersection chosen fine).restrict = chosen.restrict := by
  rw [intersection_resumption_is_exact]
  exact resumed_joint_cover_returns_every_source substitution chosen

def ReadingCoverCourse.runAfterIntersection {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    CoveredReadingConstraints attached course.finalCover :=
  let returned := chosen.recoverIntersection fine
  course.run returned

def ReadingCoverCourse.runFromIntersection {source pair head current attached clauses cover other}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) :
    CoveredReadingConstraints attached course.finalCover :=
  let returned := chosen.recoverFromIntersection common
  course.run returned

theorem stored_intersection_course_is_exact {source pair head current attached clauses cover other}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (common : CommonReadingRefinement attached chosen.fine other) :
    course.runFromIntersection chosen common = course.run chosen := by
  unfold ReadingCoverCourse.runFromIntersection
  rw [received_intersection_recovers_the_recorded_choice]

theorem cover_course_intersection_consumes_the_return {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    course.runAfterIntersection chosen fine =
      let returned := chosen.recoverIntersection fine
      course.run returned := rfl

theorem intersection_course_is_exact {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    course.runAfterIntersection chosen fine = course.run chosen := by
  unfold ReadingCoverCourse.runAfterIntersection
  rw [intersection_recovers_the_recorded_choice]

theorem intersection_course_returns_every_source {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) :
    (course.runAfterIntersection chosen fine).restrict = chosen.restrict := by
  rw [intersection_course_is_exact]
  exact cover_course_returns_every_source course chosen

theorem intersection_return_prolong_square {source pair head current target attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) (history : RecurringHistory current target) :
    (chosen.recoverIntersection fine).prolong history =
      (chosen.prolong history).recoverIntersection (fine.prolong history) := by
  rw [intersection_recovers_the_recorded_choice, intersection_recovers_the_recorded_choice]

theorem intersection_return_transport_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (chosen : CoveredReadingConstraints one cover) (fine : RealizedReadingRefinement one clauses) :
    (chosen.recoverIntersection fine).transport agreement =
      (chosen.transport agreement).recoverIntersection (fine.transport agreement) := by
  rw [intersection_recovers_the_recorded_choice, intersection_recovers_the_recorded_choice]

theorem intersection_resumption_prolong_square {source pair head current target attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) (history : RecurringHistory current target) :
    (substitution.resumeAfterIntersection chosen fine).prolong history =
      substitution.resumeAfterIntersection (chosen.prolong history) (fine.prolong history) := by
  rw [intersection_resumption_is_exact, intersection_resumption_is_exact]
  exact resumed_joint_cover_prolong_square substitution chosen history

theorem intersection_resumption_transport_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : CoveredReadingConstraints one cover) (fine : RealizedReadingRefinement one clauses) :
    (substitution.resumeAfterIntersection chosen fine).transport agreement =
      substitution.resumeAfterIntersection (chosen.transport agreement) (fine.transport agreement) := by
  rw [intersection_resumption_is_exact, intersection_resumption_is_exact]
  exact resumed_joint_cover_transport_square agreement substitution chosen

theorem intersection_resumption_continuation_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord)
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : CoveredReadingConstraints one cover) (fine : RealizedReadingRefinement one clauses) :
    ((substitution.resumeAfterIntersection chosen fine).prolong extension.execution.first.history).transport
        (extension.rich agreement) =
      (substitution.resumeAfterIntersection (chosen.transport agreement) (fine.transport agreement)).prolong
        extension.execution.second.history := by
  rw [intersection_resumption_is_exact, intersection_resumption_is_exact]
  exact resumed_joint_cover_continuation_square agreement extension substitution chosen

theorem intersection_course_prolong_square {source pair head current target attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (fine : RealizedReadingRefinement attached clauses) (history : RecurringHistory current target) :
    (course.runAfterIntersection chosen fine).prolong history =
      course.runAfterIntersection (chosen.prolong history) (fine.prolong history) := by
  rw [intersection_course_is_exact, intersection_course_is_exact]
  exact cover_course_prolong_square course chosen history

theorem intersection_course_transport_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (course : @ReadingCoverCourse clauses cover)
    (chosen : CoveredReadingConstraints one cover) (fine : RealizedReadingRefinement one clauses) :
    (course.runAfterIntersection chosen fine).transport agreement =
      course.runAfterIntersection (chosen.transport agreement) (fine.transport agreement) := by
  rw [intersection_course_is_exact, intersection_course_is_exact]
  exact cover_course_transport_square agreement course chosen

theorem intersection_course_continuation_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord) (course : @ReadingCoverCourse clauses cover)
    (chosen : CoveredReadingConstraints one cover) (fine : RealizedReadingRefinement one clauses) :
    ((course.runAfterIntersection chosen fine).prolong extension.execution.first.history).transport
        (extension.rich agreement) =
      (course.runAfterIntersection (chosen.transport agreement) (fine.transport agreement)).prolong
        extension.execution.second.history := by
  rw [intersection_course_is_exact, intersection_course_is_exact]
  exact cover_course_continuation_square agreement extension course chosen

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.withReadings
#print axioms RelationalPerimeter.Relativity.Production.received_certificates_return_the_whole_choice
#print axioms RelationalPerimeter.Relativity.Production.received_certificates_keep_every_path
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.realized
#print axioms RelationalPerimeter.Relativity.Production.recorded_cover_realization_returns_its_source
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.intersect
#print axioms RelationalPerimeter.Relativity.Production.recorded_intersection_returns_both_certificates
#print axioms RelationalPerimeter.Relativity.Production.recorded_intersection_returns_both_coarse_sources
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.recoverFromIntersection
#print axioms RelationalPerimeter.Relativity.Production.received_intersection_return_consumes_its_certificates
#print axioms RelationalPerimeter.Relativity.Production.received_intersection_recovers_the_recorded_choice
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.recoverIntersection
#print axioms RelationalPerimeter.Relativity.Production.intersection_return_consumes_the_produced_certificates
#print axioms RelationalPerimeter.Relativity.Production.intersection_recovers_the_recorded_choice
#print axioms RelationalPerimeter.Relativity.Production.intersection_return_keeps_every_path
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution.resumeAfterIntersection
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution.resumeFromIntersection
#print axioms RelationalPerimeter.Relativity.Production.stored_intersection_resumption_is_exact
#print axioms RelationalPerimeter.Relativity.Production.resumed_intersection_consumes_the_returned_choice
#print axioms RelationalPerimeter.Relativity.Production.intersection_resumption_is_exact
#print axioms RelationalPerimeter.Relativity.Production.intersection_resumption_returns_the_source
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverCourse.runAfterIntersection
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverCourse.runFromIntersection
#print axioms RelationalPerimeter.Relativity.Production.stored_intersection_course_is_exact
#print axioms RelationalPerimeter.Relativity.Production.cover_course_intersection_consumes_the_return
#print axioms RelationalPerimeter.Relativity.Production.intersection_course_is_exact
#print axioms RelationalPerimeter.Relativity.Production.intersection_course_returns_every_source
#print axioms RelationalPerimeter.Relativity.Production.intersection_return_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_return_transport_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_resumption_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_resumption_transport_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_resumption_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_course_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_course_transport_square
#print axioms RelationalPerimeter.Relativity.Production.intersection_course_continuation_square
/- AXIOM_AUDIT_END -/
