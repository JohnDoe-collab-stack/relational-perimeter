import RelationalPerimeter.Relativity.Production.ConjunctiveReadingCovers

/-!
# Continuing finite covers from their actual selected leaves

Substitution is a finite positive tree indexed by the received cover. Different
leaves may receive different justified covers. A resumed selector traverses
only the stored path, then selects in that leaf's replacement using its stored
certificate. It does not run the prefix's chooser or any instrumental producer.
The complete output agrees with selection of the composed cover when the
prefix is the canonical selection. This is descriptive composition, not a
physical realization, a location agreement or a memory-erasure permission.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production

inductive ReadingCoverSubstitution : {window : ReadingWindow} → InstrumentalReadingCover window → Type where
  | leaf {window} (replacement : InstrumentalReadingCover window) :
      ReadingCoverSubstitution (.identity window)
  | split {window division first second} (left : ReadingCoverSubstitution first)
      (right : ReadingCoverSubstitution second) :
      ReadingCoverSubstitution (@InstrumentalReadingCover.split window division first second)

def ReadingCoverSubstitution.flatten {window cover} (substitution : @ReadingCoverSubstitution window cover) :
    InstrumentalReadingCover window :=
  match substitution with
  | .leaf replacement => replacement
  | .split (division := division) left right => .split division left.flatten right.flatten

def ReadingCoverSubstitution.identity {window} (cover : InstrumentalReadingCover window) :
    ReadingCoverSubstitution cover :=
  match cover with
  | .identity fine => .leaf (.identity fine)
  | .split _ first second => .split (.identity first) (.identity second)

theorem cover_substitution_identity {window} (cover : InstrumentalReadingCover window) :
    (ReadingCoverSubstitution.identity cover).flatten = cover := by
  induction cover with
  | identity => rfl
  | split division first second ihFirst ihSecond =>
    change InstrumentalReadingCover.split division _ _ = _
    rw [ihFirst, ihSecond]

/-- Only the already selected positive path is followed. -/
def ReadingCoverSubstitution.atLeaf {window cover fine}
    (substitution : @ReadingCoverSubstitution window cover) (path : cover.Leaf fine) :
    InstrumentalReadingCover fine :=
  match substitution, path with
  | .leaf replacement, .here => replacement
  | .split left _, .left previous => left.atLeaf previous
  | .split _ right, .right previous => right.atLeaf previous
termination_by structural path

def ReadingCoverSubstitution.graft {window cover fine final}
    (substitution : @ReadingCoverSubstitution window cover) (priorPath : cover.Leaf fine)
    (suffix : (substitution.atLeaf priorPath).Leaf final) : substitution.flatten.Leaf final :=
  match substitution, priorPath with
  | .leaf _, .here => suffix
  | .split left _, .left previous => .left (left.graft previous suffix)
  | .split _ right, .right previous => .right (right.graft previous suffix)
termination_by structural priorPath

theorem graft_keeps_the_recorded_prefix {window cover fine final}
    (substitution : @ReadingCoverSubstitution window cover) (priorPath : cover.Leaf fine)
    (suffix : (substitution.atLeaf priorPath).Leaf final) :
    (substitution.graft priorPath suffix).branches = priorPath.branches ++ suffix.branches := by
  induction priorPath with
  | here => cases substitution; rfl
  | left previous ih => cases substitution with
    | split left right => exact congrArg (List.cons true) (ih left suffix)
  | right previous ih => cases substitution with
    | split left right => exact congrArg (List.cons false) (ih right suffix)

def ReadingCoverSubstitution.resume {source pair head current attached port window cover}
    (substitution : @ReadingCoverSubstitution window cover)
    (chosen : @CoveredNumericReading source pair head current attached port window cover) :
    CoveredNumericReading attached port substitution.flatten :=
  let suffix := (substitution.atLeaf chosen.leaf).select chosen.reading
  ⟨suffix.window, substitution.graft chosen.leaf suffix.leaf, suffix.reading⟩

theorem resumed_cover_consumes_the_stored_certificate {source pair head current attached port window cover}
    (substitution : @ReadingCoverSubstitution window cover)
    (chosen : @CoveredNumericReading source pair head current attached port window cover) :
    substitution.resume chosen =
      let suffix := (substitution.atLeaf chosen.leaf).select chosen.reading
      CoveredNumericReading.mk suffix.window (substitution.graft chosen.leaf suffix.leaf) suffix.reading := rfl

theorem resumed_cover_keeps_the_prefix {source pair head current attached port window cover}
    (substitution : @ReadingCoverSubstitution window cover)
    (chosen : @CoveredNumericReading source pair head current attached port window cover) :
    (substitution.resume chosen).leaf.branches = chosen.leaf.branches ++
      ((substitution.atLeaf chosen.leaf).select chosen.reading).leaf.branches :=
  graft_keeps_the_recorded_prefix ..

theorem resumed_cover_returns_the_source {source pair head current attached port window cover}
    (substitution : @ReadingCoverSubstitution window cover)
    (chosen : @CoveredNumericReading source pair head current attached port window cover) :
    (substitution.resume chosen).restrict = chosen.restrict :=
  certified_numeric_reading_ext _ _ ((substitution.resume chosen).reading.valueExact.trans chosen.reading.valueExact.symm)

theorem composed_cover_selection_is_resumption {source pair head current attached port window cover}
    (substitution : @ReadingCoverSubstitution window cover)
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    substitution.flatten.select reading = substitution.resume (cover.select reading) := by
  induction substitution with
  | leaf replacement => rfl
  | @split window division first second left right ihLeft ihRight =>
    dsimp only [ReadingCoverSubstitution.flatten]
    rw [InstrumentalReadingCover.select, InstrumentalReadingCover.select]
    dsimp only [OverlappingWindowSplit.choose]
    by_cases below : RationalStrictLess reading.value division.upperCut
    · simp only [dif_pos below]
      rw [ihLeft]
      rfl
    · simp only [dif_neg below]
      rw [ihRight]
      rfl

def ReadingCoverSubstitution.compose {window cover}
    (first : @ReadingCoverSubstitution window cover) :
    ReadingCoverSubstitution first.flatten → ReadingCoverSubstitution cover :=
  match first with
  | .leaf _ => fun second => .leaf second.flatten
  | .split left right => fun second =>
    match second with
    | .split nextLeft nextRight => .split (left.compose nextLeft) (right.compose nextRight)
termination_by structural first

theorem composed_substitution_flattens_exactly {window cover}
    (first : @ReadingCoverSubstitution window cover) (second : ReadingCoverSubstitution first.flatten) :
    (first.compose second).flatten = second.flatten := by
  induction first with
  | leaf => rfl
  | split left right ihLeft ihRight => cases second with
    | split nextLeft nextRight =>
      change InstrumentalReadingCover.split _ _ _ = _
      rw [ihLeft nextLeft, ihRight nextRight]
      rfl

theorem resumed_cover_prolong_square {source pair head current target attached port window cover}
    (substitution : @ReadingCoverSubstitution window cover)
    (chosen : @CoveredNumericReading source pair head current attached port window cover)
    (history : RecurringHistory current target) :
    (substitution.resume chosen).prolong history = substitution.resume (chosen.prolong history) := by
  unfold ReadingCoverSubstitution.resume
  have same := cover_selection_prolong_square (substitution.atLeaf chosen.leaf) chosen.reading history
  exact congrArg (fun suffix =>
    CoveredNumericReading.mk suffix.window (substitution.graft chosen.leaf suffix.leaf) suffix.reading) same

theorem resumed_cover_transport_square {source pair head current target one two port window cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (substitution : @ReadingCoverSubstitution window cover) (chosen : CoveredNumericReading one port cover) :
    (substitution.resume chosen).transport agreement = substitution.resume (chosen.transport agreement) := by
  unfold ReadingCoverSubstitution.resume
  have same := cover_selection_transport_square agreement (substitution.atLeaf chosen.leaf) chosen.reading
  exact congrArg (fun suffix =>
    CoveredNumericReading.mk suffix.window (substitution.graft chosen.leaf suffix.leaf) suffix.reading) same

inductive ConstraintCoverSubstitution : {clauses : List AttachedReadingConstraint} →
    InstrumentalConstraintCover clauses → Type where
  | nil : ConstraintCoverSubstitution .nil
  | cons {port window rest first tail} (head : ReadingCoverSubstitution first)
      (suffix : ConstraintCoverSubstitution tail) :
      ConstraintCoverSubstitution (@InstrumentalConstraintCover.cons port window rest first tail)

def ConstraintCoverSubstitution.flatten {clauses cover} (substitution : @ConstraintCoverSubstitution clauses cover) :
    InstrumentalConstraintCover clauses :=
  match substitution with
  | .nil => .nil
  | .cons first tail => .cons first.flatten tail.flatten

def ConstraintCoverSubstitution.identity {clauses} (cover : InstrumentalConstraintCover clauses) :
    ConstraintCoverSubstitution cover :=
  match cover with
  | .nil => .nil
  | .cons first tail => .cons (.identity first) (.identity tail)

theorem joint_substitution_identity {clauses} (cover : InstrumentalConstraintCover clauses) :
    (ConstraintCoverSubstitution.identity cover).flatten = cover := by
  induction cover with
  | nil => rfl
  | cons first tail ih =>
    change InstrumentalConstraintCover.cons _ _ = _
    rw [cover_substitution_identity, ih]

def ConstraintCoverSubstitution.resume {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    CoveredReadingConstraints attached substitution.flatten :=
  match substitution, chosen with
  | .nil, .nil => .nil
  | .cons first tail, .cons localReading suffix => .cons (first.resume localReading) (tail.resume suffix)
termination_by structural substitution

theorem resumed_joint_cover_returns_every_source {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    (substitution.resume chosen).restrict = chosen.restrict := by
  induction substitution with
  | nil => cases chosen; rfl
  | cons first tail ih => cases chosen with
    | cons localReading suffix =>
      change CertifiedReadingConstraints.cons _ _ = CertifiedReadingConstraints.cons _ _
      rw [resumed_cover_returns_the_source, ih suffix]

theorem composed_joint_selection_is_resumption {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    substitution.flatten.select readings = substitution.resume (cover.select readings) := by
  induction substitution with
  | nil => cases readings; rfl
  | cons first tail ih => cases readings with
    | cons reading suffix =>
      change CoveredReadingConstraints.cons _ _ = CoveredReadingConstraints.cons _ _
      rw [composed_cover_selection_is_resumption, ih suffix]

def ConstraintCoverSubstitution.compose {clauses cover}
    (first : @ConstraintCoverSubstitution clauses cover) (second : ConstraintCoverSubstitution first.flatten) :
    ConstraintCoverSubstitution cover := by
  cases first with
  | nil => cases second; exact .nil
  | cons head tail => cases second with
    | cons next rest => exact .cons (head.compose next) (tail.compose rest)
termination_by structural first

theorem composed_joint_substitution_flattens_exactly {clauses cover}
    (first : @ConstraintCoverSubstitution clauses cover) (second : ConstraintCoverSubstitution first.flatten) :
    (first.compose second).flatten = second.flatten := by
  induction first with
  | nil => cases second; rfl
  | cons head tail ih => cases second with
    | cons next rest =>
      change InstrumentalConstraintCover.cons _ _ = _
      rw [composed_substitution_flattens_exactly, ih rest]
      rfl

theorem resumed_joint_cover_keeps_values {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    (substitution.resume chosen).refined.values = chosen.refined.values := by
  have same := congrArg CertifiedReadingConstraints.values (resumed_joint_cover_returns_every_source substitution chosen)
  rw [← joint_refined_restriction, ← joint_refined_restriction,
    constraint_restriction_values, constraint_restriction_values] at same
  exact same

theorem resumed_joint_cover_prolong_square {source pair head current target attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (history : RecurringHistory current target) :
    (substitution.resume chosen).prolong history = substitution.resume (chosen.prolong history) := by
  induction substitution with
  | nil => cases chosen; rfl
  | cons first tail ih => cases chosen with
    | cons localReading suffix =>
      change CoveredReadingConstraints.cons _ _ = CoveredReadingConstraints.cons _ _
      rw [resumed_cover_prolong_square, ih suffix]

theorem resumed_joint_cover_transport_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (substitution : @ConstraintCoverSubstitution clauses cover) (chosen : CoveredReadingConstraints one cover) :
    (substitution.resume chosen).transport agreement = substitution.resume (chosen.transport agreement) := by
  induction substitution with
  | nil => cases chosen; rfl
  | cons first tail ih => cases chosen with
    | cons localReading suffix =>
      change CoveredReadingConstraints.cons _ _ = CoveredReadingConstraints.cons _ _
      rw [resumed_cover_transport_square, ih suffix]

theorem resumed_joint_cover_continuation_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord)
    (substitution : @ConstraintCoverSubstitution clauses cover) (chosen : CoveredReadingConstraints one cover) :
    ((substitution.resume chosen).prolong extension.execution.first.history).transport (extension.rich agreement) =
      (substitution.resume (chosen.transport agreement)).prolong extension.execution.second.history := by
  rw [joint_continuation_square, resumed_joint_cover_transport_square]

/-- A finite descriptive course. Its suffix refers to the cover just formed,
not to a completed instrumental history or a family of prescribed readings. -/
inductive ReadingCoverCourse : {clauses : List AttachedReadingConstraint} →
    InstrumentalConstraintCover clauses → Type where
  | done {clauses cover} : @ReadingCoverCourse clauses cover
  | step {clauses cover} (head : @ConstraintCoverSubstitution clauses cover)
      (tail : ReadingCoverCourse head.flatten) : ReadingCoverCourse cover

def ReadingCoverCourse.finalCover {clauses cover} (course : @ReadingCoverCourse clauses cover) :
    InstrumentalConstraintCover clauses :=
  match course with
  | .done => cover
  | .step _ tail => tail.finalCover

def ReadingCoverCourse.run {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    CoveredReadingConstraints attached course.finalCover :=
  match course with
  | .done => chosen
  | .step substitution tail =>
      let next := substitution.resume chosen
      tail.run next
termination_by structural course

theorem cover_course_consumes_its_produced_choice {source pair head current attached clauses cover}
    (substitution : @ConstraintCoverSubstitution clauses cover) (tail : ReadingCoverCourse substitution.flatten)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    (ReadingCoverCourse.step substitution tail).run chosen =
      let next := substitution.resume chosen
      tail.run next := rfl

theorem cover_course_returns_every_source {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    (course.run chosen).restrict = chosen.restrict := by
  induction course with
  | done => rfl
  | step substitution tail ih =>
    exact (ih (substitution.resume chosen)).trans (resumed_joint_cover_returns_every_source substitution chosen)

theorem cover_course_selection_is_exact {source pair head current attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    course.finalCover.select readings = course.run (cover.select readings) := by
  induction course with
  | done => rfl
  | step substitution tail ih =>
    change tail.finalCover.select readings = _
    rw [ih, composed_joint_selection_is_resumption]
    rfl

theorem cover_course_prolong_square {source pair head current target attached clauses cover}
    (course : @ReadingCoverCourse clauses cover)
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (history : RecurringHistory current target) :
    (course.run chosen).prolong history = course.run (chosen.prolong history) := by
  induction course with
  | done => rfl
  | step substitution tail ih =>
    change (tail.run (substitution.resume chosen)).prolong history = _
    rw [ih, resumed_joint_cover_prolong_square]
    rfl

theorem cover_course_transport_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (course : @ReadingCoverCourse clauses cover) (chosen : CoveredReadingConstraints one cover) :
    (course.run chosen).transport agreement = course.run (chosen.transport agreement) := by
  induction course with
  | done => rfl
  | step substitution tail ih =>
    change (tail.run (substitution.resume chosen)).transport agreement = _
    rw [ih, resumed_joint_cover_transport_square]
    rfl

theorem cover_course_continuation_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord)
    (course : @ReadingCoverCourse clauses cover) (chosen : CoveredReadingConstraints one cover) :
    ((course.run chosen).prolong extension.execution.first.history).transport (extension.rich agreement) =
      (course.run (chosen.transport agreement)).prolong extension.execution.second.history := by
  rw [joint_continuation_square, cover_course_transport_square]

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution.flatten
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution.identity
#print axioms RelationalPerimeter.Relativity.Production.cover_substitution_identity
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution.atLeaf
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution.graft
#print axioms RelationalPerimeter.Relativity.Production.graft_keeps_the_recorded_prefix
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution.resume
#print axioms RelationalPerimeter.Relativity.Production.resumed_cover_consumes_the_stored_certificate
#print axioms RelationalPerimeter.Relativity.Production.resumed_cover_keeps_the_prefix
#print axioms RelationalPerimeter.Relativity.Production.resumed_cover_returns_the_source
#print axioms RelationalPerimeter.Relativity.Production.composed_cover_selection_is_resumption
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverSubstitution.compose
#print axioms RelationalPerimeter.Relativity.Production.composed_substitution_flattens_exactly
#print axioms RelationalPerimeter.Relativity.Production.resumed_cover_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.resumed_cover_transport_square
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution.flatten
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution.identity
#print axioms RelationalPerimeter.Relativity.Production.joint_substitution_identity
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution.resume
#print axioms RelationalPerimeter.Relativity.Production.resumed_joint_cover_returns_every_source
#print axioms RelationalPerimeter.Relativity.Production.composed_joint_selection_is_resumption
#print axioms RelationalPerimeter.Relativity.Production.ConstraintCoverSubstitution.compose
#print axioms RelationalPerimeter.Relativity.Production.composed_joint_substitution_flattens_exactly
#print axioms RelationalPerimeter.Relativity.Production.resumed_joint_cover_keeps_values
#print axioms RelationalPerimeter.Relativity.Production.resumed_joint_cover_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.resumed_joint_cover_transport_square
#print axioms RelationalPerimeter.Relativity.Production.resumed_joint_cover_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverCourse
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverCourse.finalCover
#print axioms RelationalPerimeter.Relativity.Production.ReadingCoverCourse.run
#print axioms RelationalPerimeter.Relativity.Production.cover_course_consumes_its_produced_choice
#print axioms RelationalPerimeter.Relativity.Production.cover_course_returns_every_source
#print axioms RelationalPerimeter.Relativity.Production.cover_course_selection_is_exact
#print axioms RelationalPerimeter.Relativity.Production.cover_course_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.cover_course_transport_square
#print axioms RelationalPerimeter.Relativity.Production.cover_course_continuation_square
/- AXIOM_AUDIT_END -/
