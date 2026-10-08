import RelationalPerimeter.Relativity.Production.InstrumentalReadingCovers

/-!
# Joint finite covers and realized intersections on constituted ports

Every selected clause retains its indexed local leaf and actual certificate.
Selection consumes one joint realization, without listing combinations of
leaves. Intersections require two whole realizations on the same attachment;
alignment alone supplies neither values nor satisfaction. Cached continuation
and exact presentation agreements transport these descriptions, not producers.
This remains an instrumental construction, not physical location or geometry.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production

inductive InstrumentalConstraintCover : List AttachedReadingConstraint → Type where
  | nil : InstrumentalConstraintCover []
  | cons {port window rest} (first : InstrumentalReadingCover window)
      (tail : InstrumentalConstraintCover rest) : InstrumentalConstraintCover (⟨port, window⟩ :: rest)

def InstrumentalConstraintCover.identity (clauses : List AttachedReadingConstraint) :
    InstrumentalConstraintCover clauses :=
  match clauses with
  | [] => .nil
  | clause :: rest => .cons (.identity clause.window) (.identity rest)
termination_by structural clauses

def InstrumentalConstraintCover.append {one two}
    (first : InstrumentalConstraintCover one) (second : InstrumentalConstraintCover two) :
    InstrumentalConstraintCover (one ++ two) :=
  match first with
  | .nil => second
  | .cons cover tail => .cons cover (tail.append second)
termination_by structural first

/-- A joint positive derivation, including each selected leaf and certificate.
The fine constraint list is computed from these selections, never prescribed. -/
inductive CoveredReadingConstraints {source pair head current}
    (attached : @InteractionAttachment source pair head current) :
    {clauses : List AttachedReadingConstraint} → InstrumentalConstraintCover clauses → Type where
  | nil : CoveredReadingConstraints attached .nil
  | cons {port window rest first tail} (chosen : @CoveredNumericReading source pair head current attached port window first)
      (suffix : @CoveredReadingConstraints source pair head current attached rest tail) :
      @CoveredReadingConstraints source pair head current attached (⟨port, window⟩ :: rest)
        (InstrumentalConstraintCover.cons first tail)

def CoveredReadingConstraints.fine {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) : List AttachedReadingConstraint :=
  match chosen with
  | .nil => []
  | .cons (port := port) first tail => ⟨port, first.window⟩ :: tail.fine

def CoveredReadingConstraints.refined {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    CertifiedReadingConstraints attached chosen.fine :=
  match chosen with
  | .nil => .nil
  | .cons first tail => .cons first.reading tail.refined

def CoveredReadingConstraints.refinement {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    ReadingConstraintRefinement clauses chosen.fine :=
  match chosen with
  | .nil => .nil
  | .cons first tail => .cons first.leaf.refinement tail.refinement

def CoveredReadingConstraints.restrict {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    CertifiedReadingConstraints attached clauses :=
  match chosen with
  | .nil => .nil
  | .cons first tail => .cons first.restrict tail.restrict

def CoveredReadingConstraints.paths {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) : List (List Bool) :=
  match chosen with
  | .nil => []
  | .cons first tail => first.leaf.branches :: tail.paths

def InstrumentalConstraintCover.select {source pair head current attached clauses}
    (cover : InstrumentalConstraintCover clauses)
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    CoveredReadingConstraints attached cover :=
  match cover, readings with
  | .nil, .nil => .nil
  | .cons first tail, .cons reading suffix => .cons (first.select reading) (tail.select suffix)
termination_by structural cover

theorem joint_refined_restriction {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    chosen.refined.restrict chosen.refinement = chosen.restrict := by
  induction chosen with
  | nil => rfl
  | @cons port window rest firstCover tailCover first tail ih =>
    exact congrArg (CertifiedReadingConstraints.cons (clause := ⟨port, window⟩) first.restrict) ih

theorem selected_joint_cover_restricts {source pair head current attached clauses}
    (cover : InstrumentalConstraintCover clauses)
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    (cover.select readings).restrict = readings := by
  induction cover with
  | nil => cases readings; rfl
  | cons first tail ih => cases readings with
    | cons reading suffix =>
      change CertifiedReadingConstraints.cons (first.select reading).restrict (tail.select suffix).restrict = _
      rw [selected_cover_restricts_to_source, ih suffix]

theorem selected_joint_cover_values {source pair head current attached clauses}
    (cover : InstrumentalConstraintCover clauses)
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    (cover.select readings).refined.values = readings.values := by
  have values := constraint_restriction_values (cover.select readings).refined (cover.select readings).refinement
  rw [joint_refined_restriction, selected_joint_cover_restricts] at values
  exact values.symm

theorem joint_identity_fine {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    ((InstrumentalConstraintCover.identity clauses).select readings).fine = clauses := by
  induction readings with
  | nil => rfl
  | cons reading tail ih => exact congrArg (List.cons _) ih

theorem joint_identity_paths {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    ((InstrumentalConstraintCover.identity clauses).select readings).paths = clauses.map (fun _ => []) := by
  induction readings with
  | nil => rfl
  | cons reading tail ih => exact congrArg (List.cons []) ih

theorem joint_cover_keeps_ports {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) :
    chosen.fine.map AttachedReadingConstraint.port = clauses.map AttachedReadingConstraint.port := by
  induction chosen with
  | nil => rfl
  | cons first tail ih => exact congrArg (List.cons _) ih

def decideConjunctiveCover {source pair head current}
    (attached : @InteractionAttachment source pair head current) {clauses}
    (cover : InstrumentalConstraintCover clauses) :
    PSum (CoveredReadingConstraints attached cover) (¬ ReadingConstraintsSatisfied attached clauses) :=
  match certifyReadingConstraints attached clauses with
  | .inl readings => .inl (cover.select readings)
  | .inr refused => .inr refused

theorem conjunctive_decision_consumes_joint_result {source pair head current}
    (attached : @InteractionAttachment source pair head current) {clauses}
    (cover : InstrumentalConstraintCover clauses) :
    decideConjunctiveCover attached cover =
      match certifyReadingConstraints attached clauses with
      | .inl readings => .inl (cover.select readings)
      | .inr refused => .inr refused := rfl

theorem conjunctive_cover_exact {source pair head current}
    (attached : @InteractionAttachment source pair head current) {clauses}
    (cover : InstrumentalConstraintCover clauses) :
    ReadingConstraintsSatisfied attached clauses ↔ Nonempty (CoveredReadingConstraints attached cover) := by
  constructor
  · intro satisfied
    cases certifyReadingConstraints attached clauses with
    | inl readings => exact ⟨cover.select readings⟩
    | inr refused => exact False.elim (refused satisfied)
  · intro realized
    cases realized with | intro chosen => exact chosen.restrict.satisfied

def CoveredReadingConstraints.append {source pair head current attached one two first second}
    (chosen : @CoveredReadingConstraints source pair head current attached one first)
    (other : CoveredReadingConstraints attached second) :
    CoveredReadingConstraints attached (first.append (two := two) second) :=
  match chosen with
  | .nil => other
  | .cons selected tail => .cons selected (tail.append other)
termination_by structural chosen

theorem joint_selection_append {source pair head current attached one two}
    (first : InstrumentalConstraintCover one) (second : InstrumentalConstraintCover two)
    (readings : @CertifiedReadingConstraints source pair head current attached one)
    (others : CertifiedReadingConstraints attached two) :
    (first.append second).select (readings.append others) = (first.select readings).append (second.select others) := by
  induction first with
  | nil => cases readings; rfl
  | cons cover tail ih => cases readings with
    | cons reading suffix => exact congrArg (CoveredReadingConstraints.cons (cover.select reading)) (ih suffix)

theorem joint_append_paths {source pair head current attached one two first second}
    (chosen : @CoveredReadingConstraints source pair head current attached one first)
    (other : @CoveredReadingConstraints source pair head current attached two second) :
    (chosen.append other).paths = chosen.paths ++ other.paths := by
  induction chosen with
  | nil => rfl
  | cons selected tail ih => exact congrArg (List.cons selected.leaf.branches) ih

def CoveredReadingConstraints.prolong {source pair head current target attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (history : RecurringHistory current target) : CoveredReadingConstraints (attached.prolong history) cover :=
  match chosen with
  | .nil => .nil
  | .cons first tail => .cons (first.prolong history) (tail.prolong history)

def CoveredReadingConstraints.transport {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (chosen : @CoveredReadingConstraints source pair head current one clauses cover) :
    CoveredReadingConstraints two cover :=
  match chosen with
  | .nil => .nil
  | .cons first tail => .cons (first.transport agreement) (tail.transport agreement)

theorem joint_prolong_paths {source pair head current target attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (history : RecurringHistory current target) : (chosen.prolong history).paths = chosen.paths := by
  induction chosen with
  | nil => rfl
  | cons first tail ih => exact congrArg (List.cons first.leaf.branches) ih

theorem joint_transport_paths {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (chosen : @CoveredReadingConstraints source pair head current one clauses cover) :
    (chosen.transport agreement).paths = chosen.paths := by
  induction chosen with
  | nil => rfl
  | cons first tail ih => exact congrArg (List.cons first.leaf.branches) ih

theorem joint_selection_prolong_square {source pair head current target attached clauses}
    (cover : InstrumentalConstraintCover clauses)
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (history : RecurringHistory current target) :
    (cover.select readings).prolong history = cover.select (readings.prolong history) := by
  induction cover with
  | nil => cases readings; rfl
  | cons first tail ih => cases readings with
    | cons reading suffix =>
      change CoveredReadingConstraints.cons ((first.select reading).prolong history)
        ((tail.select suffix).prolong history) = _
      rw [cover_selection_prolong_square, ih suffix]
      rfl

theorem joint_selection_transport_square {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (cover : InstrumentalConstraintCover clauses) (readings : CertifiedReadingConstraints one clauses) :
    (cover.select readings).transport agreement = cover.select (readings.transport agreement) := by
  induction cover with
  | nil => cases readings; rfl
  | cons first tail ih => cases readings with
    | cons reading suffix =>
      change CoveredReadingConstraints.cons ((first.select reading).transport agreement)
        ((tail.select suffix).transport agreement) = _
      rw [cover_selection_transport_square, ih suffix]
      rfl

theorem joint_prolong_restriction_square {source pair head current target attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (history : RecurringHistory current target) :
    (chosen.prolong history).restrict = chosen.restrict.prolong history := by
  induction chosen with
  | nil => rfl
  | @cons port window rest firstCover tailCover first tail ih =>
    exact congrArg (CertifiedReadingConstraints.cons (clause := ⟨port, window⟩) (first.prolong history).restrict) ih

theorem joint_transport_restriction_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (chosen : @CoveredReadingConstraints source pair head current one clauses cover) :
    (chosen.transport agreement).restrict = chosen.restrict.transport agreement := by
  induction chosen with
  | nil => rfl
  | @cons port window rest firstCover tailCover first tail ih =>
    exact congrArg (CertifiedReadingConstraints.cons (clause := ⟨port, window⟩) (first.transport agreement).restrict) ih

theorem joint_continuation_square {source pair head current target one two clauses cover}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord)
    (chosen : @CoveredReadingConstraints source pair head current one clauses cover) :
    (chosen.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (chosen.transport agreement).prolong extension.execution.second.history := by
  induction chosen with
  | nil => rfl
  | cons first tail ih =>
    change CoveredReadingConstraints.cons _ _ = CoveredReadingConstraints.cons _ _
    rw [covered_continuation_square, ih]

/-- Alignment records corresponding ports. It is not a satisfaction witness. -/
inductive ReadingConstraintIntersection : List AttachedReadingConstraint → List AttachedReadingConstraint → Type where
  | nil : ReadingConstraintIntersection [] []
  | cons {port one two first second} (tail : ReadingConstraintIntersection first second) :
      ReadingConstraintIntersection (⟨port, one⟩ :: first) (⟨port, two⟩ :: second)

def ReadingConstraintIntersection.clauses {one two} (alignment : ReadingConstraintIntersection one two) :
    List AttachedReadingConstraint :=
  match alignment with
  | .nil => []
  | .cons (port := port) (one := first) (two := second) tail => ⟨port, first.intersection second⟩ :: tail.clauses

def ReadingConstraintIntersection.left {one two} (alignment : ReadingConstraintIntersection one two) :
    ReadingConstraintRefinement one alignment.clauses :=
  match alignment with
  | .nil => .nil
  | .cons tail => .cons (window_intersection_left _ _) tail.left

def ReadingConstraintIntersection.right {one two} (alignment : ReadingConstraintIntersection one two) :
    ReadingConstraintRefinement two alignment.clauses :=
  match alignment with
  | .nil => .nil
  | .cons tail => .cons (window_intersection_right _ _) tail.right

def ReadingConstraintIntersection.fromRefinements {coarse one two}
    (first : ReadingConstraintRefinement coarse one) (second : ReadingConstraintRefinement coarse two) :
    ReadingConstraintIntersection one two :=
  match first, second with
  | .nil, .nil => .nil
  | .cons _ tail, .cons _ rest => .cons (ReadingConstraintIntersection.fromRefinements tail rest)
termination_by structural first

def ReadingConstraintIntersection.certify {source pair head current attached one two}
    (alignment : ReadingConstraintIntersection one two)
    (first : @CertifiedReadingConstraints source pair head current attached one)
    (second : CertifiedReadingConstraints attached two) : CertifiedReadingConstraints attached alignment.clauses :=
  match alignment, first, second with
  | .nil, .nil, .nil => .nil
  | .cons tail, .cons reading rest, .cons other suffix => .cons (reading.common other) (tail.certify rest suffix)
termination_by structural alignment

theorem constraint_satisfaction_restrict {source pair head current attached coarse fine}
    (refinement : ReadingConstraintRefinement coarse fine)
    (satisfied : @ReadingConstraintsSatisfied source pair head current attached fine) :
    ReadingConstraintsSatisfied attached coarse := by
  induction refinement with
  | nil => exact True.intro
  | cons head tail ih => exact ⟨head.contains satisfied.1, ih satisfied.2⟩

theorem constraint_intersection_satisfaction_iff {source pair head current}
    (attached : @InteractionAttachment source pair head current) {one two}
    (alignment : ReadingConstraintIntersection one two) :
    ReadingConstraintsSatisfied attached alignment.clauses ↔
      ReadingConstraintsSatisfied attached one ∧ ReadingConstraintsSatisfied attached two := by
  constructor
  · intro realized
    exact ⟨constraint_satisfaction_restrict alignment.left realized,
      constraint_satisfaction_restrict alignment.right realized⟩
  · intro both
    induction alignment with
    | nil => exact True.intro
    | cons tail ih => exact ⟨window_intersection_contains both.1.1 both.2.1, ih ⟨both.1.2, both.2.2⟩⟩

theorem realized_intersection_returns {source pair head current attached one two}
    (alignment : ReadingConstraintIntersection one two)
    (first : @CertifiedReadingConstraints source pair head current attached one)
    (second : CertifiedReadingConstraints attached two) :
    (alignment.certify first second).restrict alignment.left = first ∧
      (alignment.certify first second).restrict alignment.right = second := by
  induction alignment with
  | nil => cases first; cases second; exact ⟨rfl, rfl⟩
  | cons tail ih => cases first with
    | cons reading rest => cases second with
      | cons other suffix =>
        have headReturns := numeric_common_restrictions reading other
        have tailReturns := ih rest suffix
        constructor
        · change CertifiedReadingConstraints.cons _ _ = CertifiedReadingConstraints.cons reading rest
          rw [headReturns.1, tailReturns.1]
        · change CertifiedReadingConstraints.cons _ _ = CertifiedReadingConstraints.cons other suffix
          rw [headReturns.2, tailReturns.2]

theorem realized_intersection_prolong_square {source pair head current target attached one two}
    (alignment : ReadingConstraintIntersection one two)
    (first : @CertifiedReadingConstraints source pair head current attached one)
    (second : CertifiedReadingConstraints attached two) (history : RecurringHistory current target) :
    (alignment.certify first second).prolong history =
      alignment.certify (first.prolong history) (second.prolong history) := by
  induction alignment with
  | nil => cases first; cases second; rfl
  | @cons port firstWindow secondWindow firstClauses secondClauses tail ih => cases first with
    | cons reading rest => cases second with
      | cons other suffix =>
        exact congrArg
          (CertifiedReadingConstraints.cons (clause := ⟨port, firstWindow.intersection secondWindow⟩)
            ((reading.common other).prolong history)) (ih rest suffix)

theorem realized_intersection_transport_square {source pair head current target one two firstClauses secondClauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (alignment : ReadingConstraintIntersection firstClauses secondClauses)
    (first : CertifiedReadingConstraints one firstClauses) (second : CertifiedReadingConstraints one secondClauses) :
    (alignment.certify first second).transport agreement =
      alignment.certify (first.transport agreement) (second.transport agreement) := by
  induction alignment with
  | nil => cases first; cases second; rfl
  | @cons port firstWindow secondWindow firstClauses secondClauses tail ih => cases first with
    | cons reading rest => cases second with
      | cons other suffix =>
        exact congrArg
          (CertifiedReadingConstraints.cons (clause := ⟨port, firstWindow.intersection secondWindow⟩)
            ((reading.common other).transport agreement)) (ih rest suffix)

def pullbackConjunctiveCover {source pair head current attached coarse fine}
    (cover : InstrumentalConstraintCover coarse) (refinement : ReadingConstraintRefinement coarse fine)
    (readings : @CertifiedReadingConstraints source pair head current attached fine) :
    (chosen : CoveredReadingConstraints attached cover) ×'
      (alignment : ReadingConstraintIntersection chosen.fine fine) ×'
        CertifiedReadingConstraints attached alignment.clauses :=
  let chosen := cover.select (readings.restrict refinement)
  let alignment := ReadingConstraintIntersection.fromRefinements chosen.refinement refinement
  ⟨chosen, alignment, alignment.certify chosen.refined readings⟩

theorem conjunctive_pullback_returns {source pair head current attached coarse fine}
    (cover : InstrumentalConstraintCover coarse) (refinement : ReadingConstraintRefinement coarse fine)
    (readings : @CertifiedReadingConstraints source pair head current attached fine) :
    let pulled := pullbackConjunctiveCover cover refinement readings
    pulled.2.2.restrict pulled.2.1.left = pulled.1.refined ∧
      pulled.2.2.restrict pulled.2.1.right = readings :=
  realized_intersection_returns _ _ _

theorem conjunctive_pullback_coarse_return {source pair head current attached coarse fine}
    (cover : InstrumentalConstraintCover coarse) (refinement : ReadingConstraintRefinement coarse fine)
    (readings : @CertifiedReadingConstraints source pair head current attached fine) :
    let pulled := pullbackConjunctiveCover cover refinement readings
    pulled.2.2.restrict (pulled.1.refinement.compose pulled.2.1.left) = readings.restrict refinement := by
  have firstReturn := (conjunctive_pullback_returns cover refinement readings).1
  dsimp only
  rw [← constraint_restriction_composes, firstReturn, joint_refined_restriction]
  exact selected_joint_cover_restricts cover (readings.restrict refinement)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalConstraintCover
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalConstraintCover.identity
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalConstraintCover.append
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.fine
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.refined
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.refinement
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.restrict
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.paths
#print axioms RelationalPerimeter.Relativity.Production.InstrumentalConstraintCover.select
#print axioms RelationalPerimeter.Relativity.Production.joint_refined_restriction
#print axioms RelationalPerimeter.Relativity.Production.selected_joint_cover_restricts
#print axioms RelationalPerimeter.Relativity.Production.selected_joint_cover_values
#print axioms RelationalPerimeter.Relativity.Production.joint_identity_fine
#print axioms RelationalPerimeter.Relativity.Production.joint_identity_paths
#print axioms RelationalPerimeter.Relativity.Production.joint_cover_keeps_ports
#print axioms RelationalPerimeter.Relativity.Production.decideConjunctiveCover
#print axioms RelationalPerimeter.Relativity.Production.conjunctive_decision_consumes_joint_result
#print axioms RelationalPerimeter.Relativity.Production.conjunctive_cover_exact
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.append
#print axioms RelationalPerimeter.Relativity.Production.joint_selection_append
#print axioms RelationalPerimeter.Relativity.Production.joint_append_paths
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.prolong
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.transport
#print axioms RelationalPerimeter.Relativity.Production.joint_prolong_paths
#print axioms RelationalPerimeter.Relativity.Production.joint_transport_paths
#print axioms RelationalPerimeter.Relativity.Production.joint_selection_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.joint_selection_transport_square
#print axioms RelationalPerimeter.Relativity.Production.joint_prolong_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.joint_transport_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.joint_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintIntersection
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintIntersection.clauses
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintIntersection.left
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintIntersection.right
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintIntersection.fromRefinements
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintIntersection.certify
#print axioms RelationalPerimeter.Relativity.Production.constraint_satisfaction_restrict
#print axioms RelationalPerimeter.Relativity.Production.constraint_intersection_satisfaction_iff
#print axioms RelationalPerimeter.Relativity.Production.realized_intersection_returns
#print axioms RelationalPerimeter.Relativity.Production.realized_intersection_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.realized_intersection_transport_square
#print axioms RelationalPerimeter.Relativity.Production.pullbackConjunctiveCover
#print axioms RelationalPerimeter.Relativity.Production.conjunctive_pullback_returns
#print axioms RelationalPerimeter.Relativity.Production.conjunctive_pullback_coarse_return
/- AXIOM_AUDIT_END -/
