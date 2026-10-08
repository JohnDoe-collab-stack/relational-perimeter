import RelationalPerimeter.Relativity.Production.NumericDescriptionWindows

/-!
# Finite constraints realized on one constituted attachment

Each port comes from the attachment's actual reception or comparison. A
conjunction is admitted only by certificates for all its clauses on that same
support. The decision consumes the existing numerical certifier's outputs;
transport and cached continuation reuse the certified readings, not producers.
This is an instrumental constraint language, not a space of physical locations.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production

structure AttachedReadingConstraint where
  port : AttachedNumericPort
  window : ReadingWindow

def ReadingConstraintsSatisfied {source pair head current}
    (attached : @InteractionAttachment source pair head current) : List AttachedReadingConstraint → Prop
  | [] => True
  | clause :: rest => clause.window.Contains (attachedNumericReading attached clause.port) ∧
      ReadingConstraintsSatisfied attached rest

inductive CertifiedReadingConstraints {source pair head current}
    (attached : @InteractionAttachment source pair head current) : List AttachedReadingConstraint → Type where
  | nil : CertifiedReadingConstraints attached []
  | cons {clause rest} (reading : CertifiedNumericReading attached clause.port clause.window)
      (tail : CertifiedReadingConstraints attached rest) : CertifiedReadingConstraints attached (clause :: rest)

theorem CertifiedReadingConstraints.satisfied {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    ReadingConstraintsSatisfied attached clauses := by
  induction readings with
  | nil => exact True.intro
  | cons reading tail ih => exact ⟨reading.valueExact ▸ reading.inside, ih⟩

/-- Each accepted clause retains the very certificate returned by its decision.
A rejected clause or suffix refutes the whole conjunction on this support. -/
def certifyReadingConstraints {source pair head current}
    (attached : @InteractionAttachment source pair head current) (clauses : List AttachedReadingConstraint) :
    PSum (CertifiedReadingConstraints attached clauses) (¬ ReadingConstraintsSatisfied attached clauses) :=
  match clauses with
  | [] => .inl .nil
  | clause :: rest =>
    match certifyNumericReading attached clause.port clause.window with
    | .inr outside => .inr (fun all => outside all.1)
    | .inl reading =>
      match certifyReadingConstraints attached rest with
      | .inr outside => .inr (fun all => outside all.2)
      | .inl tail => .inl (.cons reading tail)
termination_by structural clauses

def readingConstraintsAdmitted {source pair head current}
    (attached : @InteractionAttachment source pair head current) (clauses : List AttachedReadingConstraint) : Bool :=
  match certifyReadingConstraints attached clauses with
  | .inl _ => true
  | .inr _ => false

theorem reading_constraints_admission_exact {source pair head current}
    (attached : @InteractionAttachment source pair head current) (clauses : List AttachedReadingConstraint) :
    readingConstraintsAdmitted attached clauses = true ↔ ReadingConstraintsSatisfied attached clauses := by
  unfold readingConstraintsAdmitted
  cases certifyReadingConstraints attached clauses with
  | inl readings => exact ⟨fun _ => readings.satisfied, fun _ => rfl⟩
  | inr outside => exact ⟨fun wrong => Bool.noConfusion wrong, fun all => False.elim (outside all)⟩

def certifiedReadingConstraintsOfAdmitted {source pair head current}
    (attached : @InteractionAttachment source pair head current) (clauses : List AttachedReadingConstraint)
    (admitted : readingConstraintsAdmitted attached clauses = true) : CertifiedReadingConstraints attached clauses :=
  match certifyReadingConstraints attached clauses with
  | .inl readings => readings
  | .inr outside => False.elim (outside ((reading_constraints_admission_exact attached clauses).mp admitted))

theorem admitted_constraints_are_the_decision_output {source pair head current}
    (attached : @InteractionAttachment source pair head current) (clauses : List AttachedReadingConstraint)
    (admitted : readingConstraintsAdmitted attached clauses = true) :
    certifyReadingConstraints attached clauses =
      .inl (certifiedReadingConstraintsOfAdmitted attached clauses admitted) := by
  unfold certifiedReadingConstraintsOfAdmitted
  generalize resultExact : certifyReadingConstraints attached clauses = result
  cases result with
  | inl readings => rfl
  | inr outside => exact False.elim (outside ((reading_constraints_admission_exact attached clauses).mp admitted))

def CertifiedReadingConstraints.values {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) : List Rational :=
  match readings with
  | .nil => []
  | .cons reading tail => reading.value :: tail.values

theorem constituted_constraint_values {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    readings.values = clauses.map (fun clause => attachedNumericReading attached clause.port) := by
  induction readings with
  | nil => rfl
  | cons reading tail ih =>
    change reading.value :: tail.values = _
    rw [reading.valueExact, ih]
    rfl

def CertifiedReadingConstraints.append {source pair head current attached one two}
    (first : @CertifiedReadingConstraints source pair head current attached one)
    (second : CertifiedReadingConstraints attached two) : CertifiedReadingConstraints attached (one ++ two) :=
  match first with
  | .nil => second
  | .cons reading tail => .cons reading (tail.append second)
termination_by structural first

theorem constraint_append_values {source pair head current attached one two}
    (first : @CertifiedReadingConstraints source pair head current attached one)
    (second : CertifiedReadingConstraints attached two) :
    (first.append second).values = first.values ++ second.values := by
  induction first with
  | nil => rfl
  | cons reading tail ih => exact congrArg (List.cons reading.value) ih

inductive ReadingConstraintRefinement : List AttachedReadingConstraint → List AttachedReadingConstraint → Type where
  | nil : ReadingConstraintRefinement [] []
  | cons {port coarse fine one two} (head : WindowRefinement coarse fine)
      (tail : ReadingConstraintRefinement one two) :
      ReadingConstraintRefinement (⟨port, coarse⟩ :: one) (⟨port, fine⟩ :: two)

def ReadingConstraintRefinement.identity (clauses : List AttachedReadingConstraint) :
    ReadingConstraintRefinement clauses clauses :=
  match clauses with
  | [] => .nil
  | clause :: rest => .cons (.identity clause.window) (.identity rest)
termination_by structural clauses

def ReadingConstraintRefinement.compose {one two three}
    (first : ReadingConstraintRefinement one two) (second : ReadingConstraintRefinement two three) :
    ReadingConstraintRefinement one three :=
  match first, second with
  | .nil, .nil => .nil
  | .cons head tail, .cons next rest => .cons (head.compose next) (tail.compose rest)
termination_by structural first

def CertifiedReadingConstraints.restrict {source pair head current attached coarse fine}
    (readings : @CertifiedReadingConstraints source pair head current attached fine)
    (refinement : ReadingConstraintRefinement coarse fine) : CertifiedReadingConstraints attached coarse :=
  match refinement, readings with
  | .nil, .nil => .nil
  | .cons next rest, .cons reading tail => .cons (reading.restrict next) (tail.restrict rest)

theorem constraint_restriction_values {source pair head current attached coarse fine}
    (readings : @CertifiedReadingConstraints source pair head current attached fine)
    (refinement : ReadingConstraintRefinement coarse fine) :
    (readings.restrict refinement).values = readings.values := by
  induction refinement with
  | nil => cases readings; rfl
  | cons next rest ih => cases readings with
    | cons reading tail => exact congrArg (List.cons reading.value) (ih tail)

theorem constraint_restriction_identity {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    readings.restrict (.identity clauses) = readings := by
  induction readings with
  | nil => rfl
  | cons reading tail ih => exact congrArg (CertifiedReadingConstraints.cons reading) ih

theorem constraint_restriction_composes {source pair head current attached one two three}
    (readings : @CertifiedReadingConstraints source pair head current attached three)
    (first : ReadingConstraintRefinement one two) (second : ReadingConstraintRefinement two three) :
    (readings.restrict second).restrict first = readings.restrict (first.compose second) := by
  induction first generalizing three with
  | nil => cases second; cases readings; rfl
  | @cons port coarse middle one two head tail ih => cases second with
    | cons next rest => cases readings with
      | cons reading suffix =>
        change CertifiedReadingConstraints.cons (clause := ⟨port, coarse⟩)
          ((reading.restrict (coarse := middle) next).restrict head)
          ((suffix.restrict rest).restrict tail) = _
        rw [ih suffix rest]
        rfl

def CertifiedReadingConstraints.prolong {source pair head current target attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (history : RecurringHistory current target) : CertifiedReadingConstraints (attached.prolong history) clauses :=
  match readings with
  | .nil => .nil
  | .cons reading tail => .cons (reading.prolong history) (tail.prolong history)

def CertifiedReadingConstraints.transport {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (readings : CertifiedReadingConstraints one clauses) : CertifiedReadingConstraints two clauses :=
  match readings with
  | .nil => .nil
  | .cons reading tail => .cons (reading.transport agreement) (tail.transport agreement)

theorem constraint_prolong_values {source pair head current target attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (history : RecurringHistory current target) : (readings.prolong history).values = readings.values := by
  induction readings with
  | nil => rfl
  | cons reading tail ih => exact congrArg (List.cons reading.value) ih

theorem constraint_transport_values {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (readings : CertifiedReadingConstraints one clauses) :
    (readings.transport agreement).values = readings.values := by
  induction readings with
  | nil => rfl
  | cons reading tail ih => exact congrArg (List.cons reading.value) ih

theorem constraint_prolong_restriction_square {source pair head current target attached coarse fine}
    (readings : @CertifiedReadingConstraints source pair head current attached fine)
    (history : RecurringHistory current target) (refinement : ReadingConstraintRefinement coarse fine) :
    (readings.restrict refinement).prolong history = (readings.prolong history).restrict refinement := by
  induction refinement with
  | nil => cases readings; rfl
  | @cons port coarse fine one two next rest ih => cases readings with
    | cons reading tail =>
      change CertifiedReadingConstraints.cons (clause := ⟨port, coarse⟩)
        ((reading.restrict (coarse := coarse) next).prolong history)
        ((tail.restrict rest).prolong history) = _
      rw [ih tail]
      rfl

theorem constraint_transport_restriction_square {source pair head current target one two coarse fine}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (readings : CertifiedReadingConstraints one fine) (refinement : ReadingConstraintRefinement coarse fine) :
    (readings.restrict refinement).transport agreement = (readings.transport agreement).restrict refinement := by
  induction refinement with
  | nil => cases readings; rfl
  | @cons port coarse fine one two next rest ih => cases readings with
    | cons reading tail =>
      change CertifiedReadingConstraints.cons (clause := ⟨port, coarse⟩)
        ((reading.restrict (coarse := coarse) next).transport agreement)
        ((tail.restrict rest).transport agreement) = _
      rw [ih tail]
      rfl

theorem constraint_continuation_square {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord) (readings : CertifiedReadingConstraints one clauses) :
    (readings.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (readings.transport agreement).prolong extension.execution.second.history := by
  induction readings with
  | nil => rfl
  | cons reading tail ih =>
    exact congrArg
      (CertifiedReadingConstraints.cons ((reading.transport agreement).prolong extension.execution.second.history)) ih

theorem constraint_satisfaction_prolong {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target)
    (clauses : List AttachedReadingConstraint) :
    ReadingConstraintsSatisfied (attached.prolong history) clauses ↔ ReadingConstraintsSatisfied attached clauses := by
  induction clauses with
  | nil => exact ⟨id, id⟩
  | cons clause rest ih =>
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [attached_numeric_prolong attached history clause.port]
    exact ⟨fun all => ⟨all.1, ih.mp all.2⟩, fun all => ⟨all.1, ih.mpr all.2⟩⟩

theorem constraint_satisfaction_transport {source pair head current target one two}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (clauses : List AttachedReadingConstraint) :
    ReadingConstraintsSatisfied two clauses ↔ ReadingConstraintsSatisfied one clauses := by
  induction clauses with
  | nil => exact ⟨id, id⟩
  | cons clause rest ih =>
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [attached_numeric_agreement agreement clause.port]
    exact ⟨fun all => ⟨all.1, ih.mp all.2⟩, fun all => ⟨all.1, ih.mpr all.2⟩⟩

theorem disjoint_constraints_unrealizable {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (one two : ReadingWindow) (separated : Rational.Le one.upper two.lower)
    (rest : List AttachedReadingConstraint) :
    ¬ ReadingConstraintsSatisfied attached (⟨port, one⟩ :: ⟨port, two⟩ :: rest) := fun all =>
  (rational_strict_le all.1.2 (Rational.le_trans separated all.2.1.1.1)).2 rfl

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.AttachedReadingConstraint
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintsSatisfied
#print axioms RelationalPerimeter.Relativity.Production.CertifiedReadingConstraints
#print axioms RelationalPerimeter.Relativity.Production.CertifiedReadingConstraints.satisfied
#print axioms RelationalPerimeter.Relativity.Production.certifyReadingConstraints
#print axioms RelationalPerimeter.Relativity.Production.reading_constraints_admission_exact
#print axioms RelationalPerimeter.Relativity.Production.certifiedReadingConstraintsOfAdmitted
#print axioms RelationalPerimeter.Relativity.Production.admitted_constraints_are_the_decision_output
#print axioms RelationalPerimeter.Relativity.Production.constituted_constraint_values
#print axioms RelationalPerimeter.Relativity.Production.CertifiedReadingConstraints.append
#print axioms RelationalPerimeter.Relativity.Production.constraint_append_values
#print axioms RelationalPerimeter.Relativity.Production.ReadingConstraintRefinement.compose
#print axioms RelationalPerimeter.Relativity.Production.CertifiedReadingConstraints.restrict
#print axioms RelationalPerimeter.Relativity.Production.constraint_restriction_values
#print axioms RelationalPerimeter.Relativity.Production.constraint_restriction_identity
#print axioms RelationalPerimeter.Relativity.Production.constraint_restriction_composes
#print axioms RelationalPerimeter.Relativity.Production.CertifiedReadingConstraints.prolong
#print axioms RelationalPerimeter.Relativity.Production.CertifiedReadingConstraints.transport
#print axioms RelationalPerimeter.Relativity.Production.constraint_prolong_values
#print axioms RelationalPerimeter.Relativity.Production.constraint_transport_values
#print axioms RelationalPerimeter.Relativity.Production.constraint_prolong_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.constraint_transport_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.constraint_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.constraint_satisfaction_prolong
#print axioms RelationalPerimeter.Relativity.Production.constraint_satisfaction_transport
#print axioms RelationalPerimeter.Relativity.Production.disjoint_constraints_unrealizable
/- AXIOM_AUDIT_END -/
