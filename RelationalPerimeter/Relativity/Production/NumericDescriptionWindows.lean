import RelationalPerimeter.Relativity.Production.ContinuedInteractionDescriptions

/-!
# Certified numerical windows on constituted readings

Ports refer to the reception or comparison anchor of an actual attachment.
Windows bound that stored rational reading, not a spacetime position. Their
decision, restriction and compatible intersection execute no producer. Exact
presentation changes and cached continuations transport the same certificates.
These are finite instrumental descriptions, not a physical cover or continuum.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def RationalStrictLess (one two : Rational) : Prop := Rational.Le one two ∧ one ≠ two

instance (one two : Rational) : Decidable (RationalStrictLess one two) :=
  inferInstanceAs (Decidable (Rational.Le one two ∧ one ≠ two))

theorem rational_le_strict {one two three : Rational} (first : Rational.Le one two)
    (second : RationalStrictLess two three) : RationalStrictLess one three :=
  ⟨Rational.le_trans first second.1, fun same =>
    second.2 (Rational.le_antisymm second.1 (same ▸ first))⟩

theorem rational_strict_le {one two three : Rational} (first : RationalStrictLess one two)
    (second : Rational.Le two three) : RationalStrictLess one three :=
  ⟨Rational.le_trans first.1 second, fun same =>
    first.2 (Rational.le_antisymm first.1 (same.symm ▸ second))⟩

structure ReadingWindow where
  lower : Rational
  upper : Rational

def ReadingWindow.Contains (window : ReadingWindow) (value : Rational) : Prop :=
  RationalStrictLess window.lower value ∧ RationalStrictLess value window.upper

instance (window : ReadingWindow) (value : Rational) : Decidable (window.Contains value) :=
  inferInstanceAs (Decidable (RationalStrictLess window.lower value ∧ RationalStrictLess value window.upper))

def ReadingWindow.span (window : ReadingWindow) : Rational := Rational.sub window.upper window.lower

theorem window_lower_boundary_excluded (window : ReadingWindow) : ¬ window.Contains window.lower :=
  fun inside => inside.1.2 rfl

theorem window_upper_boundary_excluded (window : ReadingWindow) : ¬ window.Contains window.upper :=
  fun inside => inside.2.2 rfl

theorem inverted_window_empty (window : ReadingWindow) (inverted : Rational.Le window.upper window.lower)
    (value : Rational) : ¬ window.Contains value := fun inside =>
  inside.1.2 (Rational.le_antisymm inside.1.1 (Rational.le_trans inside.2.1 inverted))

theorem contained_window_has_positive_span {window : ReadingWindow} {value : Rational}
    (inside : window.Contains value) : Rational.Le Rational.zero window.span ∧ window.span ≠ Rational.zero := by
  have ordered := rational_strict_le inside.1 inside.2.1
  refine ⟨(Rational.zero_le_sub_iff ..).mpr ordered.1, ?_⟩
  intro zeroSpan
  have upperBelow := (Rational.zero_le_sub_iff window.upper window.lower).mp (by
    unfold ReadingWindow.span Rational.sub at zeroSpan
    have same := congrArg Rational.neg zeroSpan
    rw [Rational.neg_add, Rational.neg_neg, Rational.neg_zero,
      Rational.add_comm (Rational.neg window.upper) window.lower] at same
    change Rational.Le Rational.zero (Rational.add window.lower (Rational.neg window.upper))
    rw [same]
    exact Rational.le_refl _)
  exact ordered.2 (Rational.le_antisymm ordered.1 upperBelow)

structure WindowRefinement (coarse fine : ReadingWindow) : Prop where
  lower : Rational.Le coarse.lower fine.lower
  upper : Rational.Le fine.upper coarse.upper

theorem WindowRefinement.identity (window : ReadingWindow) : WindowRefinement window window :=
  ⟨Rational.le_refl _, Rational.le_refl _⟩

theorem WindowRefinement.compose {one two three : ReadingWindow}
    (first : WindowRefinement one two) (second : WindowRefinement two three) : WindowRefinement one three :=
  ⟨Rational.le_trans first.lower second.lower, Rational.le_trans second.upper first.upper⟩

theorem WindowRefinement.contains {coarse fine : ReadingWindow} (refinement : WindowRefinement coarse fine)
    {value} (inside : fine.Contains value) : coarse.Contains value :=
  ⟨rational_le_strict refinement.lower inside.1, rational_strict_le inside.2 refinement.upper⟩

theorem WindowRefinement.span_le {coarse fine : ReadingWindow} (refinement : WindowRefinement coarse fine) :
    Rational.Le fine.span coarse.span :=
  Rational.add_le refinement.upper (Rational.neg_le_neg refinement.lower)

def ReadingWindow.intersection (one two : ReadingWindow) : ReadingWindow :=
  ⟨if Rational.Le one.lower two.lower then two.lower else one.lower,
   if Rational.Le one.upper two.upper then one.upper else two.upper⟩

theorem window_intersection_left (one two : ReadingWindow) :
    WindowRefinement one (one.intersection two) := by
  unfold ReadingWindow.intersection
  split <;> split
  · exact ⟨‹_›, Rational.le_refl _⟩
  · exact ⟨‹_›, (Rational.le_total _ _).resolve_left ‹_›⟩
  · exact ⟨Rational.le_refl _, Rational.le_refl _⟩
  · exact ⟨Rational.le_refl _, (Rational.le_total _ _).resolve_left ‹_›⟩

theorem window_intersection_right (one two : ReadingWindow) :
    WindowRefinement two (one.intersection two) := by
  unfold ReadingWindow.intersection
  split <;> split
  · exact ⟨Rational.le_refl _, ‹_›⟩
  · exact ⟨Rational.le_refl _, Rational.le_refl _⟩
  · exact ⟨(Rational.le_total _ _).resolve_left ‹_›, ‹_›⟩
  · exact ⟨(Rational.le_total _ _).resolve_left ‹_›, Rational.le_refl _⟩

theorem window_intersection_contains {one two : ReadingWindow} {value : Rational}
    (first : one.Contains value) (second : two.Contains value) : (one.intersection two).Contains value := by
  unfold ReadingWindow.intersection
  split <;> split
  · exact ⟨second.1, first.2⟩
  · exact ⟨second.1, second.2⟩
  · exact ⟨first.1, first.2⟩
  · exact ⟨first.1, second.2⟩

inductive AttachedNumericPort where
  | arrival | interaction

def AttachedNumericPort.reference {source pair head current}
    (port : AttachedNumericPort) (attached : @InteractionAttachment source pair head current) :
    Ref current.kinds .reading :=
  match port with
  | .arrival => attached.readingReference
  | .interaction => attached.anchor

def attachedNumericReading {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort) : Rational :=
  current.read (port.reference attached)

theorem attached_numeric_prolong {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target)
    (port : AttachedNumericPort) : attachedNumericReading (attached.prolong history) port =
      attachedNumericReading attached port := by
  cases port
  · exact (attached_reading_exact _).trans (attached_reading_exact attached).symm
  · exact (attached_anchor_output _).trans (attached_anchor_output attached).symm

theorem attached_numeric_agreement {source pair head current target}
    {one : @InteractionAttachment source pair head current} {two : @InteractionAttachment source pair head target}
    (agreement : AttachedDescriptionAgreement one two) (port : AttachedNumericPort) :
    attachedNumericReading two port = attachedNumericReading one port := by
  cases port
  · exact attached_agreement_reading agreement
  · exact site_agreement_anchor_reading agreement.site

/-- The value is pinned to this exact constituted port, never freely supplied. -/
structure CertifiedNumericReading {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) where
  value : Rational
  valueExact : value = attachedNumericReading attached port
  inside : window.Contains value

def certifyNumericReading {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) : PSum (CertifiedNumericReading attached port window)
      (¬ window.Contains (attachedNumericReading attached port)) :=
  let value := attachedNumericReading attached port
  if inside : window.Contains value then .inl ⟨value, rfl, inside⟩ else .inr inside

def numericWindowAdmitted {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) : Bool :=
  match certifyNumericReading attached port window with
  | .inl _ => true
  | .inr _ => false

theorem numeric_admission_is_decision {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) : numericWindowAdmitted attached port window =
      decide (window.Contains (attachedNumericReading attached port)) := by
  unfold numericWindowAdmitted certifyNumericReading
  dsimp only
  by_cases inside : window.Contains (attachedNumericReading attached port)
  · rw [dif_pos inside]
    exact (decide_eq_true inside).symm
  · rw [dif_neg inside]
    exact (decide_eq_false inside).symm

theorem numeric_admission_exact {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) : numericWindowAdmitted attached port window = true ↔
      window.Contains (attachedNumericReading attached port) := by
  constructor
  · intro admitted
    by_cases inside : window.Contains (attachedNumericReading attached port)
    · exact inside
    · have denied := (numeric_admission_is_decision attached port window).trans (decide_eq_false inside)
      exact Bool.noConfusion (denied.symm.trans admitted)
  · intro inside
    exact (numeric_admission_is_decision attached port window).trans (decide_eq_true inside)

def certifiedNumericReadingOfAdmitted {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) (admitted : numericWindowAdmitted attached port window = true) :
    CertifiedNumericReading attached port window :=
  match certifyNumericReading attached port window with
  | .inl reading => reading
  | .inr outside => False.elim (outside ((numeric_admission_exact attached port window).mp admitted))

theorem admitted_certificate_is_the_decision_output {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort)
    (window : ReadingWindow) (admitted : numericWindowAdmitted attached port window = true) :
    certifyNumericReading attached port window =
      .inl (certifiedNumericReadingOfAdmitted attached port window admitted) := by
  unfold certifiedNumericReadingOfAdmitted
  generalize resultExact : certifyNumericReading attached port window = result
  cases result with
  | inl reading => rfl
  | inr outside => exact False.elim (outside ((numeric_admission_exact attached port window).mp admitted))

def CertifiedNumericReading.restrict {source pair head current attached port coarse fine}
    (reading : @CertifiedNumericReading source pair head current attached port fine)
    (refinement : WindowRefinement coarse fine) : CertifiedNumericReading attached port coarse :=
  ⟨reading.value, reading.valueExact, refinement.contains reading.inside⟩

theorem numeric_restriction_identity {source pair head current attached port window}
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    reading.restrict (WindowRefinement.identity window) = reading := by cases reading; rfl

theorem numeric_restriction_composes {source pair head current attached port one two three}
    (reading : @CertifiedNumericReading source pair head current attached port three)
    (first : WindowRefinement one two) (second : WindowRefinement two three) :
    (reading.restrict second).restrict first = reading.restrict (first.compose second) := rfl

def CertifiedNumericReading.common {source pair head current attached port one two}
    (first : @CertifiedNumericReading source pair head current attached port one)
    (second : CertifiedNumericReading attached port two) :
    CertifiedNumericReading attached port (one.intersection two) :=
  ⟨first.value, first.valueExact, window_intersection_contains first.inside
    ((second.valueExact.trans first.valueExact.symm) ▸ second.inside)⟩

theorem numeric_common_restrictions {source pair head current attached port one two}
    (first : @CertifiedNumericReading source pair head current attached port one)
    (second : CertifiedNumericReading attached port two) :
    (first.common second).restrict (window_intersection_left one two) = first ∧
      (first.common second).restrict (window_intersection_right one two) = second := by
  constructor
  · cases first; rfl
  · cases first with | mk first exactFirst insideFirst =>
      cases second with | mk second exactSecond insideSecond =>
        cases exactSecond.trans exactFirst.symm; rfl

theorem certified_numeric_error_bounds {source pair head current attached port window}
    (reading : @CertifiedNumericReading source pair head current attached port window) :
    Rational.Le Rational.zero (Rational.sub reading.value window.lower) ∧
      Rational.Le (Rational.sub reading.value window.lower) window.span ∧
      Rational.Le Rational.zero (Rational.sub window.upper reading.value) ∧
      Rational.Le (Rational.sub window.upper reading.value) window.span :=
  ⟨(Rational.zero_le_sub_iff ..).mpr reading.inside.1.1,
    Rational.add_le_left reading.inside.2.1 (Rational.neg window.lower),
    (Rational.zero_le_sub_iff ..).mpr reading.inside.2.1,
    Rational.add_le (Rational.le_refl _) (Rational.neg_le_neg reading.inside.1.1)⟩

def CertifiedNumericReading.prolong {source pair head current target attached port window}
    (reading : @CertifiedNumericReading source pair head current attached port window)
    (history : RecurringHistory current target) : CertifiedNumericReading (attached.prolong history) port window :=
  ⟨reading.value, reading.valueExact.trans (attached_numeric_prolong attached history port).symm, reading.inside⟩

def CertifiedNumericReading.transport {source pair head current target one two port window}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (reading : CertifiedNumericReading one port window) : CertifiedNumericReading two port window :=
  ⟨reading.value, reading.valueExact.trans (attached_numeric_agreement agreement port).symm, reading.inside⟩

theorem numeric_prolong_restriction_square {source pair head current target attached port coarse fine}
    (reading : @CertifiedNumericReading source pair head current attached port fine)
    (history : RecurringHistory current target) (refinement : WindowRefinement coarse fine) :
    (reading.restrict refinement).prolong history = (reading.prolong history).restrict refinement := rfl

theorem numeric_transport_restriction_square {source pair head current target one two port coarse fine}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (reading : CertifiedNumericReading one port fine) (refinement : WindowRefinement coarse fine) :
    (reading.restrict refinement).transport agreement = (reading.transport agreement).restrict refinement := rfl

theorem numeric_continuation_square {source pair head current target one two port window}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord) (reading : CertifiedNumericReading one port window) :
    (reading.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (reading.transport agreement).prolong extension.execution.second.history := rfl

theorem numeric_admission_prolong {source pair head current target}
    (attached : @InteractionAttachment source pair head current) (history : RecurringHistory current target)
    (port : AttachedNumericPort) (window : ReadingWindow) :
    numericWindowAdmitted (attached.prolong history) port window = numericWindowAdmitted attached port window := by
  rw [numeric_admission_is_decision, numeric_admission_is_decision]
  exact congrArg (fun value => decide (window.Contains value)) (attached_numeric_prolong attached history port)

theorem numeric_admission_transport {source pair head current target one two}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (port : AttachedNumericPort) (window : ReadingWindow) :
    numericWindowAdmitted two port window = numericWindowAdmitted one port window := by
  rw [numeric_admission_is_decision, numeric_admission_is_decision]
  exact congrArg (fun value => decide (window.Contains value)) (attached_numeric_agreement agreement port)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.RationalStrictLess
#print axioms RelationalPerimeter.Relativity.Production.rational_le_strict
#print axioms RelationalPerimeter.Relativity.Production.rational_strict_le
#print axioms RelationalPerimeter.Relativity.Production.ReadingWindow.Contains
#print axioms RelationalPerimeter.Relativity.Production.window_lower_boundary_excluded
#print axioms RelationalPerimeter.Relativity.Production.window_upper_boundary_excluded
#print axioms RelationalPerimeter.Relativity.Production.inverted_window_empty
#print axioms RelationalPerimeter.Relativity.Production.contained_window_has_positive_span
#print axioms RelationalPerimeter.Relativity.Production.WindowRefinement.compose
#print axioms RelationalPerimeter.Relativity.Production.WindowRefinement.contains
#print axioms RelationalPerimeter.Relativity.Production.WindowRefinement.span_le
#print axioms RelationalPerimeter.Relativity.Production.ReadingWindow.intersection
#print axioms RelationalPerimeter.Relativity.Production.window_intersection_left
#print axioms RelationalPerimeter.Relativity.Production.window_intersection_right
#print axioms RelationalPerimeter.Relativity.Production.window_intersection_contains
#print axioms RelationalPerimeter.Relativity.Production.AttachedNumericPort.reference
#print axioms RelationalPerimeter.Relativity.Production.attachedNumericReading
#print axioms RelationalPerimeter.Relativity.Production.attached_numeric_prolong
#print axioms RelationalPerimeter.Relativity.Production.attached_numeric_agreement
#print axioms RelationalPerimeter.Relativity.Production.CertifiedNumericReading
#print axioms RelationalPerimeter.Relativity.Production.certifyNumericReading
#print axioms RelationalPerimeter.Relativity.Production.numericWindowAdmitted
#print axioms RelationalPerimeter.Relativity.Production.numeric_admission_is_decision
#print axioms RelationalPerimeter.Relativity.Production.numeric_admission_exact
#print axioms RelationalPerimeter.Relativity.Production.certifiedNumericReadingOfAdmitted
#print axioms RelationalPerimeter.Relativity.Production.admitted_certificate_is_the_decision_output
#print axioms RelationalPerimeter.Relativity.Production.CertifiedNumericReading.restrict
#print axioms RelationalPerimeter.Relativity.Production.numeric_restriction_identity
#print axioms RelationalPerimeter.Relativity.Production.numeric_restriction_composes
#print axioms RelationalPerimeter.Relativity.Production.CertifiedNumericReading.common
#print axioms RelationalPerimeter.Relativity.Production.numeric_common_restrictions
#print axioms RelationalPerimeter.Relativity.Production.certified_numeric_error_bounds
#print axioms RelationalPerimeter.Relativity.Production.CertifiedNumericReading.prolong
#print axioms RelationalPerimeter.Relativity.Production.CertifiedNumericReading.transport
#print axioms RelationalPerimeter.Relativity.Production.numeric_prolong_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.numeric_transport_restriction_square
#print axioms RelationalPerimeter.Relativity.Production.numeric_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.numeric_admission_prolong
#print axioms RelationalPerimeter.Relativity.Production.numeric_admission_transport
/- AXIOM_AUDIT_END -/
