import RelationalPerimeter.Relativity.Production.PreciseReadingRefinements

/-!
# Compatible finite descriptions and separating constituted readings

Common refinements consume two already realized descriptions on the same
attachment. No precision course, cover choice or instrumental producer is
replayed. A separate, executable discriminator reads two constituted ports and
returns equality of their numerical values or a positively certified separating
window. Agreement of all these readers determines precisely the numerical
values, not source identity, rich description or physical localization.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Analysis

structure CommonReadingRefinement {source pair head current}
    (attached : @InteractionAttachment source pair head current) (first second : List AttachedReadingConstraint) where
  alignment : ReadingConstraintIntersection first second
  readings : CertifiedReadingConstraints attached alignment.clauses

def RealizedReadingRefinement.common {source pair head current attached clauses}
    (first second : @RealizedReadingRefinement source pair head current attached clauses) :
    CommonReadingRefinement attached first.fine second.fine :=
  let alignment := ReadingConstraintIntersection.fromRefinements first.refinement second.refinement
  ⟨alignment, alignment.certify first.readings second.readings⟩

def CommonReadingRefinement.left {source pair head current attached first second}
    (common : @CommonReadingRefinement source pair head current attached first second) :
    RealizedReadingRefinement attached first :=
  ⟨common.alignment.clauses, common.alignment.left, common.readings⟩

def CommonReadingRefinement.right {source pair head current attached first second}
    (common : @CommonReadingRefinement source pair head current attached first second) :
    RealizedReadingRefinement attached second :=
  ⟨common.alignment.clauses, common.alignment.right, common.readings⟩

theorem realized_common_returns {source pair head current attached clauses}
    (first second : @RealizedReadingRefinement source pair head current attached clauses) :
    (first.common second).left.readings.restrict (first.common second).left.refinement = first.readings ∧
      (first.common second).right.readings.restrict (first.common second).right.refinement = second.readings :=
  realized_intersection_returns _ _ _

theorem realized_common_coarse_returns {source pair head current attached clauses}
    (first second : @RealizedReadingRefinement source pair head current attached clauses) :
    (first.common second).readings.restrict
        (first.refinement.compose (first.common second).alignment.left) = first.readings.restrict first.refinement ∧
      (first.common second).readings.restrict
        (second.refinement.compose (first.common second).alignment.right) = second.readings.restrict second.refinement := by
  have returns := realized_common_returns first second
  constructor
  · rw [← constraint_restriction_composes]
    exact congrArg (fun readings => readings.restrict first.refinement) returns.1
  · rw [← constraint_restriction_composes]
    exact congrArg (fun readings => readings.restrict second.refinement) returns.2

theorem precision_courses_common_return {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (first second : List Precision) :
    let one := refineReadingPrecisions readings first
    let two := refineReadingPrecisions readings second
    let common := one.common two
    common.readings.restrict (one.refinement.compose common.alignment.left) = readings ∧
      common.readings.restrict (two.refinement.compose common.alignment.right) = readings := by
  have returns := realized_common_coarse_returns
    (refineReadingPrecisions readings first) (refineReadingPrecisions readings second)
  rw [precision_run_restricts_exactly, precision_run_restricts_exactly] at returns
  exact returns

theorem common_keeps_both_precision_bounds {source pair head current attached clauses}
    (first second : @RealizedReadingRefinement source pair head current attached clauses)
    (one two : Precision) (firstBound : ReadingSpansBounded one first.fine)
    (secondBound : ReadingSpansBounded two second.fine) :
    ReadingSpansBounded one (first.common second).alignment.clauses ∧
      ReadingSpansBounded two (first.common second).alignment.clauses :=
  ⟨span_bounds_survive_refinement (first.common second).alignment.left one firstBound,
   span_bounds_survive_refinement (first.common second).alignment.right two secondBound⟩

def CommonReadingRefinement.prolong {source pair head current target attached first second}
    (common : @CommonReadingRefinement source pair head current attached first second)
    (history : RecurringHistory current target) : CommonReadingRefinement (attached.prolong history) first second :=
  ⟨common.alignment, common.readings.prolong history⟩

def CommonReadingRefinement.transport {source pair head current target one two first second}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (common : @CommonReadingRefinement source pair head current one first second) :
    CommonReadingRefinement two first second :=
  ⟨common.alignment, common.readings.transport agreement⟩

theorem realized_common_prolong_square {source pair head current target attached clauses}
    (first second : @RealizedReadingRefinement source pair head current attached clauses)
    (history : RecurringHistory current target) :
    (first.common second).prolong history = (first.prolong history).common (second.prolong history) := by
  exact congrArg (CommonReadingRefinement.mk (ReadingConstraintIntersection.fromRefinements first.refinement second.refinement))
    (realized_intersection_prolong_square _ first.readings second.readings history)

theorem realized_common_transport_square {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (first second : RealizedReadingRefinement one clauses) :
    (first.common second).transport agreement = (first.transport agreement).common (second.transport agreement) := by
  exact congrArg (CommonReadingRefinement.mk (ReadingConstraintIntersection.fromRefinements first.refinement second.refinement))
    (realized_intersection_transport_square agreement _ first.readings second.readings)

theorem common_continuation_square {source pair head current target one two first second}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord) (common : CommonReadingRefinement one first second) :
    (common.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (common.transport agreement).prolong extension.execution.second.history := by
  exact congrArg (CommonReadingRefinement.mk common.alignment)
    (constraint_continuation_square agreement extension common.readings)

/-- The witness's value is pinned to the first constituted port. The second
port is refused by that very window, not by a preassigned label. -/
structure NumericReadingSeparation {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo}
    (one : @InteractionAttachment sourceOne pairOne headOne currentOne) (firstPort : AttachedNumericPort)
    (two : @InteractionAttachment sourceTwo pairTwo headTwo currentTwo) (secondPort : AttachedNumericPort) where
  window : ReadingWindow
  first : CertifiedNumericReading one firstPort window
  secondOutside : ¬ window.Contains (attachedNumericReading two secondPort)

/-- This is a discriminator for exact stored readings, not an instrument
measurement, location recognizer or authorization to forget other effects. -/
def separateNumericReadings {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo}
    (one : @InteractionAttachment sourceOne pairOne headOne currentOne) (firstPort : AttachedNumericPort)
    (two : @InteractionAttachment sourceTwo pairTwo headTwo currentTwo) (secondPort : AttachedNumericPort) :
    PSum (attachedNumericReading one firstPort = attachedNumericReading two secondPort)
      (NumericReadingSeparation one firstPort two secondPort) :=
  let first := attachedNumericReading one firstPort
  let second := attachedNumericReading two secondPort
  if same : first = second then .inl same else
    let centered := ReadingWindow.atPrecision first Precision.unit
    if ordered : Rational.Le first second then
      let window : ReadingWindow := ⟨centered.lower, second⟩
      .inr ⟨window, ⟨first, rfl, ⟨(precision_window_contains first Precision.unit).1, ⟨ordered, same⟩⟩⟩,
        window_upper_boundary_excluded window⟩
    else
      let window : ReadingWindow := ⟨second, centered.upper⟩
      .inr ⟨window, ⟨first, rfl, ⟨⟨(Rational.le_total first second).resolve_left ordered, fun equal => same equal.symm⟩,
        (precision_window_contains first Precision.unit).2⟩⟩, window_lower_boundary_excluded window⟩

theorem numeric_separator_excludes_equality {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo
    one firstPort two secondPort}
    (separation : @NumericReadingSeparation sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo
      one firstPort two secondPort) : attachedNumericReading one firstPort ≠ attachedNumericReading two secondPort := by
  intro same
  exact separation.secondOutside ((separation.first.valueExact.trans same) ▸ separation.first.inside)

theorem numeric_separator_admissions {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo
    one firstPort two secondPort}
    (separation : @NumericReadingSeparation sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo
      one firstPort two secondPort) :
    numericWindowAdmitted one firstPort separation.window = true ∧
      numericWindowAdmitted two secondPort separation.window = false :=
  ⟨(numeric_admission_exact ..).mpr (separation.first.valueExact ▸ separation.first.inside),
    (numeric_admission_is_decision ..).trans (decide_eq_false separation.secondOutside)⟩

def numericReadingSeparationOfDifferent {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo}
    (one : @InteractionAttachment sourceOne pairOne headOne currentOne) (firstPort : AttachedNumericPort)
    (two : @InteractionAttachment sourceTwo pairTwo headTwo currentTwo) (secondPort : AttachedNumericPort)
    (different : attachedNumericReading one firstPort ≠ attachedNumericReading two secondPort) :
    NumericReadingSeparation one firstPort two secondPort :=
  match separateNumericReadings one firstPort two secondPort with
  | .inl same => False.elim (different same)
  | .inr separation => separation

theorem numerical_readers_determine_values {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo}
    (one : @InteractionAttachment sourceOne pairOne headOne currentOne) (firstPort : AttachedNumericPort)
    (two : @InteractionAttachment sourceTwo pairTwo headTwo currentTwo) (secondPort : AttachedNumericPort) :
    (∀ window, numericWindowAdmitted one firstPort window = numericWindowAdmitted two secondPort window) ↔
      attachedNumericReading one firstPort = attachedNumericReading two secondPort := by
  constructor
  · intro agree
    cases separateNumericReadings one firstPort two secondPort with
    | inl same => exact same
    | inr separation =>
      have admissions := numeric_separator_admissions separation
      exact False.elim (Bool.noConfusion (admissions.1.symm.trans ((agree separation.window).trans admissions.2)))
  · intro same window
    rw [numeric_admission_is_decision, numeric_admission_is_decision, same]

theorem constraint_admission_singleton {source pair head current}
    (attached : @InteractionAttachment source pair head current) (port : AttachedNumericPort) (window : ReadingWindow) :
    readingConstraintsAdmitted attached [⟨port, window⟩] = numericWindowAdmitted attached port window := by
  unfold readingConstraintsAdmitted certifyReadingConstraints numericWindowAdmitted
  cases certifyNumericReading attached port window <;> rfl

theorem constraint_admission_cons {source pair head current}
    (attached : @InteractionAttachment source pair head current) (clause : AttachedReadingConstraint)
    (rest : List AttachedReadingConstraint) :
    readingConstraintsAdmitted attached (clause :: rest) =
      (numericWindowAdmitted attached clause.port clause.window && readingConstraintsAdmitted attached rest) := by
  unfold readingConstraintsAdmitted numericWindowAdmitted
  rw [certifyReadingConstraints]
  cases certifyNumericReading attached clause.port clause.window with
  | inr refused => rfl
  | inl reading => cases certifyReadingConstraints attached rest <;> rfl

theorem joint_numerical_readers_determine_values {sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo}
    (one : @InteractionAttachment sourceOne pairOne headOne currentOne)
    (two : @InteractionAttachment sourceTwo pairTwo headTwo currentTwo) :
    (∀ clauses, readingConstraintsAdmitted one clauses = readingConstraintsAdmitted two clauses) ↔
      ∀ port, attachedNumericReading one port = attachedNumericReading two port := by
  constructor
  · intro agree port
    apply (numerical_readers_determine_values one port two port).mp
    intro window
    have singleton := agree [⟨port, window⟩]
    rw [constraint_admission_singleton, constraint_admission_singleton] at singleton
    exact singleton
  · intro same clauses
    induction clauses with
    | nil => rfl
    | cons clause rest ih =>
      rw [constraint_admission_cons, constraint_admission_cons,
        (numerical_readers_determine_values one clause.port two clause.port).mpr (same clause.port) clause.window, ih]

def NumericReadingSeparation.prolong
    {sourceOne pairOne headOne currentOne targetOne sourceTwo pairTwo headTwo currentTwo targetTwo one firstPort two secondPort}
    (separation : @NumericReadingSeparation sourceOne pairOne headOne currentOne sourceTwo pairTwo headTwo currentTwo
      one firstPort two secondPort)
    (firstHistory : RecurringHistory currentOne targetOne) (secondHistory : RecurringHistory currentTwo targetTwo) :
    NumericReadingSeparation (one.prolong firstHistory) firstPort (two.prolong secondHistory) secondPort :=
  ⟨separation.window, separation.first.prolong firstHistory, fun inside =>
    separation.secondOutside ((attached_numeric_prolong two secondHistory secondPort) ▸ inside)⟩

def NumericReadingSeparation.transport
    {sourceOne pairOne headOne currentOne targetOne sourceTwo pairTwo headTwo currentTwo targetTwo one newOne two newTwo
      firstPort secondPort}
    (firstAgreement : @AttachedDescriptionAgreement sourceOne pairOne headOne currentOne targetOne one newOne)
    (secondAgreement : @AttachedDescriptionAgreement sourceTwo pairTwo headTwo currentTwo targetTwo two newTwo)
    (separation : NumericReadingSeparation one firstPort two secondPort) :
    NumericReadingSeparation newOne firstPort newTwo secondPort :=
  ⟨separation.window, separation.first.transport firstAgreement, fun inside =>
    separation.secondOutside ((attached_numeric_agreement secondAgreement secondPort) ▸ inside)⟩

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.CommonReadingRefinement
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement.common
#print axioms RelationalPerimeter.Relativity.Production.CommonReadingRefinement.left
#print axioms RelationalPerimeter.Relativity.Production.CommonReadingRefinement.right
#print axioms RelationalPerimeter.Relativity.Production.realized_common_returns
#print axioms RelationalPerimeter.Relativity.Production.realized_common_coarse_returns
#print axioms RelationalPerimeter.Relativity.Production.precision_courses_common_return
#print axioms RelationalPerimeter.Relativity.Production.common_keeps_both_precision_bounds
#print axioms RelationalPerimeter.Relativity.Production.CommonReadingRefinement.prolong
#print axioms RelationalPerimeter.Relativity.Production.CommonReadingRefinement.transport
#print axioms RelationalPerimeter.Relativity.Production.realized_common_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.realized_common_transport_square
#print axioms RelationalPerimeter.Relativity.Production.common_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.NumericReadingSeparation
#print axioms RelationalPerimeter.Relativity.Production.separateNumericReadings
#print axioms RelationalPerimeter.Relativity.Production.numeric_separator_excludes_equality
#print axioms RelationalPerimeter.Relativity.Production.numeric_separator_admissions
#print axioms RelationalPerimeter.Relativity.Production.numericReadingSeparationOfDifferent
#print axioms RelationalPerimeter.Relativity.Production.numerical_readers_determine_values
#print axioms RelationalPerimeter.Relativity.Production.constraint_admission_singleton
#print axioms RelationalPerimeter.Relativity.Production.constraint_admission_cons
#print axioms RelationalPerimeter.Relativity.Production.joint_numerical_readers_determine_values
#print axioms RelationalPerimeter.Relativity.Production.NumericReadingSeparation.prolong
#print axioms RelationalPerimeter.Relativity.Production.NumericReadingSeparation.transport
/- AXIOM_AUDIT_END -/
