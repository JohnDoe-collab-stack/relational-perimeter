import RelationalPerimeter.Relativity.Production.ConjunctiveReadingCovers
import RelationalPerimeter.Relativity.Analysis.ConstructiveContinuum

/-!
# Realized refinements of stored readings at every requested precision

Each fine window is computed from the received certificate's actual value,
then intersected with its previous window. Whole-list refinements carry the
same constituted ports, positive certificates and exact restrictions. A finite
list of precision requests is consumed in order, each suffix receiving the
previous result. Precision is descriptive: these operations perform no new
measurement, do not reconstruct physical locations and do not close R4.2's
separate obligation to generate coherent realizations beyond executed events.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

theorem reading_precision_positive (precision : Precision) :
    RationalStrictLess Rational.zero precision.value := by
  refine ⟨precision.zero_le_value, ?_⟩
  intro same
  have encoded := Rational.normalize_agrees precision.fraction
  change Fraction.Agree precision.value.representation precision.fraction at encoded
  rw [← same] at encoded
  have zero := Fraction.trans (Fraction.symm encoded) (Rational.normalize_agrees Fraction.zero)
  unfold Fraction.Agree Precision.fraction Fraction.zero Balance.Agree Balance.scale Balance.zero at zero
  simp only [Nat.mul_one, Nat.zero_mul, Nat.add_zero] at zero
  exact Nat.ne_of_gt precision.numeratorPositive zero

def ReadingWindow.atPrecision (value : Rational) (precision : Precision) : ReadingWindow :=
  ⟨Rational.sub value precision.half.value, Rational.add value precision.half.value⟩

theorem precision_window_contains (value : Rational) (precision : Precision) :
    (ReadingWindow.atPrecision value precision).Contains value := by
  have positive := reading_precision_positive precision.half
  have lower := Rational.add_le_left (Rational.neg_le_neg positive.1) value
  have upper := Rational.add_le_left positive.1 value
  rw [Rational.neg_zero, Rational.zero_add, Rational.add_comm _ value] at lower
  rw [Rational.zero_add, Rational.add_comm _ value] at upper
  refine ⟨⟨lower, ?_⟩, ⟨upper, ?_⟩⟩
  · intro same
    have cancelled := congrArg (fun q => Rational.add (Rational.neg value) q) same
    change Rational.add (Rational.neg value) (Rational.add value (Rational.neg precision.half.value)) =
      Rational.add (Rational.neg value) value at cancelled
    rw [← Rational.add_assoc, Rational.neg_add_cancel, Rational.zero_add] at cancelled
    have zero := congrArg Rational.neg cancelled
    rw [Rational.neg_neg, Rational.neg_zero] at zero
    exact positive.2 zero.symm
  · intro same
    have cancelled := congrArg (fun q => Rational.add (Rational.neg value) q) same
    change Rational.add (Rational.neg value) value =
      Rational.add (Rational.neg value) (Rational.add value precision.half.value) at cancelled
    rw [← Rational.add_assoc, Rational.neg_add_cancel, Rational.zero_add] at cancelled
    exact positive.2 cancelled

theorem precision_window_span (value : Rational) (precision : Precision) :
    (ReadingWindow.atPrecision value precision).span = precision.value := by
  unfold ReadingWindow.atPrecision ReadingWindow.span Rational.sub
  rw [Rational.neg_add, Rational.neg_neg]
  rw [Rational.add_assoc, Rational.add_left_comm precision.half.value (Rational.neg value),
    ← Rational.add_assoc, Rational.add_neg, Rational.zero_add, precision.half_add_half]

def CertifiedNumericReading.atPrecision {source pair head current attached port window}
    (reading : @CertifiedNumericReading source pair head current attached port window)
    (precision : Precision) : CertifiedNumericReading attached port (ReadingWindow.atPrecision reading.value precision) :=
  ⟨reading.value, reading.valueExact, precision_window_contains reading.value precision⟩

def ReadingSpansBounded (precision : Precision) : List AttachedReadingConstraint → Prop
  | [] => True
  | clause :: rest => Rational.Le clause.window.span precision.value ∧ ReadingSpansBounded precision rest

/-- A realized descriptive refinement. The certificate is on the very same
attachment; no independent values, source carrier or location are supplied. -/
structure RealizedReadingRefinement {source pair head current}
    (attached : @InteractionAttachment source pair head current) (coarse : List AttachedReadingConstraint) where
  fine : List AttachedReadingConstraint
  refinement : ReadingConstraintRefinement coarse fine
  readings : CertifiedReadingConstraints attached fine

def RealizedReadingRefinement.identity {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) :
    RealizedReadingRefinement attached clauses := ⟨clauses, .identity clauses, readings⟩

def RealizedReadingRefinement.compose {source pair head current attached clauses}
    (first : @RealizedReadingRefinement source pair head current attached clauses)
    (second : RealizedReadingRefinement attached first.fine) : RealizedReadingRefinement attached clauses :=
  ⟨second.fine, first.refinement.compose second.refinement, second.readings⟩

def refineReadingPrecision {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (precision : Precision) : RealizedReadingRefinement attached clauses :=
  match readings with
  | .nil => ⟨[], .nil, .nil⟩
  | .cons (clause := clause) reading tail =>
    let centered := reading.atPrecision precision
    let refined := reading.common centered
    let suffix := refineReadingPrecision tail precision
    ⟨⟨clause.port, clause.window.intersection (ReadingWindow.atPrecision reading.value precision)⟩ :: suffix.fine,
      .cons (window_intersection_left _ _) suffix.refinement, .cons refined suffix.readings⟩
termination_by structural readings

theorem reading_precision_restricts_exactly {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precision : Precision) :
    (refineReadingPrecision readings precision).readings.restrict
      (refineReadingPrecision readings precision).refinement = readings := by
  induction readings with
  | nil => rfl
  | cons reading tail ih =>
    change CertifiedReadingConstraints.cons
      ((reading.common (reading.atPrecision precision)).restrict (window_intersection_left _ _))
      ((refineReadingPrecision tail precision).readings.restrict
        (refineReadingPrecision tail precision).refinement) = _
    rw [(numeric_common_restrictions reading (reading.atPrecision precision)).1, ih]

theorem reading_precision_bounds_every_window {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precision : Precision) :
    ReadingSpansBounded precision (refineReadingPrecision readings precision).fine := by
  induction readings with
  | nil => exact True.intro
  | @cons clause rest reading tail ih =>
    refine ⟨?_, ih⟩
    have bound := (window_intersection_right clause.window (ReadingWindow.atPrecision reading.value precision)).span_le
    rw [precision_window_span] at bound
    exact bound

theorem refinement_preserves_all_ports {coarse fine}
    (refinement : ReadingConstraintRefinement coarse fine) :
    fine.map AttachedReadingConstraint.port = coarse.map AttachedReadingConstraint.port := by
  induction refinement with
  | nil => rfl
  | cons first tail ih => exact congrArg (List.cons _) ih

def RealizedReadingRefinement.prolong {source pair head current target attached clauses}
    (refined : @RealizedReadingRefinement source pair head current attached clauses)
    (history : RecurringHistory current target) : RealizedReadingRefinement (attached.prolong history) clauses :=
  ⟨refined.fine, refined.refinement, refined.readings.prolong history⟩

def RealizedReadingRefinement.transport {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (refined : RealizedReadingRefinement one clauses) : RealizedReadingRefinement two clauses :=
  ⟨refined.fine, refined.refinement, refined.readings.transport agreement⟩

theorem reading_precision_prolong_square {source pair head current target attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precision : Precision)
    (history : RecurringHistory current target) :
    (refineReadingPrecision readings precision).prolong history =
      refineReadingPrecision (readings.prolong history) precision := by
  induction readings with
  | nil => rfl
  | @cons clause rest reading tail ih =>
    exact congrArg (fun suffix : RealizedReadingRefinement (attached.prolong history) rest =>
      RealizedReadingRefinement.mk
        (⟨clause.port, clause.window.intersection (ReadingWindow.atPrecision reading.value precision)⟩ :: suffix.fine)
        (ReadingConstraintRefinement.cons (window_intersection_left _ _) suffix.refinement)
        (CertifiedReadingConstraints.cons
          ((reading.common (reading.atPrecision precision)).prolong history) suffix.readings)) ih

theorem reading_precision_transport_square {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (readings : CertifiedReadingConstraints one clauses) (precision : Precision) :
    (refineReadingPrecision readings precision).transport agreement =
      refineReadingPrecision (readings.transport agreement) precision := by
  induction readings with
  | nil => rfl
  | @cons clause rest reading tail ih =>
    exact congrArg (fun suffix : RealizedReadingRefinement two rest =>
      RealizedReadingRefinement.mk
        (⟨clause.port, clause.window.intersection (ReadingWindow.atPrecision reading.value precision)⟩ :: suffix.fine)
        (ReadingConstraintRefinement.cons (window_intersection_left _ _) suffix.refinement)
        (CertifiedReadingConstraints.cons
          ((reading.common (reading.atPrecision precision)).transport agreement) suffix.readings)) ih

theorem constraint_refinement_identity_left {coarse fine}
    (refinement : ReadingConstraintRefinement coarse fine) :
    (ReadingConstraintRefinement.identity coarse).compose refinement = refinement := by
  induction refinement with
  | nil => rfl
  | cons first tail ih => exact congrArg (ReadingConstraintRefinement.cons first) ih

theorem constraint_refinement_identity_right {coarse fine}
    (refinement : ReadingConstraintRefinement coarse fine) :
    refinement.compose (.identity fine) = refinement := by
  induction refinement with
  | nil => rfl
  | cons first tail ih => exact congrArg (ReadingConstraintRefinement.cons first) ih

theorem constraint_refinement_associates {one two three four}
    (first : ReadingConstraintRefinement one two) (second : ReadingConstraintRefinement two three)
    (third : ReadingConstraintRefinement three four) :
    (first.compose second).compose third = first.compose (second.compose third) := by
  induction first generalizing three four with
  | nil => cases second; cases third; rfl
  | cons next rest ih => cases second with
    | cons middle tail => cases third with
      | cons last suffix =>
        exact congrArg (ReadingConstraintRefinement.cons ((next.compose middle).compose last)) (ih tail suffix)

theorem realized_refinement_identity_left {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (refined : RealizedReadingRefinement attached clauses) :
    (RealizedReadingRefinement.identity readings).compose refined = refined := by
  cases refined with | mk fine refinement result =>
    change RealizedReadingRefinement.mk fine ((ReadingConstraintRefinement.identity clauses).compose refinement) result = _
    rw [constraint_refinement_identity_left]

theorem realized_refinement_identity_right {source pair head current attached clauses}
    (refined : @RealizedReadingRefinement source pair head current attached clauses) :
    refined.compose (.identity refined.readings) = refined := by
  cases refined with | mk fine refinement result =>
    change RealizedReadingRefinement.mk fine (refinement.compose (.identity fine)) result = _
    rw [constraint_refinement_identity_right]

theorem realized_refinement_associates {source pair head current attached clauses}
    (first : @RealizedReadingRefinement source pair head current attached clauses)
    (second : RealizedReadingRefinement attached first.fine)
    (third : RealizedReadingRefinement attached second.fine) :
    (first.compose second).compose third = first.compose (second.compose third) := by
  change RealizedReadingRefinement.mk third.fine
    ((first.refinement.compose second.refinement).compose third.refinement) third.readings = _
  rw [constraint_refinement_associates]
  rfl

theorem realized_refinement_prolong_composes {source pair head current target attached clauses}
    (first : @RealizedReadingRefinement source pair head current attached clauses)
    (second : RealizedReadingRefinement attached first.fine) (history : RecurringHistory current target) :
    (first.compose second).prolong history = (first.prolong history).compose (second.prolong history) := rfl

theorem realized_refinement_transport_composes {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (first : RealizedReadingRefinement one clauses) (second : RealizedReadingRefinement one first.fine) :
    (first.compose second).transport agreement =
      (first.transport agreement).compose (second.transport agreement) := rfl

/-- Descriptive requests, not future instructions to an earlier producer.
The head's two inputs are the received certificates and the current precision;
the suffix receives the head's computed certificates. -/
def refineReadingPrecisions {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (precisions : List Precision) : RealizedReadingRefinement attached clauses :=
  match precisions with
  | [] => .identity readings
  | precision :: rest =>
    let next := refineReadingPrecision readings precision
    let suffix := refineReadingPrecisions next.readings rest
    next.compose suffix
termination_by structural precisions

theorem precision_run_consumes_the_produced_readings {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (precision : Precision) (rest : List Precision) :
    refineReadingPrecisions readings (precision :: rest) =
      let next := refineReadingPrecision readings precision
      next.compose (refineReadingPrecisions next.readings rest) := rfl

theorem precision_run_restricts_exactly {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precisions : List Precision) :
    (refineReadingPrecisions readings precisions).readings.restrict
      (refineReadingPrecisions readings precisions).refinement = readings := by
  induction precisions generalizing clauses with
  | nil => exact constraint_restriction_identity readings
  | cons precision rest ih =>
    change ((refineReadingPrecisions (refineReadingPrecision readings precision).readings rest).readings).restrict
      ((refineReadingPrecision readings precision).refinement.compose
        (refineReadingPrecisions (refineReadingPrecision readings precision).readings rest).refinement) = _
    rw [← constraint_restriction_composes, ih, reading_precision_restricts_exactly]

theorem precision_run_keeps_values {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precisions : List Precision) :
    (refineReadingPrecisions readings precisions).readings.values = readings.values := by
  have exactReturn := congrArg CertifiedReadingConstraints.values (precision_run_restricts_exactly readings precisions)
  rw [constraint_restriction_values] at exactReturn
  exact exactReturn

theorem precision_run_keeps_ports {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precisions : List Precision) :
    (refineReadingPrecisions readings precisions).fine.map AttachedReadingConstraint.port =
      clauses.map AttachedReadingConstraint.port :=
  refinement_preserves_all_ports (refineReadingPrecisions readings precisions).refinement

theorem span_bounds_survive_refinement {coarse fine}
    (refinement : ReadingConstraintRefinement coarse fine) (precision : Precision)
    (bounded : ReadingSpansBounded precision coarse) : ReadingSpansBounded precision fine := by
  induction refinement with
  | nil => exact True.intro
  | cons first tail ih => exact ⟨Rational.le_trans first.span_le bounded.1, ih bounded.2⟩

theorem precision_run_bounds_every_requested_precision {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (precisions : List Precision) (precision : Precision) (requested : precision ∈ precisions) :
    ReadingSpansBounded precision (refineReadingPrecisions readings precisions).fine := by
  induction precisions generalizing clauses with
  | nil => cases requested
  | cons first rest ih =>
    cases requested with
    | head =>
      exact span_bounds_survive_refinement
        (refineReadingPrecisions (refineReadingPrecision readings precision).readings rest).refinement precision
        (reading_precision_bounds_every_window readings precision)
    | tail _ inRest => exact ih (refineReadingPrecision readings first).readings inRest

theorem precision_runs_append {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (first second : List Precision) :
    refineReadingPrecisions readings (first ++ second) =
      (refineReadingPrecisions readings first).compose
        (refineReadingPrecisions (refineReadingPrecisions readings first).readings second) := by
  induction first generalizing clauses with
  | nil => exact (realized_refinement_identity_left readings _).symm
  | cons precision rest ih =>
    change (refineReadingPrecision readings precision).compose
      (refineReadingPrecisions (refineReadingPrecision readings precision).readings (rest ++ second)) = _
    rw [ih, ← realized_refinement_associates]
    rfl

/-- A caller can resume the returned result without repeating its prefix. -/
def RealizedReadingRefinement.resume {source pair head current attached clauses}
    (refined : @RealizedReadingRefinement source pair head current attached clauses) (precisions : List Precision) :
    RealizedReadingRefinement attached clauses :=
  refined.compose (refineReadingPrecisions refined.readings precisions)

theorem precision_resume_returns_its_input {source pair head current attached clauses}
    (refined : @RealizedReadingRefinement source pair head current attached clauses) (precisions : List Precision) :
    (refined.resume precisions).readings.restrict (refined.resume precisions).refinement =
      refined.readings.restrict refined.refinement := by
  change (refineReadingPrecisions refined.readings precisions).readings.restrict
    (refined.refinement.compose (refineReadingPrecisions refined.readings precisions).refinement) = _
  rw [← constraint_restriction_composes, precision_run_restricts_exactly]

theorem precision_resume_associates {source pair head current attached clauses}
    (refined : @RealizedReadingRefinement source pair head current attached clauses) (first second : List Precision) :
    (refined.resume first).resume second = refined.resume (first ++ second) := by
  unfold RealizedReadingRefinement.resume
  rw [precision_runs_append]
  exact realized_refinement_associates refined (refineReadingPrecisions refined.readings first)
    (refineReadingPrecisions (refineReadingPrecisions refined.readings first).readings second)

theorem precision_run_last_bound {source pair head current attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses)
    (earlier : List Precision) (precision : Precision) :
    ReadingSpansBounded precision (refineReadingPrecisions readings (earlier ++ [precision])).fine := by
  rw [precision_runs_append]
  exact reading_precision_bounds_every_window (refineReadingPrecisions readings earlier).readings precision

theorem precision_run_prolong_square {source pair head current target attached clauses}
    (readings : @CertifiedReadingConstraints source pair head current attached clauses) (precisions : List Precision)
    (history : RecurringHistory current target) :
    (refineReadingPrecisions readings precisions).prolong history =
      refineReadingPrecisions (readings.prolong history) precisions := by
  induction precisions generalizing clauses with
  | nil => rfl
  | cons precision rest ih =>
    change ((refineReadingPrecision readings precision).compose
      (refineReadingPrecisions (refineReadingPrecision readings precision).readings rest)).prolong history = _
    rw [realized_refinement_prolong_composes]
    exact (congrArg
      (fun suffix : RealizedReadingRefinement (attached.prolong history)
          (refineReadingPrecision readings precision).fine =>
        ((refineReadingPrecision readings precision).prolong history).compose suffix)
      (ih (refineReadingPrecision readings precision).readings)).trans
      (congrArg (fun refined : RealizedReadingRefinement (attached.prolong history) clauses =>
        refined.compose (refineReadingPrecisions refined.readings rest))
        (reading_precision_prolong_square readings precision history))

theorem precision_run_transport_square {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (readings : CertifiedReadingConstraints one clauses) (precisions : List Precision) :
    (refineReadingPrecisions readings precisions).transport agreement =
      refineReadingPrecisions (readings.transport agreement) precisions := by
  induction precisions generalizing clauses with
  | nil => rfl
  | cons precision rest ih =>
    change ((refineReadingPrecision readings precision).compose
      (refineReadingPrecisions (refineReadingPrecision readings precision).readings rest)).transport agreement = _
    rw [realized_refinement_transport_composes]
    exact (congrArg
      (fun suffix : RealizedReadingRefinement two (refineReadingPrecision readings precision).fine =>
        ((refineReadingPrecision readings precision).transport agreement).compose suffix)
      (ih (refineReadingPrecision readings precision).readings)).trans
      (congrArg (fun refined : RealizedReadingRefinement two clauses =>
        refined.compose (refineReadingPrecisions refined.readings rest))
        (reading_precision_transport_square agreement readings precision))

theorem realized_refinement_continuation_square {source pair head current target one two clauses}
    (agreement : @AttachedDescriptionAgreement source pair head current target one two)
    (extension : SharedDescriptionExtension agreement.raccord) (refined : RealizedReadingRefinement one clauses) :
    (refined.prolong extension.execution.first.history).transport (extension.rich agreement) =
      (refined.transport agreement).prolong extension.execution.second.history := by
  exact congrArg (RealizedReadingRefinement.mk refined.fine refined.refinement)
    (constraint_continuation_square agreement extension refined.readings)

/-- The selected cover's certificates are consumed directly. No chooser is
called again and no instrumental production is reconstructed. -/
def CoveredReadingConstraints.precise {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) (precisions : List Precision) :
    RealizedReadingRefinement attached clauses :=
  let refined := refineReadingPrecisions chosen.refined precisions
  ⟨refined.fine, chosen.refinement.compose refined.refinement, refined.readings⟩

theorem covered_precisions_return_the_selected_source {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover) (precisions : List Precision) :
    (chosen.precise precisions).readings.restrict (chosen.precise precisions).refinement = chosen.restrict := by
  change (refineReadingPrecisions chosen.refined precisions).readings.restrict
    (chosen.refinement.compose (refineReadingPrecisions chosen.refined precisions).refinement) = _
  rw [← constraint_restriction_composes, precision_run_restricts_exactly, joint_refined_restriction]

theorem covered_precisions_last_bound {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (earlier : List Precision) (precision : Precision) :
    ReadingSpansBounded precision (chosen.precise (earlier ++ [precision])).fine :=
  precision_run_last_bound chosen.refined earlier precision

theorem covered_precisions_bound_every_request {source pair head current attached clauses cover}
    (chosen : @CoveredReadingConstraints source pair head current attached clauses cover)
    (precisions : List Precision) (precision : Precision) (requested : precision ∈ precisions) :
    ReadingSpansBounded precision (chosen.precise precisions).fine :=
  precision_run_bounds_every_requested_precision chosen.refined precisions precision requested

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.reading_precision_positive
#print axioms RelationalPerimeter.Relativity.Production.ReadingWindow.atPrecision
#print axioms RelationalPerimeter.Relativity.Production.precision_window_contains
#print axioms RelationalPerimeter.Relativity.Production.precision_window_span
#print axioms RelationalPerimeter.Relativity.Production.CertifiedNumericReading.atPrecision
#print axioms RelationalPerimeter.Relativity.Production.ReadingSpansBounded
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement.identity
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement.compose
#print axioms RelationalPerimeter.Relativity.Production.refineReadingPrecision
#print axioms RelationalPerimeter.Relativity.Production.reading_precision_restricts_exactly
#print axioms RelationalPerimeter.Relativity.Production.reading_precision_bounds_every_window
#print axioms RelationalPerimeter.Relativity.Production.refinement_preserves_all_ports
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement.prolong
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement.transport
#print axioms RelationalPerimeter.Relativity.Production.reading_precision_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.reading_precision_transport_square
#print axioms RelationalPerimeter.Relativity.Production.constraint_refinement_identity_left
#print axioms RelationalPerimeter.Relativity.Production.constraint_refinement_identity_right
#print axioms RelationalPerimeter.Relativity.Production.constraint_refinement_associates
#print axioms RelationalPerimeter.Relativity.Production.realized_refinement_identity_left
#print axioms RelationalPerimeter.Relativity.Production.realized_refinement_identity_right
#print axioms RelationalPerimeter.Relativity.Production.realized_refinement_associates
#print axioms RelationalPerimeter.Relativity.Production.realized_refinement_prolong_composes
#print axioms RelationalPerimeter.Relativity.Production.realized_refinement_transport_composes
#print axioms RelationalPerimeter.Relativity.Production.refineReadingPrecisions
#print axioms RelationalPerimeter.Relativity.Production.precision_run_consumes_the_produced_readings
#print axioms RelationalPerimeter.Relativity.Production.precision_run_restricts_exactly
#print axioms RelationalPerimeter.Relativity.Production.precision_run_keeps_values
#print axioms RelationalPerimeter.Relativity.Production.precision_run_keeps_ports
#print axioms RelationalPerimeter.Relativity.Production.span_bounds_survive_refinement
#print axioms RelationalPerimeter.Relativity.Production.precision_run_bounds_every_requested_precision
#print axioms RelationalPerimeter.Relativity.Production.precision_runs_append
#print axioms RelationalPerimeter.Relativity.Production.RealizedReadingRefinement.resume
#print axioms RelationalPerimeter.Relativity.Production.precision_resume_returns_its_input
#print axioms RelationalPerimeter.Relativity.Production.precision_resume_associates
#print axioms RelationalPerimeter.Relativity.Production.precision_run_last_bound
#print axioms RelationalPerimeter.Relativity.Production.precision_run_prolong_square
#print axioms RelationalPerimeter.Relativity.Production.precision_run_transport_square
#print axioms RelationalPerimeter.Relativity.Production.realized_refinement_continuation_square
#print axioms RelationalPerimeter.Relativity.Production.CoveredReadingConstraints.precise
#print axioms RelationalPerimeter.Relativity.Production.covered_precisions_return_the_selected_source
#print axioms RelationalPerimeter.Relativity.Production.covered_precisions_last_bound
#print axioms RelationalPerimeter.Relativity.Production.covered_precisions_bound_every_request
/- AXIOM_AUDIT_END -/
