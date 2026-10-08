import RelationalPerimeter

/-! Numerical descriptions consume stored constituted ports. Resolution,
actual production, source identity and path effects remain separate. -/
set_option genInjectivity false
namespace Tests.Relativity.NumericWindowChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def arrivals (count : Nat) : (source : Cursor) ×' ArrivalPair source :=
  let supplied := Cursor.received { input with reading := Rational.ofNat count }
  let emitted := (perform supplied emission).successor
  let first := perform emitted (.receive .here)
  let second := perform first.successor (.receive (.prior .here))
  ⟨second.successor, ⟨.prior .here, .here, .prior (.prior .here), .prior (.prior .here),
    .inherited second.determination.2 (arrivalOfProduction first), arrivalOfProduction second,
    fun same => fresh_distinct first.successor second.determination .here same.symm⟩⟩

def origin (count : Nat) : RecurringCursor := .fromCursor (arrivals count).1

def pair (count : Nat) : RecurringPair (origin count) :=
  let data := (arrivals count).2
  ⟨data.first, data.second, data.firstSignal, data.secondSignal,
    .fromCursor data.firstArrival, .fromCursor data.secondArrival, data.distinct⟩

def head (count : Nat) := performRecurring (origin count) (.compare (pair count))
def participant (count : Nat) := InteractionAttachment.first (head count) .root
def partner (count : Nat) := InteractionAttachment.second (head count) .root

def coarse : ReadingWindow := ⟨Rational.neg Rational.one, Rational.ofNat 3⟩
def left : ReadingWindow := ⟨Rational.zero, Rational.ofNat 3⟩
def right : ReadingWindow := ⟨Rational.neg Rational.one, Rational.ofNat 2⟩
def narrow : ReadingWindow := ⟨Rational.zero, Rational.ofNat 2⟩
def boundary : ReadingWindow := ⟨Rational.zero, Rational.one⟩
def reversed : ReadingWindow := ⟨Rational.ofNat 2, Rational.zero⟩
def aroundComparison : ReadingWindow := ⟨Rational.neg Rational.one, Rational.one⟩

theorem left_refines_coarse : WindowRefinement coarse left :=
  ⟨by decide, Rational.le_refl _⟩

theorem right_refines_coarse : WindowRefinement coarse right :=
  ⟨Rational.le_refl _, by decide⟩

theorem arrival_is_stored_one : attachedNumericReading (participant 1) .arrival = Rational.one := rfl
theorem comparison_is_stored_zero : attachedNumericReading (participant 1) .interaction = Rational.zero := rfl
theorem other_execution_is_stored_two : attachedNumericReading (participant 2) .arrival = Rational.ofNat 2 := rfl

theorem first_window_admitted : numericWindowAdmitted (participant 1) .arrival left = true := rfl
theorem complementary_window_admitted : numericWindowAdmitted (participant 1) .arrival right = true := rfl
theorem refined_window_admitted : numericWindowAdmitted (participant 1) .arrival narrow = true := rfl
theorem changed_reading_refused : numericWindowAdmitted (participant 2) .arrival narrow = false := rfl
theorem upper_boundary_refused : numericWindowAdmitted (participant 1) .arrival boundary = false := rfl
theorem lower_boundary_refused : numericWindowAdmitted (participant 1) .interaction boundary = false := rfl
theorem inverted_window_refused : numericWindowAdmitted (participant 1) .arrival reversed = false := rfl
theorem comparison_port_admitted : numericWindowAdmitted (participant 1) .interaction aroundComparison = true := rfl
theorem arrival_is_not_the_comparison : numericWindowAdmitted (participant 1) .arrival aroundComparison = false := rfl

def firstReading := certifiedNumericReadingOfAdmitted (participant 1) .arrival left first_window_admitted
def secondReading := certifiedNumericReadingOfAdmitted (participant 1) .arrival right complementary_window_admitted
def common := firstReading.common secondReading

theorem first_certificate_is_executed_output :
    certifyNumericReading (participant 1) .arrival left = .inl firstReading :=
  admitted_certificate_is_the_decision_output (participant 1) .arrival left first_window_admitted

theorem common_is_the_narrow_window : left.intersection right = narrow := rfl
theorem common_has_both_restrictions :
    common.restrict (window_intersection_left left right) = firstReading ∧
      common.restrict (window_intersection_right left right) = secondReading :=
  numeric_common_restrictions firstReading secondReading

theorem error_bounds_are_certified :
    Rational.Le Rational.zero (Rational.sub common.value narrow.lower) ∧
      Rational.Le (Rational.sub common.value narrow.lower) narrow.span ∧
      Rational.Le Rational.zero (Rational.sub narrow.upper common.value) ∧
      Rational.Le (Rational.sub narrow.upper common.value) narrow.span :=
  certified_numeric_error_bounds common

theorem actual_resolution_improves : RationalStrictLess narrow.span coarse.span := by decide

theorem restriction_preserves_the_produced_value :
    (firstReading.restrict left_refines_coarse).value = Rational.one := rfl

theorem same_numeric_reading_keeps_distinct_sources :
    attachedNumericReading (participant 1) .arrival = attachedNumericReading (partner 1) .arrival ∧
      (participant 1).readingReference ≠ (partner 1).readingReference :=
  ⟨rfl, participants_remain_distinct (head 1) DescriptionPath.root⟩

theorem prescribed_value_cannot_be_certified (reading : CertifiedNumericReading (participant 1) .arrival left)
    (wrong : reading.value = Rational.ofNat 2) : False :=
  (by decide : Rational.one ≠ Rational.ofNat 2)
    ((reading.valueExact.trans arrival_is_stored_one).symm.trans wrong)

def agreement := AttachedDescriptionAgreement.identity (participant 1)
def requests : List RecurringRequest :=
  [.local (.inspect .reading (participant 1).readingReference.position),
   .compare (participant 1).readingReference.position (partner 1).readingReference.position,
   .compare 0 0]

@[irreducible] def extension := runDescriptionExtension agreement.raccord requests
def continued := firstReading.prolong extension.execution.first.history
def transported := continued.transport (extension.rich agreement)

theorem extension_is_actual : extension = runDescriptionExtension agreement.raccord requests := by
  unfold extension; rfl

theorem one_new_production : StrongPerimetralTurning.History.length extension.execution.first.history = 1 := by
  rw [extension_is_actual]
  change StrongPerimetralTurning.History.length (runSharedRecurring agreement.raccord requests).first.history = 1
  rw [(shared_recurring_runners_exact agreement.raccord requests).1]
  rfl

theorem continuation_value_is_the_cached_value : continued.value = firstReading.value := rfl
theorem transported_value_is_the_cached_value : transported.value = firstReading.value := rfl

theorem continuation_and_change_commute : transported =
    (firstReading.transport agreement).prolong extension.execution.second.history :=
  numeric_continuation_square agreement extension firstReading

theorem continuation_and_resolution_commute :
    (firstReading.restrict left_refines_coarse).prolong extension.execution.first.history =
      continued.restrict left_refines_coarse :=
  numeric_prolong_restriction_square firstReading extension.execution.first.history left_refines_coarse

theorem all_future_suffixes_preserve_admission (future : List RecurringRequest) :
    numericWindowAdmitted ((extension.resume future).first (extension.first (participant 1))) .arrival narrow =
      numericWindowAdmitted (participant 1) .arrival narrow :=
  (numeric_admission_prolong _ _ _ _).trans (numeric_admission_prolong _ _ _ _)

theorem the_full_contract_is_unchanged : extension.execution.first.report =
    recurringContract.outcome (head 1).successor requests := by
  rw [extension_is_actual]
  exact (description_extension_reports_exact agreement.raccord requests).1

theorem initial_participants_are_not_comparison_anchor :
    (participant 1).anchor ≠ (participant 1).readingReference := attached_anchor_not_arrival _

end Tests.Relativity.NumericWindowChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.NumericWindowChecks.arrivals
#print axioms Tests.Relativity.NumericWindowChecks.pair
#print axioms Tests.Relativity.NumericWindowChecks.head
#print axioms Tests.Relativity.NumericWindowChecks.left_refines_coarse
#print axioms Tests.Relativity.NumericWindowChecks.right_refines_coarse
#print axioms Tests.Relativity.NumericWindowChecks.arrival_is_stored_one
#print axioms Tests.Relativity.NumericWindowChecks.comparison_is_stored_zero
#print axioms Tests.Relativity.NumericWindowChecks.other_execution_is_stored_two
#print axioms Tests.Relativity.NumericWindowChecks.first_window_admitted
#print axioms Tests.Relativity.NumericWindowChecks.complementary_window_admitted
#print axioms Tests.Relativity.NumericWindowChecks.refined_window_admitted
#print axioms Tests.Relativity.NumericWindowChecks.changed_reading_refused
#print axioms Tests.Relativity.NumericWindowChecks.upper_boundary_refused
#print axioms Tests.Relativity.NumericWindowChecks.lower_boundary_refused
#print axioms Tests.Relativity.NumericWindowChecks.inverted_window_refused
#print axioms Tests.Relativity.NumericWindowChecks.comparison_port_admitted
#print axioms Tests.Relativity.NumericWindowChecks.arrival_is_not_the_comparison
#print axioms Tests.Relativity.NumericWindowChecks.firstReading
#print axioms Tests.Relativity.NumericWindowChecks.secondReading
#print axioms Tests.Relativity.NumericWindowChecks.common
#print axioms Tests.Relativity.NumericWindowChecks.first_certificate_is_executed_output
#print axioms Tests.Relativity.NumericWindowChecks.common_is_the_narrow_window
#print axioms Tests.Relativity.NumericWindowChecks.common_has_both_restrictions
#print axioms Tests.Relativity.NumericWindowChecks.error_bounds_are_certified
#print axioms Tests.Relativity.NumericWindowChecks.actual_resolution_improves
#print axioms Tests.Relativity.NumericWindowChecks.restriction_preserves_the_produced_value
#print axioms Tests.Relativity.NumericWindowChecks.same_numeric_reading_keeps_distinct_sources
#print axioms Tests.Relativity.NumericWindowChecks.prescribed_value_cannot_be_certified
#print axioms Tests.Relativity.NumericWindowChecks.extension
#print axioms Tests.Relativity.NumericWindowChecks.extension_is_actual
#print axioms Tests.Relativity.NumericWindowChecks.one_new_production
#print axioms Tests.Relativity.NumericWindowChecks.continued
#print axioms Tests.Relativity.NumericWindowChecks.transported
#print axioms Tests.Relativity.NumericWindowChecks.continuation_value_is_the_cached_value
#print axioms Tests.Relativity.NumericWindowChecks.transported_value_is_the_cached_value
#print axioms Tests.Relativity.NumericWindowChecks.continuation_and_change_commute
#print axioms Tests.Relativity.NumericWindowChecks.continuation_and_resolution_commute
#print axioms Tests.Relativity.NumericWindowChecks.all_future_suffixes_preserve_admission
#print axioms Tests.Relativity.NumericWindowChecks.the_full_contract_is_unchanged
#print axioms Tests.Relativity.NumericWindowChecks.initial_participants_are_not_comparison_anchor
/- AXIOM_AUDIT_END -/
