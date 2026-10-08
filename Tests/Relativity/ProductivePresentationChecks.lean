import RelationalPerimeter

/-! Clients of the public productive presentation API. The final closed
evaluation is an executability smoke, not physical or complexity evidence. -/
set_option genInjectivity false
namespace Tests.Relativity.ProductivePresentationChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl

def presentation (rule : RelativeRefinementRule) : RelativePathPresentation initial :=
  RelativePathPresentation.fromState initial rule

theorem every_depth_has_actual_common_origin (rule : RelativeRefinementRule) (n : Nat) :
    ((presentation rule).realize n).state.reading.numerator.origin =
      (historyTransport ((presentation rule).realize n).chain.history).references initial.reading.numerator.origin :=
  relative_presentation_origin _ _

theorem every_depth_keeps_old_and_current_receptions (rule : RelativeRefinementRule) (n : Nat) :
    ((historyTransport ((presentation rule).realize n).chain.history).references initial.reading.arrivals.first ≠
      (historyTransport ((presentation rule).realize n).chain.history).references initial.reading.arrivals.second) ∧
    (((presentation rule).realize n).state.reading.arrivals.first ≠
      ((presentation rule).realize n).state.reading.arrivals.second) :=
  ⟨relative_presentation_sources _ _, ((presentation rule).realize n).state.reading.arrivals.distinct⟩

theorem every_depth_keeps_the_received_record (rule : RelativeRefinementRule) (n : Nat) :
    ((presentation rule).realize n).state.cursor.read
      ((historyTransport ((presentation rule).realize n).chain.history).references initial.reading.arrivals.secondSignal) =
      initial.cursor.read initial.reading.arrivals.secondSignal := history_preserves_reads _ _

theorem resumption_matches_the_complete_returned_result (rule : RelativeRefinementRule) (first second : Nat) :
    ((presentation rule).resume first).realize second = (presentation rule).realize (first + second) :=
  relative_presentation_resume_exact ..

theorem numerical_approximation_uses_the_produced_reading (rule : RelativeRefinementRule) (n : Nat) :
    (presentation rule).numeric.approximate n = ((presentation rule).realize n).state.reading.value := rfl

theorem every_positive_precision_has_a_positive_realization (rule : RelativeRefinementRule)
    (precision : Analysis.Precision) :
    Rational.Le ((presentation rule).realizePrecision precision).realization.state.reading.resolution
      precision.value := ((presentation rule).realizePrecision precision).bound

theorem arbitrary_depths_obey_the_same_cauchy_budget (rule : RelativeRefinementRule)
    (precision : Analysis.Precision) (n m : Nat)
    (hn : precision.denominator ≤ n) (hm : precision.denominator ≤ m) :
    Analysis.Close ((presentation rule).numeric.approximate n) ((presentation rule).numeric.approximate m)
      precision.value := (presentation rule).numeric.cauchy precision n m hn hm

def agreement_after_any_stored_resume (rule : RelativeRefinementRule) (steps : Nat) :
    Analysis.Agreement (presentation rule).numeric ((presentation rule).resume steps).numeric :=
  (presentation rule).resumptionAgreement steps

theorem local_head_has_no_depth_argument (rule : RelativeRefinementRule) (steps : Nat) :
    (((presentation rule).realize steps).next rule).state =
      (refineRelativePaths ((presentation rule).realize steps).state
        (rule.select ((presentation rule).realize steps).state)).state := relative_evolution_next_exact ..

theorem distinct_controls_act_differently_at_the_same_prefix (steps : Nat) :
    (((presentation .alternating).realize steps).next .lower).state.reading.value ≠
      (((presentation .alternating).realize steps).next .upper).state.reading.value :=
  relative_subdivision_choices_have_different_readings _

theorem lower_control_keeps_its_lower_reading (steps : Nat) :
    (presentation .lower).numeric.approximate steps = initial.reading.value :=
  relative_evolution_lower_endpoint (presentation .lower).stored steps

theorem alternating_first_control_reads_the_received_count :
    RelativeRefinementRule.select .alternating initial = .upper := by
  have count : initial.reading.numerator.relayCount = 0 :=
    (realizeRelativeReading (.received input) .here (.prior .here)
      (.prior (.prior .here)) rfl 0 0).numeratorCount
  unfold RelativeRefinementRule.select
  rw [count]
  rfl

theorem alternating_readout_is_not_constant :
    (presentation .alternating).numeric.approximate 0 ≠
      (presentation .alternating).numeric.approximate 1 :=
  relative_first_upper_reading_differs (presentation .alternating).stored .alternating
    alternating_first_control_reads_the_received_count

def upper_boundary_is_a_constructed_limit :
    Analysis.Agreement (presentation .upper).numeric
      (Analysis.CauchyRepresentation.constant initial.reading.upper) :=
  relative_upper_limit_agreement (presentation .upper).stored

def neighboring_children_have_a_positive_numeric_agreement :
    Analysis.Agreement
      ((RelativePathPresentation.fromState (refineRelativePaths initial .lower).state .upper).numeric)
      ((RelativePathPresentation.fromState (refineRelativePaths initial .upper).state .lower).numeric) :=
  relative_children_boundary_agreement initial

def smoke : Nat × Nat × Nat :=
  let produced := (presentation .alternating).realize 3
  (produced.state.reading.numerator.relayCount, produced.state.reading.denominator.relayCount,
    StrongPerimetralTurning.History.length produced.chain.history)
#eval smoke

end Tests.Relativity.ProductivePresentationChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ProductivePresentationChecks.input
#print axioms Tests.Relativity.ProductivePresentationChecks.initial
#print axioms Tests.Relativity.ProductivePresentationChecks.presentation
#print axioms Tests.Relativity.ProductivePresentationChecks.every_depth_has_actual_common_origin
#print axioms Tests.Relativity.ProductivePresentationChecks.every_depth_keeps_old_and_current_receptions
#print axioms Tests.Relativity.ProductivePresentationChecks.every_depth_keeps_the_received_record
#print axioms Tests.Relativity.ProductivePresentationChecks.resumption_matches_the_complete_returned_result
#print axioms Tests.Relativity.ProductivePresentationChecks.numerical_approximation_uses_the_produced_reading
#print axioms Tests.Relativity.ProductivePresentationChecks.every_positive_precision_has_a_positive_realization
#print axioms Tests.Relativity.ProductivePresentationChecks.arbitrary_depths_obey_the_same_cauchy_budget
#print axioms Tests.Relativity.ProductivePresentationChecks.agreement_after_any_stored_resume
#print axioms Tests.Relativity.ProductivePresentationChecks.local_head_has_no_depth_argument
#print axioms Tests.Relativity.ProductivePresentationChecks.distinct_controls_act_differently_at_the_same_prefix
#print axioms Tests.Relativity.ProductivePresentationChecks.lower_control_keeps_its_lower_reading
#print axioms Tests.Relativity.ProductivePresentationChecks.alternating_first_control_reads_the_received_count
#print axioms Tests.Relativity.ProductivePresentationChecks.alternating_readout_is_not_constant
#print axioms Tests.Relativity.ProductivePresentationChecks.upper_boundary_is_a_constructed_limit
#print axioms Tests.Relativity.ProductivePresentationChecks.neighboring_children_have_a_positive_numeric_agreement
#print axioms Tests.Relativity.ProductivePresentationChecks.smoke
/- AXIOM_AUDIT_END -/
