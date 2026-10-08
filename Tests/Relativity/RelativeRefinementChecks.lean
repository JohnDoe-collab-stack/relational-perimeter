import RelationalPerimeter

/-! Public clients of the productive path refinement. All closed evaluations
are executability smoke checks, not physical measurements or cost evidence. -/
set_option genInjectivity false
namespace Tests.Relativity.RelativeRefinementChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def initial : RelativePathState :=
  let realized := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution realized (.prior (.prior .here)) rfl

def course (requests : List RelativeSubdivision) := runRelativeRefinements initial requests

theorem every_course_keeps_its_emission (requests : List RelativeSubdivision) :
    (course requests).state.reading.numerator.origin =
      (historyTransport (course requests).chain.history).references initial.reading.numerator.origin :=
  relative_refinement_chain_origin _

theorem every_course_keeps_the_initial_sources (requests : List RelativeSubdivision) :
    (historyTransport (course requests).chain.history).references initial.reading.arrivals.first ≠
      (historyTransport (course requests).chain.history).references initial.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem every_course_keeps_the_initial_value (requests : List RelativeSubdivision) :
    (initial.reading.transport (course requests).chain.history).value = initial.reading.value :=
  relative_refinement_chain_keeps_reading _

theorem every_course_keeps_the_initial_path_record (requests : List RelativeSubdivision) :
    (course requests).state.cursor.read
      ((historyTransport (course requests).chain.history).references initial.reading.arrivals.secondSignal) =
      initial.cursor.read initial.reading.arrivals.secondSignal := history_preserves_reads _ _

theorem requests_are_not_reversed (requests : List RelativeSubdivision) :
    (course requests).chain.requests = requests :=
  relative_refinement_requested_order (⟨initial, .root initial⟩ : RelativeRefinementRun initial) requests

theorem resumption_does_not_rebuild_the_prefix (first second : List RelativeSubdivision) :
    (course first).runMore second = course (first ++ second) := relative_refinement_runs_append ..

theorem choices_produce_different_results :
    (refineRelativePaths initial .lower).state.reading.value ≠
      (refineRelativePaths initial .upper).state.reading.value :=
  relative_subdivision_choices_have_different_readings initial

theorem all_finite_courses_have_nested_brackets (requests : List RelativeSubdivision) :
    Rational.Le initial.reading.value (course requests).state.reading.value ∧
      Rational.Le (course requests).state.reading.upper initial.reading.upper :=
  relative_refinement_chain_brackets (course requests).chain

theorem actual_scale_at_every_finite_depth (requests : List RelativeSubdivision) :
    (course requests).state.reading.denominator.relayCount = 2 ^ requests.length := by
  have scale := relative_refinement_chain_scale (course requests).chain
  have initialCount : initial.reading.denominator.relayCount = 1 :=
    (realizeRelativeReading (.received input) .here (.prior .here)
      (.prior (.prior .here)) rfl 0 0).denominatorCount
  rw [initialCount, requests_are_not_reversed, Nat.one_mul] at scale
  exact scale

theorem arbitrary_precision_is_realized (precision : Analysis.Precision)
    (requests : List RelativeSubdivision) (enough : precision.denominator ≤ requests.length) :
    Rational.Le (course requests).state.reading.resolution precision.value :=
  relative_refinement_all_requests_precision (⟨initial, .root initial⟩ : RelativeRefinementRun initial)
    requests precision enough

def precisionWitness (requests : List RelativeSubdivision) (precision : Analysis.Precision) :
    RelativePrecisionRun initial precision := (course requests).refineToPrecision precision

theorem any_positive_precision_has_a_produced_witness (requests : List RelativeSubdivision)
    (precision : Analysis.Precision) :
    Rational.Le (precisionWitness requests precision).realization.state.reading.resolution precision.value :=
  (precisionWitness requests precision).bound

theorem precision_witness_resumes_the_received_prefix (requests : List RelativeSubdivision)
    (precision : Analysis.Precision) :
    (precisionWitness requests precision).realization =
      (course requests).runMore (relativePrecisionRequests precision) := rfl

theorem one_head_halves_the_span (requests : List RelativeSubdivision) (choice : RelativeSubdivision) :
    Rational.add ((course requests).resume choice).state.reading.resolution
      ((course requests).resume choice).state.reading.resolution = (course requests).state.reading.resolution :=
  relative_refinement_halves_span (refineRelativePaths (course requests).state choice)

theorem stored_head_has_no_future_input (requests : List RelativeSubdivision)
    (choice : RelativeSubdivision) :
    ((course requests).resume choice).state = (refineRelativePaths (course requests).state choice).state := rfl

theorem realized_subdivisions_cover_the_numerical_bracket (requests : List RelativeSubdivision)
    (query : Rational) (lower : Rational.Le (course requests).state.reading.value query)
    (upper : Rational.Le query (course requests).state.reading.upper) :
    (Rational.Le ((course requests).resume .lower).state.reading.value query ∧
      Rational.Le query ((course requests).resume .lower).state.reading.upper) ∨
    (Rational.Le ((course requests).resume .upper).state.reading.value query ∧
      Rational.Le query ((course requests).resume .upper).state.reading.upper) :=
  relative_refinement_children_cover (course requests).state query lower upper

def afterOrdinaryContinuation (requests : List RelativeSubdivision)
    (schedule : Program (course requests).state.cursor.kinds) : RelativePathState :=
  let stored := course requests
  let resumed := run stored.state.cursor schedule
  stored.state.prolong resumed.history

theorem arbitrary_ordinary_suffix_keeps_the_ratio (requests : List RelativeSubdivision)
    (schedule : Program (course requests).state.cursor.kinds) :
    (afterOrdinaryContinuation requests schedule).reading.value = (course requests).state.reading.value :=
  (course requests).state.reading.transport_value (run (course requests).state.cursor schedule).history

theorem refining_after_an_ordinary_suffix_keeps_both_old_sources (requests : List RelativeSubdivision)
    (schedule : Program (course requests).state.cursor.kinds) (choice : RelativeSubdivision) :
    (refineRelativePaths (afterOrdinaryContinuation requests schedule) choice).previous.arrivals.first ≠
      (refineRelativePaths (afterOrdinaryContinuation requests schedule) choice).previous.arrivals.second :=
  relative_refinement_keeps_previous_sources _

def smoke : Nat × Nat × Nat :=
  let realized := course [.upper, .lower]
  (realized.state.reading.numerator.relayCount, realized.state.reading.denominator.relayCount,
    StrongPerimetralTurning.History.length realized.chain.history)
#eval smoke

end Tests.Relativity.RelativeRefinementChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.RelativeRefinementChecks.initial
#print axioms Tests.Relativity.RelativeRefinementChecks.course
#print axioms Tests.Relativity.RelativeRefinementChecks.every_course_keeps_its_emission
#print axioms Tests.Relativity.RelativeRefinementChecks.every_course_keeps_the_initial_sources
#print axioms Tests.Relativity.RelativeRefinementChecks.every_course_keeps_the_initial_value
#print axioms Tests.Relativity.RelativeRefinementChecks.every_course_keeps_the_initial_path_record
#print axioms Tests.Relativity.RelativeRefinementChecks.requests_are_not_reversed
#print axioms Tests.Relativity.RelativeRefinementChecks.resumption_does_not_rebuild_the_prefix
#print axioms Tests.Relativity.RelativeRefinementChecks.choices_produce_different_results
#print axioms Tests.Relativity.RelativeRefinementChecks.all_finite_courses_have_nested_brackets
#print axioms Tests.Relativity.RelativeRefinementChecks.actual_scale_at_every_finite_depth
#print axioms Tests.Relativity.RelativeRefinementChecks.arbitrary_precision_is_realized
#print axioms Tests.Relativity.RelativeRefinementChecks.precisionWitness
#print axioms Tests.Relativity.RelativeRefinementChecks.any_positive_precision_has_a_produced_witness
#print axioms Tests.Relativity.RelativeRefinementChecks.precision_witness_resumes_the_received_prefix
#print axioms Tests.Relativity.RelativeRefinementChecks.one_head_halves_the_span
#print axioms Tests.Relativity.RelativeRefinementChecks.stored_head_has_no_future_input
#print axioms Tests.Relativity.RelativeRefinementChecks.realized_subdivisions_cover_the_numerical_bracket
#print axioms Tests.Relativity.RelativeRefinementChecks.afterOrdinaryContinuation
#print axioms Tests.Relativity.RelativeRefinementChecks.arbitrary_ordinary_suffix_keeps_the_ratio
#print axioms Tests.Relativity.RelativeRefinementChecks.refining_after_an_ordinary_suffix_keeps_both_old_sources
#print axioms Tests.Relativity.RelativeRefinementChecks.smoke
/- AXIOM_AUDIT_END -/
