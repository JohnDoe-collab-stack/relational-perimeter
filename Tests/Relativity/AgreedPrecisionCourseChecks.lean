import RelationalPerimeter

/-! Closed public clients for agreement courses between actually produced
neighboring families. Only the empty-course evaluation is a finite smoke.
No cost, physical localization or equality of source histories is claimed. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.AgreedPrecisionCourseChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl

def leftSource : RelativePathState := (refineRelativePaths initial .lower).state
def rightSource : RelativePathState := (refineRelativePaths initial .upper).state

def first : RelativePathPresentation leftSource := RelativePathPresentation.fromState _ .upper
def second : RelativePathPresentation rightSource := RelativePathPresentation.fromState _ .lower

def agreement : Agreement first.numeric second.numeric := relative_children_boundary_agreement initial

def initialWindow : ReadingWindow := ⟨Rational.neg (Rational.ofNat 2), Rational.ofNat 5⟩

def firstCertificate : ProductiveWindowCertificate first initialWindow :=
  first.initialWindow.restrict ⟨by decide, by decide⟩

def secondCertificate : ProductiveWindowCertificate second initialWindow :=
  second.initialWindow.restrict ⟨by decide, by decide⟩

def firstCourse (requests : List Precision) := firstCertificate.runPrecisions requests
def matchedCourse (requests : List Precision) :=
  (firstCourse requests).matchAgreed secondCertificate agreement

theorem initial_readings_remain_distinct :
    first.stored.state.reading.value ≠ second.stored.state.reading.value :=
  relative_subdivision_choices_have_different_readings initial

theorem every_matching_course_starts_from_its_received_second_prefix (requests : List Precision) :
    (matchedCourse requests).endpoint.realization =
      secondCertificate.realization.evolve second.rule (matchedCourse requests).steps :=
  (matchedCourse requests).runExact

theorem every_matching_course_records_its_actual_depth (requests : List Precision) :
    (matchedCourse requests).endpoint.depth =
      secondCertificate.depth + (matchedCourse requests).steps :=
  (matchedCourse requests).depthExact

theorem response_certifies_exactly_the_source_endpoint_window (requests : List Precision) :
    (firstCourse requests).endpoint.window.BracketContains
      (matchedCourse requests).endpoint.realization.state.reading :=
  (matchedCourse requests).endpoint.inside

theorem every_later_second_reading_keeps_the_initial_constraint (requests : List Precision)
    (index : Nat) (enough : (matchedCourse requests).endpoint.depth ≤ index) :
    initialWindow.Contains (second.numeric.approximate index) :=
  (matchedCourse requests).noLaterEscape index enough

theorem both_later_readings_use_the_same_window (requests : List Precision) (left right : Nat)
    (leftEnough : (firstCourse requests).endpoint.certificate.depth ≤ left)
    (rightEnough : (matchedCourse requests).endpoint.depth ≤ right) :
    (firstCourse requests).endpoint.window.Contains (first.numeric.approximate left) ∧
      (firstCourse requests).endpoint.window.Contains (second.numeric.approximate right) :=
  ⟨productive_certificate_all_later_indices (firstCourse requests).endpoint.certificate left leftEnough,
    productive_certificate_all_later_indices (matchedCourse requests).endpoint right rightEnough⟩

theorem requested_precision_controls_both_futures (precision : Precision) (left right : Nat)
    (leftEnough : (firstCourse [precision]).endpoint.certificate.depth ≤ left)
    (rightEnough : (matchedCourse [precision]).endpoint.depth ≤ right) :
    Close (first.numeric.approximate left) (second.numeric.approximate right) precision.value :=
  ((matchedCourse [precision]).comparison precision
    (firstCertificate.continuePrecision precision).diameter).allLaterClose left right leftEnough rightEnough

theorem the_matching_head_does_not_receive_the_future (precision : Precision) (one two : List Precision) :
    (matchedCourse (precision :: one)).headProduction =
      (matchedCourse (precision :: two)).headProduction :=
  productive_agreed_course_head_horizon_independent _ _ _ _ _ _

theorem every_matching_course_keeps_second_sources_distinct (requests : List Precision) :
    (historyTransport (matchedCourse requests).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.first ≠
      (historyTransport (matchedCourse requests).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem every_matching_course_keeps_second_source_record (requests : List Precision) :
    (matchedCourse requests).endpoint.realization.state.cursor.read
      ((historyTransport (matchedCourse requests).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.secondSignal) = rightSource.cursor.read rightSource.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

theorem the_received_first_course_keeps_its_own_sources (requests : List Precision) :
    (historyTransport (firstCourse requests).endpoint.certificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (firstCourse requests).endpoint.certificate.realization.chain.history).references
        leftSource.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem the_empty_matching_course_reuses_its_entire_certificate :
    (matchedCourse []).endpoint = secondCertificate := rfl

def continued (firstRequests more : List Precision) :=
  (matchedCourse firstRequests).continue more agreement

theorem continuing_uses_the_returned_second_endpoint (firstRequests more : List Precision) :
    (continued firstRequests more).endpoint.realization =
      (matchedCourse firstRequests).endpoint.realization.evolve second.rule (continued firstRequests more).steps :=
  productive_agreed_continued_run_exact _ _ _

theorem continuing_uses_the_returned_first_endpoint (firstRequests more : List Precision) :
    ((firstCourse firstRequests).endpoint.certificate.runPrecisions more).endpoint.certificate.realization =
      (firstCourse firstRequests).endpoint.certificate.realization.evolve first.rule (precisionCourseSteps more) :=
  ProductivePrecisionCourse.runExact _

theorem continued_matching_keeps_second_sources_distinct (firstRequests more : List Precision) :
    (historyTransport (continued firstRequests more).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.first ≠
      (historyTransport (continued firstRequests more).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem a_coarser_second_request_cannot_reopen_a_finer_window (fine coarse : Precision) :
    WindowRefinement (firstCertificate.continuePrecision fine).window
      ((firstCourse [fine, coarse]).endpoint.window) :=
  ((firstCertificate.continuePrecision fine).certificate.continuePrecision coarse).refinement

theorem matching_never_returns_a_zero_width_window (requests : List Precision) :
    (firstCourse requests).endpoint.window.span ≠ Rational.zero :=
  (contained_window_has_positive_span
    (bracket_contains_endpoints (matchedCourse requests).endpoint.inside).1).2

def emptySmoke : Nat := (matchedCourse []).endpoint.depth
#eval emptySmoke

end Tests.Relativity.AgreedPrecisionCourseChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.input
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.initial
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.leftSource
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.rightSource
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.first
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.second
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.agreement
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.initialWindow
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.firstCertificate
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.secondCertificate
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.firstCourse
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.matchedCourse
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.initial_readings_remain_distinct
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.every_matching_course_starts_from_its_received_second_prefix
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.every_matching_course_records_its_actual_depth
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.response_certifies_exactly_the_source_endpoint_window
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.every_later_second_reading_keeps_the_initial_constraint
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.both_later_readings_use_the_same_window
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.requested_precision_controls_both_futures
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.the_matching_head_does_not_receive_the_future
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.every_matching_course_keeps_second_sources_distinct
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.every_matching_course_keeps_second_source_record
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.the_received_first_course_keeps_its_own_sources
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.the_empty_matching_course_reuses_its_entire_certificate
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.continued
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.continuing_uses_the_returned_second_endpoint
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.continuing_uses_the_returned_first_endpoint
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.continued_matching_keeps_second_sources_distinct
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.a_coarser_second_request_cannot_reopen_a_finer_window
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.matching_never_returns_a_zero_width_window
#print axioms Tests.Relativity.AgreedPrecisionCourseChecks.emptySmoke
/- AXIOM_AUDIT_END -/
