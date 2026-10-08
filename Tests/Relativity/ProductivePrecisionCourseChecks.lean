import RelationalPerimeter

/-! Closed public consumers of successive instrumental precision requests.
The evaluation is a finite executability smoke, never a physical or cost claim. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.ProductivePrecisionCourseChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩

def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl

def family (rule : RelativeRefinementRule) : RelativePathPresentation initial :=
  RelativePathPresentation.fromState initial rule

def course (rule : RelativeRefinementRule) (requests : List Precision) :=
  (family rule).initialWindow.runPrecisions requests

theorem every_course_is_the_actual_forward_extension (rule : RelativeRefinementRule)
    (requests : List Precision) :
    (course rule requests).endpoint.certificate.realization =
      (family rule).stored.evolve rule (precisionCourseSteps requests) :=
  (course rule requests).runExact

theorem every_course_has_the_constructed_depth (rule : RelativeRefinementRule)
    (requests : List Precision) :
    (course rule requests).endpoint.certificate.depth = precisionCourseSteps requests :=
  (course rule requests).depthExact.trans (Nat.zero_add _)

theorem every_course_keeps_the_initial_constraint (rule : RelativeRefinementRule)
    (requests : List Precision) (index : Nat)
    (enough : (course rule requests).endpoint.certificate.depth ≤ index) :
    initial.reading.bracketWindow.Contains ((family rule).numeric.approximate index) :=
  (course rule requests).noLaterEscape index enough

theorem every_course_keeps_the_two_sources_distinct (rule : RelativeRefinementRule)
    (requests : List Precision) :
    (historyTransport (course rule requests).endpoint.certificate.realization.chain.history).references
        initial.reading.arrivals.first ≠
      (historyTransport (course rule requests).endpoint.certificate.realization.chain.history).references
        initial.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem every_course_keeps_the_source_record (rule : RelativeRefinementRule)
    (requests : List Precision) :
    (course rule requests).endpoint.certificate.realization.state.cursor.read
      ((historyTransport (course rule requests).endpoint.certificate.realization.chain.history).references
        initial.reading.arrivals.secondSignal) = initial.cursor.read initial.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

theorem head_never_receives_the_future (rule : RelativeRefinementRule) (precision : Precision)
    (first second : List Precision) :
    (course rule (precision :: first)).headProduction =
      (course rule (precision :: second)).headProduction :=
  productive_precision_head_horizon_independent _ _ _ _

theorem every_local_request_meets_its_precision {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) (precision : Precision) :
    Rational.Le (received.continuePrecision precision).window.span precision.value :=
  (received.continuePrecision precision).diameter

theorem a_coarser_request_cannot_reopen_a_finer_window {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) (fine coarse : Precision) :
    WindowRefinement (received.continuePrecision fine).window
      ((received.continuePrecision fine).certificate.continuePrecision coarse).window :=
  ((received.continuePrecision fine).certificate.continuePrecision coarse).refinement

theorem second_request_uses_the_first_returned_prefix {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) (first second : Precision) :
    ((received.continuePrecision first).certificate.continuePrecision second).certificate.realization =
      (received.continuePrecision first).certificate.realization.evolve presentation.rule
        second.half.denominator := rfl

theorem an_empty_course_reuses_the_entire_certificate {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) :
    (received.runPrecisions []).endpoint.certificate = received := rfl

theorem continuing_a_returned_course_does_not_replay_its_prefix (rule : RelativeRefinementRule)
    (first second : List Precision) :
    ((course rule first).continue second).endpoint.certificate.realization =
      (course rule first).endpoint.certificate.realization.evolve rule (precisionCourseSteps second) :=
  productive_precision_continued_run_exact _ _

theorem no_course_returns_a_zero_width_window (rule : RelativeRefinementRule) (requests : List Precision) :
    (course rule requests).endpoint.window.span ≠ Rational.zero :=
  (contained_window_has_positive_span
    (bracket_contains_endpoints (course rule requests).endpoint.certificate.inside).1).2

theorem fine_then_coarse_is_still_nested (rule : RelativeRefinementRule) :
    WindowRefinement
      ((family rule).initialWindow.continuePrecision Precision.unit.half).window
      (((family rule).initialWindow.continuePrecision Precision.unit.half).certificate.continuePrecision
        Precision.unit).window :=
  a_coarser_request_cannot_reopen_a_finer_window _ _ _

def smoke (rule : RelativeRefinementRule) : Nat :=
  (course rule [Precision.unit, Precision.unit]).endpoint.certificate.depth

#eval smoke .upper

end Tests.Relativity.ProductivePrecisionCourseChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.input
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.initial
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.family
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.course
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.every_course_is_the_actual_forward_extension
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.every_course_has_the_constructed_depth
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.every_course_keeps_the_initial_constraint
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.every_course_keeps_the_two_sources_distinct
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.every_course_keeps_the_source_record
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.head_never_receives_the_future
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.every_local_request_meets_its_precision
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.a_coarser_request_cannot_reopen_a_finer_window
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.second_request_uses_the_first_returned_prefix
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.an_empty_course_reuses_the_entire_certificate
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.continuing_a_returned_course_does_not_replay_its_prefix
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.no_course_returns_a_zero_width_window
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.fine_then_coarse_is_still_nested
#print axioms Tests.Relativity.ProductivePrecisionCourseChecks.smoke
/- AXIOM_AUDIT_END -/
