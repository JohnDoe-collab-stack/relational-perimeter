import RelationalPerimeter

/-! Public clients close the composition on generated neighboring families
and an actual resumed third prefix. No physical localization is inferred;
only an empty-course executable smoke is evaluated. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.ComposedAgreementCourseChecks
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

def thirdSeed (steps : Nat) := firstCertificate.advance steps
def third (steps : Nat) := (thirdSeed steps).receivedPresentation
def thirdCertificate (steps : Nat) : ProductiveWindowCertificate (third steps) initialWindow :=
  (thirdSeed steps).receivedCertificate
def secondThirdAgreement (steps : Nat) : Agreement second.numeric (third steps).numeric :=
  (thirdSeed steps).agreementFromReceived agreement.reverse

def firstCourse (requests : List Precision) := firstCertificate.runPrecisions requests
def middleCourse (requests : List Precision) :=
  (firstCourse requests).matchAgreed secondCertificate agreement
def composedCourse (steps : Nat) (requests : List Precision) :=
  (middleCourse requests).composeAgreed (thirdCertificate steps) (secondThirdAgreement steps)

theorem the_third_seed_is_an_actual_prolonged_prefix (steps : Nat) :
    (thirdCertificate steps).realization = firstCertificate.realization.evolve first.rule steps := rfl

theorem a_new_third_prefix_changes_its_initial_reading :
    first.stored.state.reading.value ≠ (third 1).stored.state.reading.value :=
  relative_first_upper_reading_differs first.stored .upper rfl

theorem the_first_two_initial_readings_remain_distinct :
    first.stored.state.reading.value ≠ second.stored.state.reading.value :=
  relative_subdivision_choices_have_different_readings initial

theorem every_composed_course_extends_its_received_third_prefix (steps : Nat) (requests : List Precision) :
    (composedCourse steps requests).endpoint.realization =
      (thirdCertificate steps).realization.evolve (third steps).rule (composedCourse steps requests).steps :=
  productive_composed_course_run_exact _ _ _

theorem every_composed_course_accumulates_actual_depth (steps : Nat) (requests : List Precision) :
    (composedCourse steps requests).endpoint.depth =
      (thirdCertificate steps).depth + (composedCourse steps requests).steps :=
  productive_composed_course_depth_exact _ _ _

theorem every_composed_course_keeps_its_seed_requests (steps : Nat) (requests : List Precision) :
    (composedCourse steps requests).endpoint.realization.chain.requests.length =
      (thirdCertificate steps).realization.chain.requests.length + (composedCourse steps requests).steps := by
  rw [every_composed_course_extends_its_received_third_prefix]
  exact relative_evolution_request_count ..

theorem all_three_later_readings_share_the_same_window (steps : Nat) (requests : List Precision)
    (one two three : Nat)
    (oneEnough : (firstCourse requests).endpoint.certificate.depth ≤ one)
    (twoEnough : (middleCourse requests).endpoint.depth ≤ two)
    (threeEnough : (composedCourse steps requests).endpoint.depth ≤ three) :
    (firstCourse requests).endpoint.window.Contains (first.numeric.approximate one) ∧
      (firstCourse requests).endpoint.window.Contains (second.numeric.approximate two) ∧
        (firstCourse requests).endpoint.window.Contains ((third steps).numeric.approximate three) :=
  ⟨productive_certificate_all_later_indices _ _ oneEnough,
    productive_certificate_all_later_indices _ _ twoEnough,
    productive_certificate_all_later_indices _ _ threeEnough⟩

theorem every_third_future_keeps_the_initial_constraint (steps : Nat) (requests : List Precision)
    (index : Nat) (enough : (composedCourse steps requests).endpoint.depth ≤ index) :
    initialWindow.Contains ((third steps).numeric.approximate index) :=
  (composedCourse steps requests).noLaterEscape index enough

theorem the_local_budget_uses_the_actual_middle_certificate (steps : Nat) (precision : Precision)
    (requests : List Precision) :
    (composedCourse steps (precision :: requests)).headProduction.steps =
      (secondThirdAgreement steps).modulus
          (middleCourse (precision :: requests)).headProduction.certificate.agreementPrecision +
        (middleCourse (precision :: requests)).headProduction.certificate.agreementPrecision.denominator := by
  dsimp only [composedCourse]
  rw [productive_composed_course_head_exact]
  exact productive_composition_budget_reads_intermediate_margins _ _ _

theorem the_composed_head_is_independent_of_both_future_tails (steps : Nat) (precision : Precision)
    (one two : List Precision) :
    (composedCourse steps (precision :: one)).headProduction =
      (composedCourse steps (precision :: two)).headProduction :=
  productive_composed_course_head_horizon_independent _ _ _ _ _ _ _ _

theorem requested_precision_controls_first_and_third_futures (steps : Nat) (precision : Precision)
    (one three : Nat) (oneEnough : (firstCourse [precision]).endpoint.certificate.depth ≤ one)
    (threeEnough : (composedCourse steps [precision]).endpoint.depth ≤ three) :
    Close (first.numeric.approximate one) ((third steps).numeric.approximate three) precision.value :=
  ((composedCourse steps [precision]).comparison precision
    (firstCertificate.continuePrecision precision).diameter).allLaterClose one three oneEnough threeEnough

theorem the_composition_keeps_third_sources_distinct (steps : Nat) (requests : List Precision) :
    (historyTransport (composedCourse steps requests).endpoint.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (composedCourse steps requests).endpoint.realization.chain.history).references
        leftSource.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem the_composition_keeps_the_third_source_record (steps : Nat) (requests : List Precision) :
    (composedCourse steps requests).endpoint.realization.state.cursor.read
      ((historyTransport (composedCourse steps requests).endpoint.realization.chain.history).references
        leftSource.reading.arrivals.secondSignal) = leftSource.cursor.read leftSource.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

theorem the_intermediate_course_keeps_its_separate_sources (requests : List Precision) :
    (historyTransport (middleCourse requests).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.first ≠
      (historyTransport (middleCourse requests).endpoint.realization.chain.history).references
        rightSource.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem the_empty_composition_reuses_its_whole_received_certificate (steps : Nat) :
    (composedCourse steps []).endpoint = thirdCertificate steps := rfl

def continued (steps : Nat) (requests more : List Precision) :=
  (middleCourse requests).continueComposed (composedCourse steps requests) agreement
    (secondThirdAgreement steps) more

theorem continuation_uses_the_actual_third_endpoint (steps : Nat) (requests more : List Precision) :
    (continued steps requests more).endpoint.realization =
      (composedCourse steps requests).endpoint.realization.evolve (third steps).rule
        (continued steps requests more).steps :=
  productive_composed_continued_run_exact _ _ _ _ _

theorem continuation_uses_the_actual_second_endpoint (requests more : List Precision) :
    ((middleCourse requests).continue more agreement).endpoint.realization =
      (middleCourse requests).endpoint.realization.evolve second.rule
        ((middleCourse requests).continue more agreement).steps :=
  productive_agreed_continued_run_exact _ _ _

theorem continuation_uses_the_actual_first_endpoint (requests more : List Precision) :
    ((firstCourse requests).endpoint.certificate.runPrecisions more).endpoint.certificate.realization =
      (firstCourse requests).endpoint.certificate.realization.evolve first.rule (precisionCourseSteps more) :=
  ProductivePrecisionCourse.runExact _

def emptySmoke : Nat := (composedCourse 1 []).endpoint.depth
#eval emptySmoke

end Tests.Relativity.ComposedAgreementCourseChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.input
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.initial
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.leftSource
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.rightSource
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.first
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.second
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.agreement
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.initialWindow
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.firstCertificate
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.secondCertificate
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.thirdSeed
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.third
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.thirdCertificate
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.secondThirdAgreement
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.firstCourse
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.middleCourse
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.composedCourse
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_third_seed_is_an_actual_prolonged_prefix
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.a_new_third_prefix_changes_its_initial_reading
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_first_two_initial_readings_remain_distinct
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.every_composed_course_extends_its_received_third_prefix
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.every_composed_course_accumulates_actual_depth
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.every_composed_course_keeps_its_seed_requests
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.all_three_later_readings_share_the_same_window
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.every_third_future_keeps_the_initial_constraint
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_local_budget_uses_the_actual_middle_certificate
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_composed_head_is_independent_of_both_future_tails
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.requested_precision_controls_first_and_third_futures
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_composition_keeps_third_sources_distinct
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_composition_keeps_the_third_source_record
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_intermediate_course_keeps_its_separate_sources
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.the_empty_composition_reuses_its_whole_received_certificate
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.continued
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.continuation_uses_the_actual_third_endpoint
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.continuation_uses_the_actual_second_endpoint
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.continuation_uses_the_actual_first_endpoint
#print axioms Tests.Relativity.ComposedAgreementCourseChecks.emptySmoke
/- AXIOM_AUDIT_END -/
