import RelationalPerimeter

/-! Closed public clients for full course retention on generated neighboring
families and a real third prefix. Only an empty-course smoke is evaluated. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.ResumedAgreementCourseChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def initial : RelativePathState :=
  let produced := realizeRelativeReading (.received input) .here (.prior .here)
    (.prior (.prior .here)) rfl 0 0
  RelativePathState.fromExecution produced (.prior (.prior .here)) rfl
def leftSource := (refineRelativePaths initial .lower).state
def rightSource := (refineRelativePaths initial .upper).state
def first := RelativePathPresentation.fromState leftSource .upper
def second := RelativePathPresentation.fromState rightSource .lower
def agreement : Agreement first.numeric second.numeric := relative_children_boundary_agreement initial
def initialWindow : ReadingWindow := ⟨Rational.neg (Rational.ofNat 2), Rational.ofNat 5⟩
def firstCertificate : ProductiveWindowCertificate first initialWindow :=
  first.initialWindow.restrict ⟨by decide, by decide⟩
def secondCertificate : ProductiveWindowCertificate second initialWindow :=
  second.initialWindow.restrict ⟨by decide, by decide⟩
def thirdSeed (steps : Nat) := firstCertificate.advance steps
def third (steps : Nat) := (thirdSeed steps).receivedPresentation
def thirdCertificate (steps : Nat) := (thirdSeed steps).receivedCertificate
def secondThirdAgreement (steps : Nat) : Agreement second.numeric (third steps).numeric :=
  (thirdSeed steps).agreementFromReceived agreement.reverse
def firstCourse (requests : List Precision) := firstCertificate.runPrecisions requests
def middleCourse (requests : List Precision) :=
  (firstCourse requests).matchAgreed secondCertificate agreement
def thirdCourse (steps : Nat) (requests : List Precision) :=
  (middleCourse requests).composeAgreed (thirdCertificate steps) (secondThirdAgreement steps)
def retained (steps : Nat) (requests more : List Precision) :=
  (middleCourse requests).resumeComposedRetaining (thirdCourse steps requests)
    agreement (secondThirdAgreement steps) more

theorem the_complete_second_endpoint_is_the_actual_suffix (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).1.endpointView =
      ((middleCourse requests).continue more agreement).endpointView :=
  productive_resumed_second_endpoint_exact ..

theorem the_complete_third_endpoint_is_the_actual_suffix (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).2.endpointView =
      ((middleCourse requests).continueComposed (thirdCourse steps requests) agreement
        (secondThirdAgreement steps) more).endpointView :=
  productive_resumed_third_endpoint_exact ..

theorem the_retained_composition_is_the_complete_produced_course
    (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).2 =
      (retained steps requests more).1.composeAgreed (thirdCertificate steps) (secondThirdAgreement steps) :=
  (productive_composition_append_square (middleCourse requests)
    ((middleCourse requests).continue more agreement) (thirdCertificate steps) (secondThirdAgreement steps)).symm

theorem both_old_and_new_second_subdivisions_are_retained (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).1.steps = (middleCourse requests).steps +
      ((middleCourse requests).continue more agreement).steps :=
  productive_agreed_append_steps ..

theorem both_old_and_new_third_subdivisions_are_retained (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).2.steps = (thirdCourse steps requests).steps +
      ((middleCourse requests).continueComposed (thirdCourse steps requests) agreement
        (secondThirdAgreement steps) more).steps :=
  productive_agreed_append_steps ..

theorem retained_second_run_extends_its_original_received_prefix
    (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).1.endpoint.realization =
      secondCertificate.realization.evolve second.rule (retained steps requests more).1.steps :=
  (retained steps requests more).1.runExact

theorem retained_third_run_extends_its_original_received_prefix
    (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).2.endpoint.realization =
      (thirdCertificate steps).realization.evolve (third steps).rule (retained steps requests more).2.steps :=
  (retained steps requests more).2.runExact

theorem old_second_head_is_unchanged (steps : Nat) (precision : Precision) (requests more : List Precision) :
    (retained steps (precision :: requests) more).1.headProduction =
      (middleCourse (precision :: requests)).headProduction := rfl

theorem old_third_head_is_unchanged (steps : Nat) (precision : Precision) (requests more : List Precision) :
    (retained steps (precision :: requests) more).2.headProduction =
      (thirdCourse steps (precision :: requests)).headProduction := rfl

theorem all_second_futures_keep_the_initial_window (steps : Nat) (requests more : List Precision)
    (index : Nat) (enough : (retained steps requests more).1.endpoint.depth ≤ index) :
    initialWindow.Contains (second.numeric.approximate index) :=
  (retained steps requests more).1.noLaterEscape index enough

theorem all_third_futures_keep_the_initial_window (steps : Nat) (requests more : List Precision)
    (index : Nat) (enough : (retained steps requests more).2.endpoint.depth ≤ index) :
    initialWindow.Contains ((third steps).numeric.approximate index) :=
  (retained steps requests more).2.noLaterEscape index enough

theorem retaining_keeps_sources_separate (steps : Nat) (requests more : List Precision) :
    (historyTransport (retained steps requests more).2.endpoint.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (retained steps requests more).2.endpoint.realization.chain.history).references
        leftSource.reading.arrivals.second :=
  relative_refinement_chain_keeps_sources _

theorem retaining_keeps_the_source_record (steps : Nat) (requests more : List Precision) :
    (retained steps requests more).2.endpoint.realization.state.cursor.read
      ((historyTransport (retained steps requests more).2.endpoint.realization.chain.history).references
        leftSource.reading.arrivals.secondSignal) = leftSource.cursor.read leftSource.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

def emptySmoke : Nat := (retained 1 [] []).2.endpoint.depth
#eval emptySmoke

end Tests.Relativity.ResumedAgreementCourseChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.input
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.initial
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.leftSource
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.rightSource
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.first
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.second
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.agreement
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.initialWindow
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.firstCertificate
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.secondCertificate
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.thirdSeed
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.third
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.thirdCertificate
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.secondThirdAgreement
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.firstCourse
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.middleCourse
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.thirdCourse
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.retained
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.the_complete_second_endpoint_is_the_actual_suffix
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.the_complete_third_endpoint_is_the_actual_suffix
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.the_retained_composition_is_the_complete_produced_course
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.both_old_and_new_second_subdivisions_are_retained
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.both_old_and_new_third_subdivisions_are_retained
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.retained_second_run_extends_its_original_received_prefix
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.retained_third_run_extends_its_original_received_prefix
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.old_second_head_is_unchanged
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.old_third_head_is_unchanged
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.all_second_futures_keep_the_initial_window
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.all_third_futures_keep_the_initial_window
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.retaining_keeps_sources_separate
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.retaining_keeps_the_source_record
#print axioms Tests.Relativity.ResumedAgreementCourseChecks.emptySmoke
/- AXIOM_AUDIT_END -/
