import RelationalPerimeter.Relativity.Production.AgreedPrecisionCourses

/-!
# Agreement-course composition through actual intermediate certificates

The received second course supplies its recorded local certificates. Each
third-family head consumes that certificate's margins and the received third
prefix; its result is handed to the next head. The first two courses are not
replayed. This is numerical composition, not identification of rich histories,
associativity of their executions, physical localization or erasure permission.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

/-- Reindex the actual received prefix as the local family's zero prefix.
No event or producer is added by this descriptive operation. -/
def ProductiveWindowCertificate.receivedCertificate {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) :
    ProductiveWindowCertificate received.receivedPresentation window :=
  ⟨0, received.realization, rfl, received.inside⟩

theorem productive_received_certificate_keeps_actual_run {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) :
    received.receivedCertificate.realization = received.realization := rfl

/-- The actual intermediate certificate supplies the new window and margins.
Only the third family's actual received prefix is extended as new data. -/
def ProductiveAgreedContinuation.viaIntermediate
    {source target other first second third window left precision}
    {head : @ProductivePrecisionContinuation source first window left precision}
    {middle : @ProductiveWindowCertificate target second window}
    (produced : ProductiveAgreedContinuation head middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    ProductiveAgreedContinuation head received := by
  let continued := received.receivedPresentation
  let continuedAgreement := received.agreementFromReceived agreement
  let returned := produced.certificate.certifyAgreed continued continuedAgreement
  have actual : returned.realization = received.realization.evolve third.rule returned.depth := by
    rw [productive_agreed_certificate_exact, productive_agreed_certificate_depth]
    rfl
  refine ProductiveAgreedContinuation.mk (head := head) (received := received)
    returned.depth (received.fromReceived returned) ?_ ?_
  · rfl
  · dsimp only [ProductiveWindowCertificate.fromReceived]
    with_reducible exact actual

theorem productive_composition_uses_intermediate_certificate
    {source target other first second third window left precision}
    {head : @ProductivePrecisionContinuation source first window left precision}
    {middle : @ProductiveWindowCertificate target second window}
    (produced : ProductiveAgreedContinuation head middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    (produced.viaIntermediate received agreement).certificate =
      received.fromReceived (produced.certificate.certifyAgreed received.receivedPresentation
        (received.agreementFromReceived agreement)) := rfl

theorem productive_composition_budget_reads_intermediate_margins
    {source target other first second third window left precision}
    {head : @ProductivePrecisionContinuation source first window left precision}
    {middle : @ProductiveWindowCertificate target second window}
    (produced : ProductiveAgreedContinuation head middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    (produced.viaIntermediate received agreement).steps =
      agreement.modulus produced.certificate.agreementPrecision +
        produced.certificate.agreementPrecision.denominator := rfl

def ProductiveAgreedPrecisionCourse.composeAgreed
    {source target other first second third window left requests course middle}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    ProductiveAgreedPrecisionCourse first third course received :=
  match matched with
  | .done left _ => .done left received
  | .step head tail _ produced next =>
    let thirdHead := produced.viaIntermediate received agreement
    let thirdTail := next.composeAgreed thirdHead.certificate agreement
    .step head tail received thirdHead thirdTail
termination_by structural matched

theorem productive_composed_course_run_exact
    {source target other first second third window left requests course middle}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    (matched.composeAgreed received agreement).endpoint.realization =
      received.realization.evolve third.rule (matched.composeAgreed received agreement).steps :=
  (matched.composeAgreed received agreement).runExact

theorem productive_composed_course_depth_exact
    {source target other first second third window left requests course middle}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    (matched.composeAgreed received agreement).endpoint.depth =
      received.depth + (matched.composeAgreed received agreement).steps :=
  (matched.composeAgreed received agreement).depthExact

theorem productive_composed_course_head_exact
    {source target other first second third window left precision requests course middle}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left
      (precision :: requests) course middle)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    (matched.composeAgreed received agreement).headProduction =
      matched.headProduction.viaIntermediate received agreement := by
  cases matched
  rfl

theorem productive_composed_course_head_horizon_independent
    {source target other first second third window}
    (left : @ProductiveWindowCertificate source first window)
    (middle : @ProductiveWindowCertificate target second window)
    (received : @ProductiveWindowCertificate other third window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric)
    (precision : Precision) (one two : List Precision) :
    (((left.runPrecisions (precision :: one)).matchAgreed middle firstAgreement).composeAgreed
      received secondAgreement).headProduction =
    (((left.runPrecisions (precision :: two)).matchAgreed middle firstAgreement).composeAgreed
      received secondAgreement).headProduction := rfl

theorem productive_composed_empty_course_reuses_received_certificate
    {source target other first second third window}
    (left : @ProductiveWindowCertificate source first window)
    (middle : @ProductiveWindowCertificate target second window)
    (received : @ProductiveWindowCertificate other third window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (((left.runPrecisions []).matchAgreed middle firstAgreement).composeAgreed
      received secondAgreement).endpoint = received := rfl

/-- Continue the first/second pair from its two stored endpoints once, then
compose this new suffix from the stored third endpoint. The old courses
remain available and no prefix production is replayed here. -/
def ProductiveAgreedPrecisionCourse.continueComposed
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric)
    (more : List Precision) :
    ProductiveAgreedPrecisionCourse first third (course.endpoint.certificate.runPrecisions more)
      composed.endpoint :=
  let nextPair := matched.continue more firstAgreement
  nextPair.composeAgreed composed.endpoint secondAgreement

theorem productive_composed_continued_run_exact
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric)
    (more : List Precision) :
    (matched.continueComposed composed firstAgreement secondAgreement more).endpoint.realization =
      composed.endpoint.realization.evolve third.rule
        (matched.continueComposed composed firstAgreement secondAgreement more).steps :=
  (matched.continueComposed composed firstAgreement secondAgreement more).runExact

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.receivedCertificate
#print axioms RelationalPerimeter.Relativity.Production.productive_received_certificate_keeps_actual_run
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedContinuation.viaIntermediate
#print axioms RelationalPerimeter.Relativity.Production.productive_composition_uses_intermediate_certificate
#print axioms RelationalPerimeter.Relativity.Production.productive_composition_budget_reads_intermediate_margins
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.composeAgreed
#print axioms RelationalPerimeter.Relativity.Production.productive_composed_course_run_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_composed_course_depth_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_composed_course_head_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_composed_course_head_horizon_independent
#print axioms RelationalPerimeter.Relativity.Production.productive_composed_empty_course_reuses_received_certificate
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.continueComposed
#print axioms RelationalPerimeter.Relativity.Production.productive_composed_continued_run_exact
/- AXIOM_AUDIT_END -/
