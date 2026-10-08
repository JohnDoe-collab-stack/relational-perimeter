import RelationalPerimeter.Relativity.Production.ProductivePrecisionCourses

/-!
# Successive agreement certification from actual returned prefixes

A received first course supplies its recorded local windows. Each matching
head extends the actual second certificate, then hands that complete result
to the next head. Numerical agreement supplies a precision modulus, not a
source-history transport or a physical localization. No first production
is replayed by the matching runner.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

def ProductiveWindowCertificate.receivedPresentation {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) :
    RelativePathPresentation source := ⟨received.realization, presentation.rule⟩

theorem productive_received_presentation_exact {source presentation window}
    (received : @ProductiveWindowCertificate source presentation window) (steps : Nat) :
    received.receivedPresentation.realize steps = presentation.realize (received.depth + steps) :=
  (congrArg (fun run => run.evolve presentation.rule steps) received.realizationExact).trans
    (relative_evolution_compose presentation.stored presentation.rule received.depth steps)

def ProductiveWindowCertificate.agreementFromReceived {source target : RelativePathState}
    {first : RelativePathPresentation source} {second : RelativePathPresentation target}
    {window : ReadingWindow}
    (received : ProductiveWindowCertificate second window)
    (agreement : Agreement first.numeric second.numeric) :
    Agreement first.numeric received.receivedPresentation.numeric where
  modulus precision := agreement.modulus precision
  close precision left right leftEnough rightEnough := by
    change Close (first.realize left).state.reading.value
      (received.receivedPresentation.realize right).state.reading.value precision.value
    rw [productive_received_presentation_exact]
    dsimp only [RelativePathPresentation.numeric] at agreement
    with_reducible
      exact agreement.close precision left
        (received.depth + right) leftEnough (Nat.le_trans rightEnough (Nat.le_add_left ..))

/-- Keep the returned realization as data; only its original-family index
is justified by composition with the exact received prefix. -/
def ProductiveWindowCertificate.fromReceived {source presentation window nextWindow}
    (received : @ProductiveWindowCertificate source presentation window)
    (returned : ProductiveWindowCertificate received.receivedPresentation nextWindow) :
    ProductiveWindowCertificate presentation nextWindow :=
  ⟨received.depth + returned.depth, returned.realization,
    returned.realizationExact.trans (productive_received_presentation_exact received returned.depth),
    returned.inside⟩

structure ProductiveAgreedContinuation {source target first second window left precision}
    (head : @ProductivePrecisionContinuation source first window left precision)
    (received : @ProductiveWindowCertificate target second window) where
  steps : Nat
  certificate : ProductiveWindowCertificate second head.window
  depthExact : certificate.depth = received.depth + steps
  runExact : certificate.realization = received.realization.evolve second.rule steps

/-- Consume the stored local first head and the actual received second
prefix. The first head is never reexecuted. The modulus and margins are
those of the received positive agreement and realized certificate. -/
def ProductivePrecisionContinuation.continueAgreed
    {source target first second window left precision}
    (head : @ProductivePrecisionContinuation source first window left precision)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) :
    ProductiveAgreedContinuation head received := by
  let continued := received.receivedPresentation
  let continuedAgreement := received.agreementFromReceived agreement
  let returned := head.certificate.certifyAgreed continued continuedAgreement
  have actual : returned.realization = received.realization.evolve second.rule returned.depth := by
    rw [productive_agreed_certificate_exact, productive_agreed_certificate_depth]
    rfl
  refine ProductiveAgreedContinuation.mk (head := head) (received := received)
    returned.depth (received.fromReceived returned) ?_ ?_
  · rfl
  · dsimp only [ProductiveWindowCertificate.fromReceived]
    with_reducible exact actual

theorem productive_agreed_continuation_uses_received_prefix
    {source target first second window left precision}
    (head : @ProductivePrecisionContinuation source first window left precision)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) :
    (head.continueAgreed received agreement).certificate.realization =
      received.realization.evolve second.rule (head.continueAgreed received agreement).steps :=
  (head.continueAgreed received agreement).runExact

theorem productive_agreed_continuation_keeps_source_window
    {source target first second window left precision}
    (head : @ProductivePrecisionContinuation source first window left precision)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) :
    head.window.BracketContains (head.continueAgreed received agreement).certificate.realization.state.reading :=
  (head.continueAgreed received agreement).certificate.inside

theorem productive_agreed_continuation_budget_exact
    {source target first second window left precision}
    (head : @ProductivePrecisionContinuation source first window left precision)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) :
    (head.continueAgreed received agreement).steps =
      agreement.modulus head.certificate.agreementPrecision +
        head.certificate.agreementPrecision.denominator := rfl

inductive ProductiveAgreedPrecisionCourse {source target}
    (first : RelativePathPresentation source) (second : RelativePathPresentation target) :
    {window : ReadingWindow} → {left : ProductiveWindowCertificate first window} →
    {requests : List Precision} → ProductivePrecisionCourse first left requests →
    ProductiveWindowCertificate second window → Type where
  | done {window} (left : ProductiveWindowCertificate first window)
      (received : ProductiveWindowCertificate second window) :
      ProductiveAgreedPrecisionCourse first second (.done left) received
  | step {window precision requests} {left : ProductiveWindowCertificate first window}
      (head : ProductivePrecisionContinuation left precision)
      (tail : ProductivePrecisionCourse first head.certificate requests)
      (received : ProductiveWindowCertificate second window)
      (produced : ProductiveAgreedContinuation head received)
      (next : ProductiveAgreedPrecisionCourse first second tail produced.certificate) :
      ProductiveAgreedPrecisionCourse first second (.step head tail) received

def ProductivePrecisionCourse.matchAgreed {source target first second window left requests}
    (course : @ProductivePrecisionCourse source first window left requests)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) :
    ProductiveAgreedPrecisionCourse first second course received :=
  match course with
  | .done certificate => .done certificate received
  | .step head tail =>
    let produced := head.continueAgreed received agreement
    let next := tail.matchAgreed produced.certificate agreement
    .step head tail received produced next
termination_by structural course

def ProductiveAgreedPrecisionCourse.endpoint
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received) :
    ProductiveWindowCertificate second course.endpoint.window :=
  match matched with
  | .done _ received => received
  | .step _ _ _ _ next => next.endpoint

def ProductiveAgreedPrecisionCourse.steps
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received) : Nat :=
  match matched with
  | .done _ _ => 0
  | .step _ _ _ produced next => produced.steps + next.steps

def ProductiveAgreedPrecisionCourse.headProduction
    {source target first second window left precision requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left
      (precision :: requests) course received) :
    ProductiveAgreedContinuation course.headProduction received :=
  match matched with
  | .step _ _ _ produced _ => produced

theorem ProductiveAgreedPrecisionCourse.depthExact
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received) :
    matched.endpoint.depth = received.depth + matched.steps := by
  induction matched with
  | done _ received => exact (Nat.add_zero _).symm
  | step head tail received produced next ih =>
    change next.endpoint.depth = _
    rw [ih, produced.depthExact]
    exact Nat.add_assoc _ _ _

theorem ProductiveAgreedPrecisionCourse.runExact
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received) :
    matched.endpoint.realization = received.realization.evolve second.rule matched.steps := by
  induction matched with
  | done _ received => rfl
  | step head tail received produced next ih =>
    change next.endpoint.realization = _
    rw [ih, produced.runExact]
    exact relative_evolution_compose ..

theorem ProductiveAgreedPrecisionCourse.noLaterEscape
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received)
    (index : Nat) (enough : matched.endpoint.depth ≤ index) :
    window.Contains (second.numeric.approximate index) :=
  course.refinement.contains (productive_certificate_all_later_indices matched.endpoint index enough)

def ProductiveAgreedPrecisionCourse.comparison
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received)
    (precision : Precision) (diameter : Rational.Le course.endpoint.window.span precision.value) :
    ProductiveWindowComparison first second precision :=
  ⟨course.endpoint.window, course.endpoint.certificate, matched.endpoint, diameter⟩

theorem productive_agreed_course_head_horizon_independent
    {source target first second window}
    (left : @ProductiveWindowCertificate source first window)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) (precision : Precision)
    (one two : List Precision) :
    ((left.runPrecisions (precision :: one)).matchAgreed received agreement).headProduction =
      ((left.runPrecisions (precision :: two)).matchAgreed received agreement).headProduction := rfl

theorem productive_agreed_empty_course_reuses_received_certificate
    {source target first second window}
    (left : @ProductiveWindowCertificate source first window)
    (received : @ProductiveWindowCertificate target second window)
    (agreement : Agreement first.numeric second.numeric) :
    ((left.runPrecisions []).matchAgreed received agreement).endpoint = received := rfl

/-- Start both new courses from their actually returned endpoints. The
previous first course and matching course remain stored, not replayed. -/
def ProductiveAgreedPrecisionCourse.continue
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received)
    (more : List Precision) (agreement : Agreement first.numeric second.numeric) :
    ProductiveAgreedPrecisionCourse first second
      (course.endpoint.certificate.runPrecisions more) matched.endpoint :=
  let firstSuffix := course.endpoint.certificate.runPrecisions more
  firstSuffix.matchAgreed matched.endpoint agreement

theorem productive_agreed_continued_run_exact
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received)
    (more : List Precision) (agreement : Agreement first.numeric second.numeric) :
    (matched.continue more agreement).endpoint.realization =
      matched.endpoint.realization.evolve second.rule (matched.continue more agreement).steps :=
  (matched.continue more agreement).runExact

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.receivedPresentation
#print axioms RelationalPerimeter.Relativity.Production.productive_received_presentation_exact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.agreementFromReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.fromReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedContinuation
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionContinuation.continueAgreed
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_continuation_uses_received_prefix
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_continuation_keeps_source_window
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_continuation_budget_exact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse
#print axioms RelationalPerimeter.Relativity.Production.ProductivePrecisionCourse.matchAgreed
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.steps
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.headProduction
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.depthExact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.runExact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.noLaterEscape
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.comparison
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_course_head_horizon_independent
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_empty_course_reuses_received_certificate
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.continue
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_continued_run_exact
/- AXIOM_AUDIT_END -/
