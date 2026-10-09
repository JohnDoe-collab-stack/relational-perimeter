import RelationalPerimeter.Relativity.Production.ComposedAgreementCourses

/-!
# Retaining actual course records across agreement resumption

Appending already-produced courses runs no producer. Composition follows the
recorded intermediate certificates in the same order before and after append.
A shared resumption produces one source suffix and its two matching suffixes,
then retains both complete courses. Numerical compatibility is not physical
location, source identification, erasure, or a total cost bound.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

def ProductiveAgreedPrecisionCourse.endpointView
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received) :
    ProductiveWindowEndpoint second := ⟨course.endpoint.window, matched.endpoint⟩

/-- Append records only. The next course starts at the exact stored endpoint. -/
def ProductiveAgreedPrecisionCourse.append
    {source target : RelativePathState}
    {first : RelativePathPresentation source} {second : RelativePathPresentation target} :
    {window : ReadingWindow} → {left : ProductiveWindowCertificate first window} →
      {requests : List Precision} → {course : ProductivePrecisionCourse first left requests} →
      {received : ProductiveWindowCertificate second window} →
      (matched : ProductiveAgreedPrecisionCourse first second course received) → {more : List Precision} →
      {suffix : ProductivePrecisionCourse first course.endpoint.certificate more} →
      ProductiveAgreedPrecisionCourse first second suffix matched.endpoint →
      ProductiveAgreedPrecisionCourse first second (course.append suffix) received
  | _, _, _, _, _, .done _ _, _, _, next => next
  | _, _, _, _, _, .step head tail received produced rest, _, suffix, next =>
    .step head (tail.append suffix) received produced (rest.append next)

theorem productive_agreed_append_returns_whole_endpoint
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received)
    {more : List Precision} {suffix : ProductivePrecisionCourse first course.endpoint.certificate more}
    (next : ProductiveAgreedPrecisionCourse first second suffix matched.endpoint) :
    (matched.append next).endpointView = next.endpointView := by
  induction matched with
  | done => rfl
  | step head tail received produced rest ih => exact ih next

theorem productive_agreed_append_steps
    {source target first second window left requests course received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course received)
    {more : List Precision} {suffix : ProductivePrecisionCourse first course.endpoint.certificate more}
    (next : ProductiveAgreedPrecisionCourse first second suffix matched.endpoint) :
    (matched.append next).steps = matched.steps + next.steps := by
  induction matched with
  | done => exact (Nat.zero_add _).symm
  | step head tail received produced rest ih =>
    change produced.steps + (rest.append next).steps = _
    rw [ih next]
    exact (Nat.add_assoc _ _ _).symm

theorem productive_agreed_append_keeps_head
    {source target first second window left precision requests received}
    (head : @ProductivePrecisionContinuation source first window left precision)
    (tail : ProductivePrecisionCourse first head.certificate requests)
    (produced : @ProductiveAgreedContinuation source target first second window left precision head received)
    (rest : ProductiveAgreedPrecisionCourse first second tail produced.certificate)
    {more : List Precision} {suffix : ProductivePrecisionCourse first tail.endpoint.certificate more}
    (next : ProductiveAgreedPrecisionCourse first second suffix rest.endpoint) :
    ((ProductiveAgreedPrecisionCourse.step head tail received produced rest).append next).headProduction =
      produced := rfl

theorem productive_composition_append_square
    {source target other first second third window left requests course middle}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    {more : List Precision} {suffix : ProductivePrecisionCourse first course.endpoint.certificate more}
    (next : ProductiveAgreedPrecisionCourse first second suffix matched.endpoint)
    (received : @ProductiveWindowCertificate other third window)
    (agreement : Agreement second.numeric third.numeric) :
    (matched.append next).composeAgreed received agreement =
      (matched.composeAgreed received agreement).append
        (next.composeAgreed (matched.composeAgreed received agreement).endpoint agreement) := by
  induction matched with
  | done => rfl
  | step head tail middle produced rest ih =>
    change ProductivePrecisionCourse first tail.endpoint.certificate more at suffix
    change ProductiveAgreedPrecisionCourse first second suffix rest.endpoint at next
    exact congrArg (fun finished => ProductiveAgreedPrecisionCourse.step head (tail.append suffix)
      received (produced.viaIntermediate received agreement) finished)
      (ih next (produced.viaIntermediate received agreement).certificate)

/-- Shared suffix production, then record-only append to both received courses.
Both complete outputs have literally the same prolonged first-course index. -/
def ProductiveAgreedPrecisionCourse.resumeComposedRetaining
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) (more : List Precision) :
    ProductiveAgreedPrecisionCourse first second
        (course.append (course.endpoint.certificate.runPrecisions more)) middle ×
      ProductiveAgreedPrecisionCourse first third
        (course.append (course.endpoint.certificate.runPrecisions more)) received :=
  let sourceEnd := course.endpoint
  let firstSuffix := sourceEnd.certificate.runPrecisions more
  let secondSuffix := firstSuffix.matchAgreed matched.endpoint firstAgreement
  let thirdSuffix := secondSuffix.composeAgreed composed.endpoint secondAgreement
  (matched.append secondSuffix, composed.append thirdSuffix)

theorem productive_resumed_second_endpoint_exact
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) (more : List Precision) :
    (matched.resumeComposedRetaining composed firstAgreement secondAgreement more).1.endpointView =
      (matched.continue more firstAgreement).endpointView :=
  productive_agreed_append_returns_whole_endpoint ..

theorem productive_resumed_third_endpoint_exact
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) (more : List Precision) :
    (matched.resumeComposedRetaining composed firstAgreement secondAgreement more).2.endpointView =
      (matched.continueComposed composed firstAgreement secondAgreement more).endpointView :=
  productive_agreed_append_returns_whole_endpoint ..

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.endpointView
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.append
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_append_returns_whole_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_append_steps
#print axioms RelationalPerimeter.Relativity.Production.productive_agreed_append_keeps_head
#print axioms RelationalPerimeter.Relativity.Production.productive_composition_append_square
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.resumeComposedRetaining
#print axioms RelationalPerimeter.Relativity.Production.productive_resumed_second_endpoint_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_resumed_third_endpoint_exact
/- AXIOM_AUDIT_END -/
