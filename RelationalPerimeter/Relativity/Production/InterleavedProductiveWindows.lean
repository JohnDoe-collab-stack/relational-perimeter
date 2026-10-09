import RelationalPerimeter.Relativity.Production.RetainedProductiveCovers

/-!
# Interleaved precision and cover requests on the same three prefixes

Each request reads only the currently returned triple. A precision production
is shared through the actual second and third certificates; cover requests
reuse the existing selector. Whole records survive append and resumption.
All requested precision bounds persist under later window refinement.
Agreements and cover trees remain declared inputs. These instrumental courses
neither identify rich histories nor construct physical localizations.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

structure ProductiveTriplePrecisionHead {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (precision : Precision) where
  first : ProductivePrecisionContinuation received.firstCertificate precision
  second : ProductiveReceivedWindowMatch first.certificate received.secondCertificate
  third : ProductiveReceivedWindowMatch second.certificate received.thirdCertificate

def ProductiveTripleEndpoint.continueSharedPrecision {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (precision : Precision) (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveTriplePrecisionHead received precision :=
  let firstHead := received.firstCertificate.continuePrecision precision
  let secondHead := firstHead.certificate.matchFromReceived received.secondCertificate firstAgreement
  let thirdHead := secondHead.certificate.matchFromReceived received.thirdCertificate secondAgreement
  ⟨firstHead, secondHead, thirdHead⟩

def ProductiveTriplePrecisionHead.endpoint {source target other first second third received precision}
    (head : @ProductiveTriplePrecisionHead source target other first second third received precision) :
    ProductiveTripleEndpoint first second third :=
  ⟨head.first.window, head.first.certificate, head.second.certificate, head.third.certificate⟩

theorem productive_shared_precision_third_consumes_actual_second
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (precision : Precision) (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.continueSharedPrecision precision firstAgreement secondAgreement).third =
      (received.continueSharedPrecision precision firstAgreement secondAgreement).second.certificate.matchFromReceived
        received.thirdCertificate secondAgreement := rfl

theorem ProductiveTriplePrecisionHead.extendsReceived
    {source target other first second third received precision}
    (head : @ProductiveTriplePrecisionHead source target other first second third received precision) :
    ProductiveTripleExtension received head.endpoint :=
  ⟨⟨precision.half.denominator, head.first.runExact⟩,
    ⟨head.second.steps, head.second.runExact⟩, ⟨head.third.steps, head.third.runExact⟩⟩

inductive ProductiveWindowOperation {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third) where
  | precision (value : Precision)
  | cover (tree : InstrumentalReadingCover received.window)

abbrev ProductiveWindowRequest {source target other}
    (first : RelativePathPresentation source) (second : RelativePathPresentation target)
    (third : RelativePathPresentation other) :=
  (received : ProductiveTripleEndpoint first second third) → ProductiveWindowOperation received

def ProductiveWindowProduction {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (operation : ProductiveWindowOperation received) : Type :=
  match operation with
  | .precision value => ProductiveTriplePrecisionHead received value
  | .cover tree => ProductiveCoverHead received tree

def ProductiveWindowProduction.endpoint {source target other first second third received}
    (operation : @ProductiveWindowOperation source target other first second third received)
    (production : ProductiveWindowProduction received operation) : ProductiveTripleEndpoint first second third :=
  match operation with
  | .precision _ => ProductiveTriplePrecisionHead.endpoint production
  | .cover _ => ProductiveCoverHead.endpoint production

def ProductiveWindowProduction.choice {source target other first second third received}
    (operation : @ProductiveWindowOperation source target other first second third received)
    (production : ProductiveWindowProduction received operation) : Option (List Bool) :=
  match operation with
  | .precision _ => none
  | .cover _ => some production.chosen.leaf.branches

def ProductiveWindowProduction.CoverExact {source target other first second third received}
    (operation : @ProductiveWindowOperation source target other first second third received)
    (production : ProductiveWindowProduction received operation) : Prop :=
  match operation with
  | .precision _ => True
  | .cover tree => production.chosen = tree.selectProductive received.firstCertificate

/-- The complete actual production is stored, not hidden behind a proof.
Its endpoint and readouts are cached with exact return laws. The operation is
only an index: conversion need not call an old request to reconstruct it. -/
structure ProductiveWindowHead {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (operation : ProductiveWindowOperation received) where
  production : ProductiveWindowProduction received operation
  endpoint : ProductiveTripleEndpoint first second third
  endpointExact : endpoint = ProductiveWindowProduction.endpoint operation production
  precisions : List Precision
  precisionsExact : precisions = (match operation with | .precision value => [value] | .cover _ => [])
  recordedChoice : Option (List Bool)
  choiceExact : recordedChoice = ProductiveWindowProduction.choice operation production
  coverExact : ProductiveWindowProduction.CoverExact operation production

def ProductiveTriplePrecisionHead.asWindowHead {source target other first second third received precision}
    (head : @ProductiveTriplePrecisionHead source target other first second third received precision) :
    ProductiveWindowHead received (.precision precision) :=
  ⟨head, head.endpoint, rfl, [precision], rfl, none, rfl, True.intro⟩

def ProductiveCoverHead.asWindowHead {source target other first second third received cover}
    (head : @ProductiveCoverHead source target other first second third received cover)
    (chosenExact : head.chosen = cover.selectProductive received.firstCertificate) :
    ProductiveWindowHead received (.cover cover) :=
  ⟨head, head.endpoint, rfl, [], rfl, some head.chosen.leaf.branches, rfl, chosenExact⟩

def ProductiveTripleEndpoint.performWindow {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (operation : ProductiveWindowOperation received)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) : ProductiveWindowHead received operation :=
  match operation with
  | .precision value => (received.continueSharedPrecision value firstAgreement secondAgreement).asWindowHead
  | .cover tree => (received.selectSharedCover tree firstAgreement secondAgreement).asWindowHead rfl

theorem ProductiveWindowHead.refinement {source target other first second third received operation}
    (head : @ProductiveWindowHead source target other first second third received operation) :
    WindowRefinement received.window head.endpoint.window := by
  rw [head.endpointExact]
  cases operation with
  | precision value => exact head.production.first.refinement
  | cover tree => exact head.production.chosen.leaf.refinement

theorem ProductiveWindowHead.extendsReceived {source target other first second third received operation}
    (head : @ProductiveWindowHead source target other first second third received operation) :
    ProductiveTripleExtension received head.endpoint := by
  rw [head.endpointExact]
  cases operation with
  | precision value => exact head.production.extendsReceived
  | cover tree => exact head.production.extendsReceived head.coverExact

inductive ProductiveWindowCourse {source target other}
    (first : RelativePathPresentation source) (second : RelativePathPresentation target)
    (third : RelativePathPresentation other) :
    ProductiveTripleEndpoint first second third → List (ProductiveWindowRequest first second third) → Type where
  | done (received : ProductiveTripleEndpoint first second third) : ProductiveWindowCourse first second third received []
  | step {received request requests} (head : ProductiveWindowHead received (request received))
      (tail : ProductiveWindowCourse first second third head.endpoint requests) :
      ProductiveWindowCourse first second third received (request :: requests)

def ProductiveTripleEndpoint.runWindows {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveWindowCourse first second third received requests :=
  match requests with
  | [] => .done received
  | request :: requests =>
    let operation := request received
    let head := received.performWindow operation firstAgreement secondAgreement
    let tail := head.endpoint.runWindows requests firstAgreement secondAgreement
    .step head tail
termination_by structural requests

def ProductiveWindowCourse.endpoint {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests) :
    ProductiveTripleEndpoint first second third :=
  match course with
  | .done received => received
  | .step _ tail => tail.endpoint

def ProductiveWindowCourse.headProduction {source target other first second third received request requests}
    (course : @ProductiveWindowCourse source target other first second third received (request :: requests)) :
    ProductiveWindowHead received (request received) :=
  match course with
  | .step head _ => head

theorem productive_window_course_head_exact {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (request : ProductiveWindowRequest first second third) (requests : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runWindows (request :: requests) firstAgreement secondAgreement).headProduction =
      received.performWindow (request received) firstAgreement secondAgreement := rfl

theorem productive_window_head_horizon_independent {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (request : ProductiveWindowRequest first second third)
    (one two : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runWindows (request :: one) firstAgreement secondAgreement).headProduction =
      (received.runWindows (request :: two) firstAgreement secondAgreement).headProduction := rfl

theorem ProductiveWindowCourse.refinement {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests) :
    WindowRefinement received.window course.endpoint.window := by
  induction course with
  | done received => exact .identity _
  | step head tail ih => exact head.refinement.compose ih

theorem ProductiveWindowCourse.extendsReceived {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests) :
    ProductiveTripleExtension received course.endpoint := by
  induction course with
  | done received => exact productive_triple_extension_identity _
  | step head tail ih => exact productive_triple_extensions_compose head.extendsReceived ih

theorem ProductiveWindowHead.precisionBound {source target other first second third received operation}
    (head : @ProductiveWindowHead source target other first second third received operation)
    (precision : Precision) (present : precision ∈ head.precisions) :
    Rational.Le head.endpoint.window.span precision.value := by
  rw [head.precisionsExact] at present
  rw [head.endpointExact]
  cases operation with
  | precision value =>
    cases present with
    | head => exact head.production.first.diameter
    | tail _ impossible => cases impossible
  | cover tree => cases present

/-- Read the precision requests from actual head records, including adaptive
requests. Covers contribute no new precision but retain earlier bounds. -/
def ProductiveWindowCourse.requestedPrecisions {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests) : List Precision :=
  match course with
  | .done _ => []
  | .step head tail => head.precisions ++ tail.requestedPrecisions

theorem productive_precision_in_append (precision : Precision) (one two : List Precision)
    (present : precision ∈ one ++ two) : precision ∈ one ∨ precision ∈ two := by
  induction one with
  | nil => exact .inr present
  | cons value rest ih =>
    cases present with
    | head => exact .inl (.head _)
    | tail _ present =>
      cases ih present with
      | inl prior => exact .inl (.tail _ prior)
      | inr later => exact .inr later

theorem ProductiveWindowCourse.allRequestedBounds {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests)
    (precision : Precision) (requested : precision ∈ course.requestedPrecisions) :
    Rational.Le course.endpoint.window.span precision.value := by
  induction course with
  | done received => cases requested
  | step head tail ih =>
    cases productive_precision_in_append precision head.precisions tail.requestedPrecisions requested with
    | inl present => exact Rational.le_trans tail.refinement.span_le (head.precisionBound precision present)
    | inr present => exact ih present

theorem ProductiveWindowCourse.allLaterReadings {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests) (later : Nat) :
    received.window.Contains (course.endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      received.window.Contains (course.endpoint.secondCertificate.advance later).realization.state.reading.value ∧
      received.window.Contains (course.endpoint.thirdCertificate.advance later).realization.state.reading.value :=
  ⟨course.refinement.contains (bracket_contains_endpoints (course.endpoint.firstCertificate.advance later).inside).1,
    course.refinement.contains (bracket_contains_endpoints (course.endpoint.secondCertificate.advance later).inside).1,
    course.refinement.contains (bracket_contains_endpoints (course.endpoint.thirdCertificate.advance later).inside).1⟩

/-- Append already-produced records. Explicit structural equations keep this
data-producing dependent recursion executable. No agreement or producer needed. -/
def ProductiveWindowCourse.append {source target other first second third} :
    {received : @ProductiveTripleEndpoint source target other first second third} →
    {requests : List (ProductiveWindowRequest first second third)} →
    (course : ProductiveWindowCourse first second third received requests) →
    {more : List (ProductiveWindowRequest first second third)} →
    ProductiveWindowCourse first second third course.endpoint more →
    ProductiveWindowCourse first second third received (requests ++ more)
  | _, _, .done _, _, next => next
  | _, _, .step head tail, _, next => .step head (tail.append next)

theorem productive_window_append_returns_whole_endpoint
    {source target other first second third received requests more}
    (course : @ProductiveWindowCourse source target other first second third received requests)
    (next : ProductiveWindowCourse first second third course.endpoint more) :
    (course.append next).endpoint = next.endpoint := by
  induction course with
  | done received => rfl
  | step head tail ih => exact ih next

theorem productive_window_append_keeps_whole_head
    {source target other first second third received request requests more}
    (course : @ProductiveWindowCourse source target other first second third received (request :: requests))
    (next : ProductiveWindowCourse first second third course.endpoint more) :
    (course.append next).headProduction = course.headProduction := by cases course; rfl

theorem productive_window_run_append_exact {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests more : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    received.runWindows (requests ++ more) firstAgreement secondAgreement =
      (received.runWindows requests firstAgreement secondAgreement).append
        ((received.runWindows requests firstAgreement secondAgreement).endpoint.runWindows
          more firstAgreement secondAgreement) := by
  induction requests generalizing received with
  | nil => rfl
  | cons request requests ih =>
    exact congrArg (fun tail => ProductiveWindowCourse.step
      (received.performWindow (request received) firstAgreement secondAgreement) tail)
      (ih (received.performWindow (request received) firstAgreement secondAgreement).endpoint)

def ProductiveWindowCourse.resumeRetaining {source target other first second third received requests}
    (course : @ProductiveWindowCourse source target other first second third received requests)
    (more : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveWindowCourse first second third received (requests ++ more) :=
  let returned := course.endpoint
  let next := returned.runWindows more firstAgreement secondAgreement
  course.append next

theorem productive_retained_windows_are_whole_continuous_course
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests more : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runWindows requests firstAgreement secondAgreement).resumeRetaining
        more firstAgreement secondAgreement =
      received.runWindows (requests ++ more) firstAgreement secondAgreement :=
  (productive_window_run_append_exact ..).symm

def coverWindowRequest {source target other first second third}
    (request : @ProductiveCoverRequest source target other first second third) :
    ProductiveWindowRequest first second third := fun received => .cover (request received)

/-- Convert stored cover records, not their producers. The complete endpoint
and actual selected leaves are retained without selecting or certifying again. -/
def ProductiveCoverCourse.asWindowCourse {source target other first second third} :
    {received : @ProductiveTripleEndpoint source target other first second third} →
    {requests : List (ProductiveCoverRequest first second third)} →
    ProductiveCoverCourse first second third received requests →
    ProductiveWindowCourse first second third received (requests.map coverWindowRequest)
  | _, [], .done received => .done received
  | _, _ :: _, .step head chosenExact tail =>
      let wrapped := head.asWindowHead chosenExact
      .step wrapped (ProductiveCoverCourse.asWindowCourse (received := wrapped.endpoint) tail)

theorem productive_cover_conversion_returns_whole_endpoint
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) :
    course.asWindowCourse.endpoint = course.endpoint := by
  induction course with
  | done received => rfl
  | step head chosenExact tail ih => exact ih

theorem productive_cover_conversion_keeps_recorded_head
    {source target other first second third received request requests}
    (course : @ProductiveCoverCourse source target other first second third received (request :: requests)) :
    course.asWindowCourse.headProduction.recordedChoice = some course.headProduction.chosen.leaf.branches := by
  cases course
  rfl

theorem productive_cover_only_is_same_whole_course {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runCovers requests firstAgreement secondAgreement).asWindowCourse =
      received.runWindows (requests.map coverWindowRequest) firstAgreement secondAgreement := by
  induction requests generalizing received with
  | nil => rfl
  | cons request requests ih =>
    exact congrArg (fun tail => ProductiveWindowCourse.step (request := coverWindowRequest request)
      ((received.selectSharedCover (request received) firstAgreement secondAgreement).asWindowHead rfl) tail)
      (ih (received.selectSharedCover (request received) firstAgreement secondAgreement).endpoint)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTriplePrecisionHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint.continueSharedPrecision
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTriplePrecisionHead.endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_shared_precision_third_consumes_actual_second
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTriplePrecisionHead.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowOperation
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowRequest
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowProduction
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowProduction.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowProduction.choice
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowProduction.CoverExact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTriplePrecisionHead.asWindowHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverHead.asWindowHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint.performWindow
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead.recordedChoice
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint.runWindows
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.headProduction
#print axioms RelationalPerimeter.Relativity.Production.productive_window_course_head_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_window_head_horizon_independent
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead.precisions
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowHead.precisionBound
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.requestedPrecisions
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_in_append
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.allRequestedBounds
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.allLaterReadings
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.append
#print axioms RelationalPerimeter.Relativity.Production.productive_window_append_returns_whole_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_window_append_keeps_whole_head
#print axioms RelationalPerimeter.Relativity.Production.productive_window_run_append_exact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCourse.resumeRetaining
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_windows_are_whole_continuous_course
#print axioms RelationalPerimeter.Relativity.Production.coverWindowRequest
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.asWindowCourse
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_conversion_returns_whole_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_conversion_keeps_recorded_head
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_only_is_same_whole_course
/- AXIOM_AUDIT_END -/
