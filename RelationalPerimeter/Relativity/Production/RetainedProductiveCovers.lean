import RelationalPerimeter.Relativity.Production.SharedProductiveCovers

/-!
# Whole recorded cover courses retained across resumption

Append consumes already-produced records, with a suffix indexed by the actual
three-certificate endpoint. Resumption executes only new requests. Equality
with the continuous runner concerns complete courses, including each selected
leaf and each rich received-prefix response, not only numerical readings.
These instrumental agreements do not license physical grouping or erasure.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

/-- Concatenate records without calling a selector or certificate producer. -/
def ProductiveCoverCourse.append
    {source target other : RelativePathState}
    {first : RelativePathPresentation source} {second : RelativePathPresentation target}
    {third : RelativePathPresentation other} :
    {received : ProductiveTripleEndpoint first second third} →
      {requests : List (ProductiveCoverRequest first second third)} →
      (course : ProductiveCoverCourse first second third received requests) →
      {more : List (ProductiveCoverRequest first second third)} →
      ProductiveCoverCourse first second third course.endpoint more →
      ProductiveCoverCourse first second third received (requests ++ more)
  | _, _, .done _, _, next => next
  | _, _, .step head chosenExact tail, _, next =>
    .step head chosenExact (tail.append next)

def ProductiveCoverCourse.recordedChoices {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) :
    List (List Bool) :=
  match course with
  | .done _ => []
  | .step head _ tail => head.chosen.leaf.branches :: tail.recordedChoices

def ProductiveCoverCourse.recordedBudgets {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) :
    List (Nat × Nat) :=
  match course with
  | .done _ => []
  | .step head _ tail => (head.second.steps, head.third.steps) :: tail.recordedBudgets

theorem productive_cover_append_returns_whole_endpoint
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    {more : List (ProductiveCoverRequest first second third)}
    (next : ProductiveCoverCourse first second third course.endpoint more) :
    (course.append next).endpoint = next.endpoint := by
  induction course with
  | done => rfl
  | step head chosenExact tail ih => exact ih next

theorem productive_cover_append_keeps_whole_head
    {source target other first second third received request requests}
    (course : @ProductiveCoverCourse source target other first second third received (request :: requests))
    {more : List (ProductiveCoverRequest first second third)}
    (next : ProductiveCoverCourse first second third course.endpoint more) :
    (course.append next).headProduction = course.headProduction := by
  cases course
  rfl

theorem productive_cover_append_choices
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    {more : List (ProductiveCoverRequest first second third)}
    (next : ProductiveCoverCourse first second third course.endpoint more) :
    (course.append next).recordedChoices = course.recordedChoices ++ next.recordedChoices := by
  induction course with
  | done => rfl
  | step head chosenExact tail ih =>
    exact congrArg (List.cons head.chosen.leaf.branches) (ih next)

theorem productive_cover_append_budgets
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    {more : List (ProductiveCoverRequest first second third)}
    (next : ProductiveCoverCourse first second third course.endpoint more) :
    (course.append next).recordedBudgets = course.recordedBudgets ++ next.recordedBudgets := by
  induction course with
  | done => rfl
  | step head chosenExact tail ih =>
    exact congrArg (List.cons (head.second.steps, head.third.steps)) (ih next)

/-- Adaptive requests see the same actual endpoints on both sides. This is
equality of the whole recorded production, not just of its observations. -/
theorem productive_cover_run_append_exact
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    received.runCovers (requests ++ more) firstAgreement secondAgreement =
      (received.runCovers requests firstAgreement secondAgreement).append
        ((received.runCovers requests firstAgreement secondAgreement).endpoint.runCovers
          more firstAgreement secondAgreement) := by
  induction requests generalizing received with
  | nil => rfl
  | cons request requests ih =>
    exact congrArg (fun tail => ProductiveCoverCourse.step
      (received.selectSharedCover (request received) firstAgreement secondAgreement) rfl tail)
      (ih (received.selectSharedCover (request received) firstAgreement secondAgreement).endpoint)

/-- Execute the new suffix once, then retain the already-produced course.
The endpoint traversal and record append are not asserted cost-free. -/
def ProductiveCoverCourse.resumeRetaining
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveCoverCourse first second third received (requests ++ more) :=
  let returned := course.endpoint
  let next := returned.runCovers more firstAgreement secondAgreement
  course.append next

theorem productive_retained_cover_is_whole_continuous_course
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runCovers requests firstAgreement secondAgreement).resumeRetaining
        more firstAgreement secondAgreement =
      received.runCovers (requests ++ more) firstAgreement secondAgreement :=
  (productive_cover_run_append_exact ..).symm

theorem productive_cover_request_append_assoc
    {source target other first second third}
    (one two three : List (@ProductiveCoverRequest source target other first second third)) :
    (one ++ two) ++ three = one ++ (two ++ three) := by
  induction one with
  | nil => rfl
  | cons request rest ih => exact congrArg (List.cons request) ih

theorem productive_retained_covers_twice_same_endpoint
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests more last : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (((received.runCovers requests firstAgreement secondAgreement).resumeRetaining
        more firstAgreement secondAgreement).resumeRetaining last firstAgreement secondAgreement).endpoint =
      (received.runCovers (requests ++ (more ++ last)) firstAgreement secondAgreement).endpoint := by
  rw [productive_retained_cover_is_whole_continuous_course,
    productive_retained_cover_is_whole_continuous_course, productive_cover_request_append_assoc]

theorem productive_retained_cover_returns_actual_suffix_endpoint
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (course.resumeRetaining more firstAgreement secondAgreement).endpoint =
      (course.resume more firstAgreement secondAgreement).endpoint :=
  productive_cover_append_returns_whole_endpoint ..

theorem productive_retained_cover_keeps_whole_head
    {source target other first second third received request requests}
    (course : @ProductiveCoverCourse source target other first second third received (request :: requests))
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (course.resumeRetaining more firstAgreement secondAgreement).headProduction = course.headProduction :=
  productive_cover_append_keeps_whole_head ..

theorem productive_retained_cover_choices
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (course.resumeRetaining more firstAgreement secondAgreement).recordedChoices =
      course.recordedChoices ++ (course.resume more firstAgreement secondAgreement).recordedChoices :=
  productive_cover_append_choices ..

theorem productive_retained_cover_budgets
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (course.resumeRetaining more firstAgreement secondAgreement).recordedBudgets =
      course.recordedBudgets ++ (course.resume more firstAgreement secondAgreement).recordedBudgets :=
  productive_cover_append_budgets ..

theorem productive_retained_cover_extends_three_received_prefixes
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveTripleExtension received (course.resumeRetaining more firstAgreement secondAgreement).endpoint :=
  (course.resumeRetaining more firstAgreement secondAgreement).extendsReceived

theorem productive_retained_cover_all_later_readings
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) (later : Nat) :
    received.window.Contains
        ((course.resumeRetaining more firstAgreement secondAgreement).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      received.window.Contains
        ((course.resumeRetaining more firstAgreement secondAgreement).endpoint.secondCertificate.advance later).realization.state.reading.value ∧
      received.window.Contains
        ((course.resumeRetaining more firstAgreement secondAgreement).endpoint.thirdCertificate.advance later).realization.state.reading.value :=
  (course.resumeRetaining more firstAgreement secondAgreement).allLaterReadings later

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.append
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.recordedChoices
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.recordedBudgets
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_append_returns_whole_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_append_keeps_whole_head
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_append_choices
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_append_budgets
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_run_append_exact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.resumeRetaining
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_is_whole_continuous_course
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_request_append_assoc
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_covers_twice_same_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_returns_actual_suffix_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_keeps_whole_head
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_choices
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_budgets
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_extends_three_received_prefixes
#print axioms RelationalPerimeter.Relativity.Production.productive_retained_cover_all_later_readings
/- AXIOM_AUDIT_END -/
