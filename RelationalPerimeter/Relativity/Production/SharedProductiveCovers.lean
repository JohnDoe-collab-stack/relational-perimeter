import RelationalPerimeter.Relativity.Production.ResumedAgreementCourses

/-!
# Shared productive cover choices on three received prefixes

One first-family selection records the leaf. The second certificate consumes
that realized window; the third consumes the actual second certificate. Each
finite request receives only the current endpoint. Agreements and cover trees
are declared inputs, not discovered physical laws. Numerical agreement neither
identifies source histories nor authorizes physical grouping or erasure.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

/-- A matching production indexed by the realized source window and received
target prefix. Its result keeps the complete newly executed realization. -/
structure ProductiveReceivedWindowMatch {source target : RelativePathState}
    {first : RelativePathPresentation source} {second : RelativePathPresentation target}
    {fine coarse : ReadingWindow}
    (certificate : ProductiveWindowCertificate first fine)
    (received : ProductiveWindowCertificate second coarse) where
  steps : Nat
  certificate : ProductiveWindowCertificate second fine
  depthExact : certificate.depth = received.depth + steps
  runExact : certificate.realization = received.realization.evolve second.rule steps

def ProductiveWindowCertificate.matchFromReceived
    {source target first second fine coarse}
    (certificate : @ProductiveWindowCertificate source first fine)
    (received : @ProductiveWindowCertificate target second coarse)
    (agreement : Agreement first.numeric second.numeric) :
    ProductiveReceivedWindowMatch certificate received := by
  let returned := certificate.certifyAgreed received.receivedPresentation
    (received.agreementFromReceived agreement)
  have actual : returned.realization = received.realization.evolve second.rule returned.depth := by
    rw [productive_agreed_certificate_exact, productive_agreed_certificate_depth]
    rfl
  refine ProductiveReceivedWindowMatch.mk (certificate := certificate) (received := received)
    returned.depth (received.fromReceived returned) ?_ ?_
  · rfl
  · dsimp only [ProductiveWindowCertificate.fromReceived]
    with_reducible exact actual

theorem productive_received_window_match_reads_margins
    {source target first second fine coarse}
    (certificate : @ProductiveWindowCertificate source first fine)
    (received : @ProductiveWindowCertificate target second coarse)
    (agreement : Agreement first.numeric second.numeric) :
    (certificate.matchFromReceived received agreement).steps =
      agreement.modulus certificate.agreementPrecision + certificate.agreementPrecision.denominator := rfl

structure ProductiveTripleEndpoint {source target other : RelativePathState}
    (first : RelativePathPresentation source) (second : RelativePathPresentation target)
    (third : RelativePathPresentation other) where
  window : ReadingWindow
  firstCertificate : ProductiveWindowCertificate first window
  secondCertificate : ProductiveWindowCertificate second window
  thirdCertificate : ProductiveWindowCertificate third window

structure ProductiveCoverHead {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (cover : InstrumentalReadingCover received.window) where
  chosen : CoveredProductivePresentation first cover
  second : ProductiveReceivedWindowMatch chosen.certificate received.secondCertificate
  third : ProductiveReceivedWindowMatch second.certificate received.thirdCertificate

def ProductiveTripleEndpoint.selectSharedCover {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (cover : InstrumentalReadingCover received.window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveCoverHead received cover :=
  let chosen := cover.selectProductive received.firstCertificate
  let secondHead := chosen.certificate.matchFromReceived received.secondCertificate firstAgreement
  let thirdHead := secondHead.certificate.matchFromReceived received.thirdCertificate secondAgreement
  ⟨chosen, secondHead, thirdHead⟩

def ProductiveCoverHead.endpoint {source target other first second third received cover}
    (head : @ProductiveCoverHead source target other first second third received cover) :
    ProductiveTripleEndpoint first second third :=
  ⟨head.chosen.window, head.chosen.certificate, head.second.certificate, head.third.certificate⟩

theorem productive_shared_cover_keeps_the_selected_leaf
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (cover : InstrumentalReadingCover received.window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.selectSharedCover cover firstAgreement secondAgreement).chosen =
      cover.selectProductive received.firstCertificate := rfl

theorem productive_shared_cover_third_consumes_actual_second
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (cover : InstrumentalReadingCover received.window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.selectSharedCover cover firstAgreement secondAgreement).third =
      (received.selectSharedCover cover firstAgreement secondAgreement).second.certificate.matchFromReceived
        received.thirdCertificate secondAgreement := rfl

def ProductiveTripleExtension {source target other first second third}
    (before after : @ProductiveTripleEndpoint source target other first second third) : Prop :=
  (∃ steps, after.firstCertificate.realization =
    before.firstCertificate.realization.evolve first.rule steps) ∧
  (∃ steps, after.secondCertificate.realization =
    before.secondCertificate.realization.evolve second.rule steps) ∧
  (∃ steps, after.thirdCertificate.realization =
    before.thirdCertificate.realization.evolve third.rule steps)

theorem productive_triple_extension_identity {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third) :
    ProductiveTripleExtension received received := ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem productive_triple_extensions_compose {source target other first second third}
    {one two three : @ProductiveTripleEndpoint source target other first second third}
    (firstExtension : ProductiveTripleExtension one two)
    (secondExtension : ProductiveTripleExtension two three) :
    ProductiveTripleExtension one three := by
  obtain ⟨⟨left, leftExact⟩, ⟨middle, middleExact⟩, ⟨right, rightExact⟩⟩ := firstExtension
  obtain ⟨⟨nextLeft, nextLeftExact⟩, ⟨nextMiddle, nextMiddleExact⟩, ⟨nextRight, nextRightExact⟩⟩ := secondExtension
  refine ⟨⟨left + nextLeft, ?_⟩, ⟨middle + nextMiddle, ?_⟩, ⟨right + nextRight, ?_⟩⟩
  · rw [nextLeftExact, leftExact, relative_evolution_compose]
  · rw [nextMiddleExact, middleExact, relative_evolution_compose]
  · rw [nextRightExact, rightExact, relative_evolution_compose]

theorem ProductiveCoverHead.extendsReceived {source target other first second third received cover}
    (head : @ProductiveCoverHead source target other first second third received cover)
    (chosenExact : head.chosen = cover.selectProductive received.firstCertificate) :
    ProductiveTripleExtension received head.endpoint := by
  obtain ⟨steps, _, actual⟩ := productive_cover_extends_only_its_received_prefix cover received.firstCertificate
  refine ⟨⟨steps, ?_⟩, ⟨head.second.steps, head.second.runExact⟩, ⟨head.third.steps, head.third.runExact⟩⟩
  change head.chosen.certificate.realization = _
  rw [chosenExact]
  exact actual

/-- The request supplies a justified tree on the received window, not a leaf.
It receives no completed suffix. This interface is numerical, not physical. -/
abbrev ProductiveCoverRequest {source target other}
    (first : RelativePathPresentation source) (second : RelativePathPresentation target)
    (third : RelativePathPresentation other) :=
  (received : ProductiveTripleEndpoint first second third) → InstrumentalReadingCover received.window

inductive ProductiveCoverCourse {source target other}
    (first : RelativePathPresentation source) (second : RelativePathPresentation target)
    (third : RelativePathPresentation other) :
    ProductiveTripleEndpoint first second third → List (ProductiveCoverRequest first second third) → Type where
  | done (received : ProductiveTripleEndpoint first second third) : ProductiveCoverCourse first second third received []
  | step {received request requests}
      (head : ProductiveCoverHead received (request received))
      (chosenExact : head.chosen = (request received).selectProductive received.firstCertificate)
      (tail : ProductiveCoverCourse first second third head.endpoint requests) :
      ProductiveCoverCourse first second third received (request :: requests)

def ProductiveTripleEndpoint.runCovers {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveCoverCourse first second third received requests :=
  match requests with
  | [] => .done received
  | request :: requests =>
    let head := received.selectSharedCover (request received) firstAgreement secondAgreement
    let tail := head.endpoint.runCovers requests firstAgreement secondAgreement
    .step head rfl tail
termination_by structural requests

def ProductiveCoverCourse.endpoint {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) :
    ProductiveTripleEndpoint first second third :=
  match course with
  | .done received => received
  | .step _ _ tail => tail.endpoint

def ProductiveCoverCourse.headProduction {source target other first second third received request requests}
    (course : @ProductiveCoverCourse source target other first second third received (request :: requests)) :
    ProductiveCoverHead received (request received) :=
  match course with
  | .step head _ _ => head

theorem productive_cover_course_head_exact
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (request : ProductiveCoverRequest first second third) (requests : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runCovers (request :: requests) firstAgreement secondAgreement).headProduction =
      received.selectSharedCover (request received) firstAgreement secondAgreement := rfl

theorem productive_cover_head_window_exact {source target other first second third received cover}
    (head : @ProductiveCoverHead source target other first second third received cover) :
    head.endpoint.window = head.chosen.window := rfl

theorem productive_shared_cover_third_budget
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (cover : InstrumentalReadingCover received.window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.selectSharedCover cover firstAgreement secondAgreement).third.steps =
      secondAgreement.modulus
        (received.selectSharedCover cover firstAgreement secondAgreement).second.certificate.agreementPrecision +
      (received.selectSharedCover cover firstAgreement secondAgreement).second.certificate.agreementPrecision.denominator := rfl

theorem ProductiveCoverCourse.refinement {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) :
    WindowRefinement received.window course.endpoint.window := by
  induction course with
  | done => exact .identity _
  | step head _ tail ih => exact head.chosen.leaf.refinement.compose ih

theorem ProductiveCoverCourse.extendsReceived {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) :
    ProductiveTripleExtension received course.endpoint := by
  induction course with
  | done => exact productive_triple_extension_identity _
  | step head chosenExact tail ih =>
    exact productive_triple_extensions_compose (head.extendsReceived chosenExact) ih

theorem productive_cover_course_head_horizon_independent
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (request : ProductiveCoverRequest first second third) (one two : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runCovers (request :: one) firstAgreement secondAgreement).headProduction =
      (received.runCovers (request :: two) firstAgreement secondAgreement).headProduction := rfl

theorem productive_cover_course_empty_returns_whole_endpoint
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.runCovers [] firstAgreement secondAgreement).endpoint = received := rfl

theorem ProductiveCoverCourse.allLaterReadings {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests) (steps : Nat) :
    received.window.Contains (course.endpoint.firstCertificate.advance steps).realization.state.reading.value ∧
    received.window.Contains (course.endpoint.secondCertificate.advance steps).realization.state.reading.value ∧
    received.window.Contains (course.endpoint.thirdCertificate.advance steps).realization.state.reading.value :=
  ⟨course.refinement.contains (bracket_contains_endpoints (course.endpoint.firstCertificate.advance steps).inside).1,
    course.refinement.contains (bracket_contains_endpoints (course.endpoint.secondCertificate.advance steps).inside).1,
    course.refinement.contains (bracket_contains_endpoints (course.endpoint.thirdCertificate.advance steps).inside).1⟩

def ProductiveCoverCourse.resume {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveCoverCourse first second third course.endpoint more :=
  course.endpoint.runCovers more firstAgreement secondAgreement

theorem productive_cover_resumption_extends_actual_endpoints
    {source target other first second third received requests}
    (course : @ProductiveCoverCourse source target other first second third received requests)
    (more : List (ProductiveCoverRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveTripleExtension course.endpoint (course.resume more firstAgreement secondAgreement).endpoint :=
  (course.resume more firstAgreement secondAgreement).extendsReceived

/-- Consume the complete endpoints already stored by the precision courses.
No precision course or producer is run by this view. -/
def ProductiveAgreedPrecisionCourse.coverEndpoint
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received) :
    ProductiveTripleEndpoint first second third :=
  ⟨course.endpoint.window, course.endpoint.certificate, matched.endpoint, composed.endpoint⟩

theorem productive_cover_endpoint_keeps_three_actual_certificates
    {source target other first second third window left requests course middle received}
    (matched : @ProductiveAgreedPrecisionCourse source target first second window left requests course middle)
    (composed : @ProductiveAgreedPrecisionCourse source other first third window left requests course received) :
    (matched.coverEndpoint composed).firstCertificate = course.endpoint.certificate ∧
    (matched.coverEndpoint composed).secondCertificate = matched.endpoint ∧
    (matched.coverEndpoint composed).thirdCertificate = composed.endpoint := ⟨rfl, rfl, rfl⟩

/-- A one-split leaf is read from the returned bracket, not from the
cover's syntactic position. These laws leave the rich prefix opaque. -/
theorem productive_single_split_left_branches {source presentation window}
    (split : OverlappingWindowSplit window)
    (certificate : @ProductiveWindowCertificate source presentation window)
    (below : RationalStrictLess
      (certificate.advance (strictReadingGap split.lowerCut split.upperCut split.overlap).half.denominator).realization.state.reading.upper
      split.upperCut) :
    ((InstrumentalReadingCover.split split (.identity _) (.identity _)).selectProductive certificate).leaf.branches = [true] := by
  rw [InstrumentalReadingCover.selectProductive]
  unfold OverlappingWindowSplit.chooseProductive
  dsimp only
  rw [dif_pos below]
  rfl

theorem productive_single_split_right_branches {source presentation window}
    (split : OverlappingWindowSplit window)
    (certificate : @ProductiveWindowCertificate source presentation window)
    (notBelow : ¬ RationalStrictLess
      (certificate.advance (strictReadingGap split.lowerCut split.upperCut split.overlap).half.denominator).realization.state.reading.upper
      split.upperCut) :
    ((InstrumentalReadingCover.split split (.identity _) (.identity _)).selectProductive certificate).leaf.branches = [false] := by
  rw [InstrumentalReadingCover.selectProductive]
  unfold OverlappingWindowSplit.chooseProductive
  dsimp only
  rw [dif_neg notBelow]
  rfl

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveReceivedWindowMatch
#print axioms RelationalPerimeter.Relativity.Production.ProductiveWindowCertificate.matchFromReceived
#print axioms RelationalPerimeter.Relativity.Production.productive_received_window_match_reads_margins
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint.selectSharedCover
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverHead.endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_shared_cover_keeps_the_selected_leaf
#print axioms RelationalPerimeter.Relativity.Production.productive_shared_cover_third_consumes_actual_second
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleExtension
#print axioms RelationalPerimeter.Relativity.Production.productive_triple_extension_identity
#print axioms RelationalPerimeter.Relativity.Production.productive_triple_extensions_compose
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverHead.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverRequest
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint.runCovers
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.headProduction
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_course_head_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_head_window_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_shared_cover_third_budget
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_course_head_horizon_independent
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_course_empty_returns_whole_endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.allLaterReadings
#print axioms RelationalPerimeter.Relativity.Production.ProductiveCoverCourse.resume
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_resumption_extends_actual_endpoints
#print axioms RelationalPerimeter.Relativity.Production.ProductiveAgreedPrecisionCourse.coverEndpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_endpoint_keeps_three_actual_certificates
#print axioms RelationalPerimeter.Relativity.Production.productive_single_split_left_branches
#print axioms RelationalPerimeter.Relativity.Production.productive_single_split_right_branches
/- AXIOM_AUDIT_END -/
