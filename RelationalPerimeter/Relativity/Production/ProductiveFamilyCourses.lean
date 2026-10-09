import RelationalPerimeter.Relativity.Production.FiniteProductiveParticipants

/-!
# Retained mixed requests on arbitrary finite constituted families

Each head is formed from the received endpoint alone. Its complete production
and endpoint are stored before the next request. Append only copies records;
resumption executes the new requests on the actual final endpoint. Numerical
agreements and requests remain inputs, not physical locations or erased paths.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

inductive ProductiveFamilyOperation {first participants}
    (received : @ProductiveFamilyEndpoint first participants) where
  | precision (value : Precision)
  | cover (tree : InstrumentalReadingCover received.window)

abbrev ProductiveFamilyRequest {first} (participants : ProductiveParticipants first) :=
  (received : ProductiveFamilyEndpoint participants) → ProductiveFamilyOperation received

def ProductiveFamilyProduction {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (operation : ProductiveFamilyOperation received) : Type :=
  match operation with
  | .precision value => ProductiveFamilyPrecisionHead received value
  | .cover tree => ProductiveFamilyCoverHead received tree

def ProductiveFamilyProduction.endpoint {first participants received}
    (operation : @ProductiveFamilyOperation first participants received)
    (production : ProductiveFamilyProduction received operation) : ProductiveFamilyEndpoint participants :=
  match operation with
  | .precision _ => ProductiveFamilyPrecisionHead.endpoint production
  | .cover _ => ProductiveFamilyCoverHead.endpoint production

def ProductiveFamilyProduction.choice {first participants received}
    (operation : @ProductiveFamilyOperation first participants received)
    (production : ProductiveFamilyProduction received operation) : Option (List Bool) :=
  match operation with
  | .precision _ => none
  | .cover _ => some production.chosen.leaf.branches

structure ProductiveFamilyHead {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (operation : ProductiveFamilyOperation received) where
  production : ProductiveFamilyProduction received operation
  endpoint : ProductiveFamilyEndpoint participants
  endpointExact : endpoint = ProductiveFamilyProduction.endpoint operation production
  precisions : List Precision
  precisionsExact : precisions = (match operation with | .precision value => [value] | .cover _ => [])
  recordedChoice : Option (List Bool)
  choiceExact : recordedChoice = ProductiveFamilyProduction.choice operation production

def ProductiveFamilyPrecisionHead.asFamilyHead {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision) :
    ProductiveFamilyHead received (.precision precision) :=
  ⟨head, head.endpoint, rfl, [precision], rfl, none, rfl⟩

def ProductiveFamilyCoverHead.asFamilyHead {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) :
    ProductiveFamilyHead received (.cover cover) :=
  ⟨head, head.endpoint, rfl, [], rfl, some head.chosen.leaf.branches, rfl⟩

def ProductiveFamilyEndpoint.performWindow {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (operation : ProductiveFamilyOperation received) : ProductiveFamilyHead received operation :=
  match operation with
  | .precision value => (received.continuePrecision value).asFamilyHead
  | .cover tree => (received.selectCover tree).asFamilyHead

theorem ProductiveFamilyHead.refinement {first participants received operation}
    (head : @ProductiveFamilyHead first participants received operation) :
    WindowRefinement received.window head.endpoint.window := by
  rw [head.endpointExact]
  cases operation with
  | precision value => exact head.production.refinement
  | cover tree => exact head.production.refinement

theorem ProductiveFamilyHead.extendsReceived {first participants received operation}
    (head : @ProductiveFamilyHead first participants received operation) :
    ProductiveFamilyExtension received head.endpoint := by
  rw [head.endpointExact]
  cases operation with
  | precision value => exact head.production.extendsReceived
  | cover tree => exact head.production.extendsReceived

theorem ProductiveFamilyHead.precisionBound {first participants received operation}
    (head : @ProductiveFamilyHead first participants received operation)
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

inductive ProductiveFamilyCourse {first} (participants : ProductiveParticipants first) :
    ProductiveFamilyEndpoint participants → List (ProductiveFamilyRequest participants) → Type where
  | done (received : ProductiveFamilyEndpoint participants) : ProductiveFamilyCourse participants received []
  | step {received request requests} (head : ProductiveFamilyHead received (request received))
      (tail : ProductiveFamilyCourse participants head.endpoint requests) :
      ProductiveFamilyCourse participants received (request :: requests)

def ProductiveFamilyEndpoint.runWindows {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (requests : List (ProductiveFamilyRequest participants)) :
    ProductiveFamilyCourse participants received requests :=
  match requests with
  | [] => .done received
  | request :: rest =>
    let operation := request received
    let head := received.performWindow operation
    let tail := head.endpoint.runWindows rest
    .step head tail
termination_by structural requests

def ProductiveFamilyCourse.endpoint {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) : ProductiveFamilyEndpoint participants :=
  match course with
  | .done received => received
  | .step _ tail => tail.endpoint

def ProductiveFamilyCourse.headProduction {first participants received request requests}
    (course : @ProductiveFamilyCourse first participants received (request :: requests)) :
    ProductiveFamilyHead received (request received) :=
  match course with
  | .step head _ => head

theorem productive_family_head_exact {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (request : ProductiveFamilyRequest participants) (requests : List (ProductiveFamilyRequest participants)) :
    (received.runWindows (request :: requests)).headProduction = received.performWindow (request received) := rfl

theorem productive_family_head_horizon_independent {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (request : ProductiveFamilyRequest participants)
    (one two : List (ProductiveFamilyRequest participants)) :
    (received.runWindows (request :: one)).headProduction = (received.runWindows (request :: two)).headProduction := rfl

theorem participant_bundle_extension_identity (members : List ProductiveParticipant) {window}
    (certificates : participantCertificates members window) : ParticipantBundleExtension members certificates certificates := by
  induction members with
  | nil => exact True.intro
  | cons member rest ih => exact ⟨⟨0, rfl⟩, ih certificates.2⟩

theorem productive_family_extension_identity {first participants}
    (received : @ProductiveFamilyEndpoint first participants) : ProductiveFamilyExtension received received :=
  ⟨⟨0, rfl⟩, participant_bundle_extension_identity participants.members received.certificates⟩

theorem ProductiveFamilyCourse.refinement {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) :
    WindowRefinement received.window course.endpoint.window := by
  induction course with
  | done received => exact .identity _
  | step head tail ih => exact head.refinement.compose ih

theorem ProductiveFamilyCourse.extendsReceived {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) : ProductiveFamilyExtension received course.endpoint := by
  induction course with
  | done received => exact productive_family_extension_identity _
  | step head tail ih => exact productive_family_extensions_compose head.extendsReceived ih

def ProductiveFamilyCourse.requestedPrecisions {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) : List Precision :=
  match course with
  | .done _ => []
  | .step head tail => head.precisions ++ tail.requestedPrecisions

def ProductiveFamilyCourse.recordedChoices {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) : List (Option (List Bool)) :=
  match course with
  | .done _ => []
  | .step head tail => head.recordedChoice :: tail.recordedChoices

theorem ProductiveFamilyCourse.allRequestedBounds {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests)
    (precision : Precision) (present : precision ∈ course.requestedPrecisions) :
    Rational.Le course.endpoint.window.span precision.value := by
  induction course with
  | done received => cases present
  | step head tail ih =>
    cases productive_precision_in_append precision head.precisions tail.requestedPrecisions present with
    | inl prior => exact Rational.le_trans tail.refinement.span_le (head.precisionBound precision prior)
    | inr later => exact ih later

theorem ProductiveFamilyCourse.allLaterReadings {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) (later : Nat) :
    received.window.Contains (course.endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      ParticipantBundleLaterInside participants.members course.endpoint.certificates received.window later :=
  ⟨course.refinement.contains (bracket_contains_endpoints (course.endpoint.firstCertificate.advance later).inside).1,
    participant_bundle_restrict_later_inside participants.members course.endpoint.certificates later course.refinement⟩

theorem ProductiveFamilyCourse.keepsSources {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests) :
    (historyTransport course.endpoint.firstCertificate.realization.chain.history).references first.source.reading.arrivals.first ≠
        (historyTransport course.endpoint.firstCertificate.realization.chain.history).references first.source.reading.arrivals.second ∧
      ParticipantBundleKeepsSources participants.members course.endpoint.certificates :=
  ⟨relative_refinement_chain_keeps_sources _, participant_bundle_keeps_every_source_distinction ..⟩

def ProductiveFamilyCourse.append {first participants} :
    {received : @ProductiveFamilyEndpoint first participants} →
    {requests : List (ProductiveFamilyRequest participants)} →
    (course : ProductiveFamilyCourse participants received requests) →
    {more : List (ProductiveFamilyRequest participants)} →
    ProductiveFamilyCourse participants course.endpoint more →
    ProductiveFamilyCourse participants received (requests ++ more)
  | _, _, .done _, _, next => next
  | _, _, .step head tail, _, next => .step head (tail.append next)

theorem productive_family_append_returns_whole_endpoint {first participants received requests more}
    (course : @ProductiveFamilyCourse first participants received requests)
    (next : ProductiveFamilyCourse participants course.endpoint more) : (course.append next).endpoint = next.endpoint := by
  induction course with
  | done received => rfl
  | step head tail ih => exact ih next

theorem productive_family_append_keeps_whole_head {first participants received request requests more}
    (course : @ProductiveFamilyCourse first participants received (request :: requests))
    (next : ProductiveFamilyCourse participants course.endpoint more) :
    (course.append next).headProduction = course.headProduction := by cases course; rfl

theorem productive_family_append_keeps_choices {first participants received requests more}
    (course : @ProductiveFamilyCourse first participants received requests)
    (next : ProductiveFamilyCourse participants course.endpoint more) :
    (course.append next).recordedChoices = course.recordedChoices ++ next.recordedChoices := by
  induction course with
  | done received => rfl
  | step head tail ih => exact congrArg (List.cons head.recordedChoice) (ih next)

theorem productive_family_precision_append_assoc (one two three : List Precision) :
    (one ++ two) ++ three = one ++ (two ++ three) := by
  induction one with
  | nil => rfl
  | cons value rest ih => exact congrArg (List.cons value) ih

theorem productive_family_append_keeps_precisions {first participants received requests more}
    (course : @ProductiveFamilyCourse first participants received requests)
    (next : ProductiveFamilyCourse participants course.endpoint more) :
    (course.append next).requestedPrecisions = course.requestedPrecisions ++ next.requestedPrecisions := by
  induction course with
  | done received => rfl
  | step head tail ih =>
    change head.precisions ++ (tail.append next).requestedPrecisions =
      (head.precisions ++ tail.requestedPrecisions) ++ next.requestedPrecisions
    rw [ih next]
    exact (productive_family_precision_append_assoc _ _ _).symm

theorem productive_family_run_append_exact {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (requests more : List (ProductiveFamilyRequest participants)) :
    received.runWindows (requests ++ more) =
      (received.runWindows requests).append ((received.runWindows requests).endpoint.runWindows more) := by
  induction requests generalizing received with
  | nil => rfl
  | cons request requests ih =>
    exact congrArg (fun tail => ProductiveFamilyCourse.step (received.performWindow (request received)) tail)
      (ih (received.performWindow (request received)).endpoint)

def ProductiveFamilyCourse.resumeRetaining {first participants received requests}
    (course : @ProductiveFamilyCourse first participants received requests)
    (more : List (ProductiveFamilyRequest participants)) : ProductiveFamilyCourse participants received (requests ++ more) :=
  let returned := course.endpoint
  let next := returned.runWindows more
  course.append next

theorem productive_family_retained_is_whole_continuous_course {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (requests more : List (ProductiveFamilyRequest participants)) :
    (received.runWindows requests).resumeRetaining more = received.runWindows (requests ++ more) :=
  (productive_family_run_append_exact ..).symm

/-- Read the three actual certificates, without invoking a producer. -/
def ProductiveFamilyEndpoint.asTriple {source target other first second third}
    {firstAgreement : Agreement first.numeric second.numeric}
    {secondAgreement : Agreement second.numeric third.numeric}
    (received : ProductiveFamilyEndpoint (first := ⟨source, first⟩)
      (.step ⟨target, second⟩ firstAgreement (.step ⟨other, third⟩ secondAgreement (.done _)))) :
    ProductiveTripleEndpoint first second third :=
  ⟨received.window, received.firstCertificate, received.certificates.1, received.certificates.2.1⟩

theorem productive_three_return_is_exact {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    (received.asFamily firstAgreement secondAgreement).asTriple = received := rfl

def familyRequestOfTriple {source target other first second third}
    (request : @ProductiveWindowRequest source target other first second third)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveFamilyRequest (first := ⟨source, first⟩)
      (.step ⟨target, second⟩ firstAgreement (.step ⟨other, third⟩ secondAgreement (.done _))) :=
  fun received => match request received.asTriple with
    | .precision value => .precision value
    | .cover tree => .cover tree

theorem productive_three_mixed_head_endpoint {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (request : ProductiveWindowRequest first second third)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ((received.asFamily firstAgreement secondAgreement).performWindow
      (familyRequestOfTriple request firstAgreement secondAgreement
        (received.asFamily firstAgreement secondAgreement))).endpoint =
      (received.performWindow (request received) firstAgreement secondAgreement).endpoint.asFamily
        firstAgreement secondAgreement := by
  cases received with
  | mk window one two three =>
    dsimp only [familyRequestOfTriple, ProductiveTripleEndpoint.asFamily, ProductiveFamilyEndpoint.asTriple]
    cases request ⟨window, one, two, three⟩ <;> rfl

theorem productive_three_mixed_course_returns_whole_endpoint {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (requests : List (ProductiveWindowRequest first second third))
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ((received.asFamily firstAgreement secondAgreement).runWindows
      (requests.map (fun request => familyRequestOfTriple request firstAgreement secondAgreement))).endpoint =
      (received.runWindows requests firstAgreement secondAgreement).endpoint.asFamily firstAgreement secondAgreement := by
  induction requests generalizing received with
  | nil => rfl
  | cons request requests ih =>
    dsimp only [List.map, ProductiveFamilyEndpoint.runWindows, ProductiveFamilyCourse.endpoint,
      ProductiveTripleEndpoint.runWindows, ProductiveWindowCourse.endpoint]
    rw [productive_three_mixed_head_endpoint]
    exact ih (received.performWindow (request received) firstAgreement secondAgreement).endpoint

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyOperation
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyRequest
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyProduction
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyProduction.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyProduction.choice
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.asFamilyHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.asFamilyHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint.performWindow
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyHead.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyHead.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyHead.precisionBound
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint.runWindows
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.headProduction
#print axioms RelationalPerimeter.Relativity.Production.productive_family_head_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_family_head_horizon_independent
#print axioms RelationalPerimeter.Relativity.Production.participant_bundle_extension_identity
#print axioms RelationalPerimeter.Relativity.Production.productive_family_extension_identity
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.requestedPrecisions
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.recordedChoices
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.allRequestedBounds
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.allLaterReadings
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.keepsSources
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.append
#print axioms RelationalPerimeter.Relativity.Production.productive_family_append_returns_whole_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_family_append_keeps_whole_head
#print axioms RelationalPerimeter.Relativity.Production.productive_family_append_keeps_choices
#print axioms RelationalPerimeter.Relativity.Production.productive_family_precision_append_assoc
#print axioms RelationalPerimeter.Relativity.Production.productive_family_append_keeps_precisions
#print axioms RelationalPerimeter.Relativity.Production.productive_family_run_append_exact
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCourse.resumeRetaining
#print axioms RelationalPerimeter.Relativity.Production.productive_family_retained_is_whole_continuous_course
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint.asTriple
#print axioms RelationalPerimeter.Relativity.Production.productive_three_return_is_exact
#print axioms RelationalPerimeter.Relativity.Production.familyRequestOfTriple
#print axioms RelationalPerimeter.Relativity.Production.productive_three_mixed_head_endpoint
#print axioms RelationalPerimeter.Relativity.Production.productive_three_mixed_course_returns_whole_endpoint
/- AXIOM_AUDIT_END -/
