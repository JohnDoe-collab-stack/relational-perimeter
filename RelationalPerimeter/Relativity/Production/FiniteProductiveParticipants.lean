import RelationalPerimeter.Relativity.Production.InterleavedProductiveWindows

/-!
# Joint produced windows for arbitrary finite participant families

Each member keeps its constituted presentation and received certificate.
Positive numerical agreements are declared inputs. One leader production is
shared through actual responses; each response extends its own received prefix
and supplies the next response's certificate. All recursions are structural on
the finite member list. Returned bundles support further precision and covers.
These instrumental laws do not identify sources or construct physical points.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

structure ProductiveParticipant where
  source : RelativePathState
  presentation : RelativePathPresentation source

abbrev ProductiveParticipant.Certificate (participant : ProductiveParticipant) (window : ReadingWindow) :=
  ProductiveWindowCertificate participant.presentation window

/-- Explicit positive agreements in production order, not source equalities. -/
def participantAgreements (first : ProductiveParticipant) : List ProductiveParticipant → Type
  | [] => Unit
  | second :: rest => Agreement first.presentation.numeric second.presentation.numeric × participantAgreements second rest

structure ProductiveParticipants (first : ProductiveParticipant) where
  members : List ProductiveParticipant
  agreements : participantAgreements first members

def ProductiveParticipants.done (first : ProductiveParticipant) : ProductiveParticipants first := ⟨[], ()⟩

def ProductiveParticipants.step {first} (second : ProductiveParticipant)
    (agreement : Agreement first.presentation.numeric second.presentation.numeric)
    (tail : ProductiveParticipants second) : ProductiveParticipants first :=
  ⟨second :: tail.members, agreement, tail.agreements⟩

def participantCertificates : List ProductiveParticipant → ReadingWindow → Type
  | [], _ => Unit
  | second :: rest, window => second.Certificate window × participantCertificates rest window

def participantResponses (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse : ReadingWindow} (produced : first.Certificate fine)
    (received : participantCertificates members coarse) : Type :=
  match members with
  | [] => Unit
  | _ :: rest => (head : ProductiveReceivedWindowMatch produced received.1) ×
      participantResponses _ rest head.certificate received.2
termination_by structural members

/-- Certify once, bind the actual result, then pass it to the next link. -/
def matchParticipantCertificates (first : ProductiveParticipant) (members : List ProductiveParticipant)
    (agreements : participantAgreements first members) {fine coarse : ReadingWindow}
    (produced : first.Certificate fine) (received : participantCertificates members coarse) :
    participantResponses first members produced received :=
  match members with
  | [] => ()
  | second :: rest =>
      let head := produced.matchFromReceived received.1 agreements.1
      let tail := matchParticipantCertificates second rest agreements.2 head.certificate received.2
      ⟨head, tail⟩
termination_by structural members

def returnedParticipantCertificates (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse : ReadingWindow} {produced : first.Certificate fine}
    {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received) : participantCertificates members fine :=
  match members with
  | [] => ()
  | second :: rest => ⟨responses.1.certificate, returnedParticipantCertificates second rest responses.2⟩
termination_by structural members

def recordedParticipantBudgets (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse : ReadingWindow} {produced : first.Certificate fine}
    {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received) : List Nat :=
  match members with
  | [] => []
  | second :: rest => responses.1.steps :: recordedParticipantBudgets second rest responses.2
termination_by structural members

def ParticipantBundleExtension (members : List ProductiveParticipant) {coarse fine : ReadingWindow}
    (received : participantCertificates members coarse) (returned : participantCertificates members fine) : Prop :=
  match members with
  | [] => True
  | second :: rest =>
      (∃ steps, returned.1.realization = received.1.realization.evolve second.presentation.rule steps) ∧
        ParticipantBundleExtension rest received.2 returned.2
termination_by structural members

theorem participant_responses_extend_every_received_prefix
    (first : ProductiveParticipant) (members : List ProductiveParticipant) {fine coarse : ReadingWindow}
    {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received) :
    ParticipantBundleExtension members received (returnedParticipantCertificates first members responses) := by
  induction members generalizing first with
  | nil => exact True.intro
  | cons second rest ih => exact ⟨⟨responses.1.steps, responses.1.runExact⟩, ih second responses.2⟩

theorem participant_response_budgets_cover_every_member
    (first : ProductiveParticipant) (members : List ProductiveParticipant) {fine coarse : ReadingWindow}
    {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received) :
    (recordedParticipantBudgets first members responses).length = members.length := by
  induction members generalizing first with
  | nil => rfl
  | cons second rest ih => exact congrArg (fun count => count + 1) (ih second responses.2)

theorem participant_bundle_extensions_compose (members : List ProductiveParticipant)
    {one two three : ReadingWindow}
    {before : participantCertificates members one} {middle : participantCertificates members two}
    {after : participantCertificates members three}
    (first : ParticipantBundleExtension members before middle)
    (second : ParticipantBundleExtension members middle after) :
    ParticipantBundleExtension members before after := by
  induction members with
  | nil => exact True.intro
  | cons participant rest ih =>
      obtain ⟨⟨left, leftExact⟩, remainingLeft⟩ := first
      obtain ⟨⟨right, rightExact⟩, remainingRight⟩ := second
      refine ⟨⟨left + right, ?_⟩, ih remainingLeft remainingRight⟩
      rw [rightExact, leftExact, relative_evolution_compose]

def ParticipantBundleLaterInside (members : List ProductiveParticipant) {window : ReadingWindow}
    (certificates : participantCertificates members window) (constraint : ReadingWindow) (later : Nat) : Prop :=
  match members with
  | [] => True
  | _ :: rest =>
      constraint.Contains (certificates.1.advance later).realization.state.reading.value ∧
        ParticipantBundleLaterInside rest certificates.2 constraint later
termination_by structural members

theorem participant_bundle_all_later_inside (members : List ProductiveParticipant) {window : ReadingWindow}
    (certificates : participantCertificates members window) (later : Nat) :
    ParticipantBundleLaterInside members certificates window later := by
  induction members with
  | nil => exact True.intro
  | cons second rest ih =>
      exact ⟨(bracket_contains_endpoints (certificates.1.advance later).inside).1, ih certificates.2⟩

theorem participant_bundle_restrict_later_inside (members : List ProductiveParticipant)
    {window constraint : ReadingWindow} (certificates : participantCertificates members window)
    (later : Nat) (refinement : WindowRefinement constraint window) :
    ParticipantBundleLaterInside members certificates constraint later := by
  induction members with
  | nil => exact True.intro
  | cons second rest ih =>
      exact ⟨refinement.contains (bracket_contains_endpoints (certificates.1.advance later).inside).1,
        ih certificates.2⟩

theorem productive_participant_head_and_successor_exact
    (first second : ProductiveParticipant) (rest : List ProductiveParticipant)
    (agreements : Agreement first.presentation.numeric second.presentation.numeric × participantAgreements second rest)
    {fine coarse} (produced : first.Certificate fine)
    (received : second.Certificate coarse × participantCertificates rest coarse) :
    matchParticipantCertificates first (second :: rest) agreements produced received =
      ⟨produced.matchFromReceived received.1 agreements.1,
        matchParticipantCertificates second rest agreements.2
          (produced.matchFromReceived received.1 agreements.1).certificate received.2⟩ := rfl

theorem productive_participant_head_independent_of_other_members
    (first second : ProductiveParticipant) (one two : List ProductiveParticipant)
    (agreement : Agreement first.presentation.numeric second.presentation.numeric)
    (oneAgreements : participantAgreements second one) (twoAgreements : participantAgreements second two)
    {fine coarse} (produced : first.Certificate fine) (received : second.Certificate coarse)
    (oneCertificates : participantCertificates one coarse) (twoCertificates : participantCertificates two coarse) :
    (matchParticipantCertificates first (second :: one) ⟨agreement, oneAgreements⟩ produced
      ⟨received, oneCertificates⟩).1 =
    (matchParticipantCertificates first (second :: two) ⟨agreement, twoAgreements⟩ produced
      ⟨received, twoCertificates⟩).1 := rfl

/-- Preservation refers to transported occurrences, not equality of readings. -/
def ParticipantBundleKeepsSources (members : List ProductiveParticipant) {window : ReadingWindow}
    (certificates : participantCertificates members window) : Prop :=
  match members with
  | [] => True
  | participant :: rest =>
      (historyTransport certificates.1.realization.chain.history).references participant.source.reading.arrivals.first ≠
        (historyTransport certificates.1.realization.chain.history).references participant.source.reading.arrivals.second ∧
      ParticipantBundleKeepsSources rest certificates.2
termination_by structural members

theorem participant_bundle_keeps_every_source_distinction (members : List ProductiveParticipant)
    {window : ReadingWindow} (certificates : participantCertificates members window) :
    ParticipantBundleKeepsSources members certificates := by
  induction members with
  | nil => exact True.intro
  | cons participant rest ih => exact ⟨relative_refinement_chain_keeps_sources _, ih certificates.2⟩

structure ProductiveFamilyEndpoint {first} (participants : ProductiveParticipants first) where
  window : ReadingWindow
  firstCertificate : first.Certificate window
  certificates : participantCertificates participants.members window

structure ProductiveFamilyPrecisionHead {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (precision : Precision) where
  first : ProductivePrecisionContinuation received.firstCertificate precision
  responses : participantResponses _ participants.members first.certificate received.certificates

def ProductiveFamilyEndpoint.continuePrecision {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (precision : Precision) :
    ProductiveFamilyPrecisionHead received precision :=
  let head := received.firstCertificate.continuePrecision precision
  let responses := matchParticipantCertificates first participants.members participants.agreements
    head.certificate received.certificates
  ⟨head, responses⟩

def ProductiveFamilyPrecisionHead.endpoint {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision) :
    ProductiveFamilyEndpoint participants :=
  ⟨head.first.window, head.first.certificate, returnedParticipantCertificates first participants.members head.responses⟩

structure ProductiveFamilyCoverHead {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (cover : InstrumentalReadingCover received.window) where
  chosen : CoveredProductivePresentation first.presentation cover
  chosenExact : chosen = cover.selectProductive received.firstCertificate
  responses : participantResponses first participants.members chosen.certificate received.certificates

def ProductiveFamilyEndpoint.selectCover {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (cover : InstrumentalReadingCover received.window) : ProductiveFamilyCoverHead received cover :=
  let chosen := cover.selectProductive received.firstCertificate
  let responses := matchParticipantCertificates first participants.members participants.agreements
    chosen.certificate received.certificates
  ⟨chosen, rfl, responses⟩

def ProductiveFamilyCoverHead.endpoint {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) : ProductiveFamilyEndpoint participants :=
  ⟨head.chosen.window, head.chosen.certificate, returnedParticipantCertificates first participants.members head.responses⟩

def ProductiveFamilyExtension {first participants}
    (before after : @ProductiveFamilyEndpoint first participants) : Prop :=
  (∃ steps, after.firstCertificate.realization = before.firstCertificate.realization.evolve first.presentation.rule steps) ∧
    ParticipantBundleExtension participants.members before.certificates after.certificates

theorem productive_family_extensions_compose {first participants}
    {before middle after : @ProductiveFamilyEndpoint first participants}
    (one : ProductiveFamilyExtension before middle) (two : ProductiveFamilyExtension middle after) :
    ProductiveFamilyExtension before after := by
  obtain ⟨⟨left, leftExact⟩, remainingLeft⟩ := one
  obtain ⟨⟨right, rightExact⟩, remainingRight⟩ := two
  refine ⟨⟨left + right, ?_⟩,
    participant_bundle_extensions_compose participants.members remainingLeft remainingRight⟩
  rw [rightExact, leftExact, relative_evolution_compose]

theorem ProductiveFamilyPrecisionHead.refinement {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision) :
    WindowRefinement received.window head.endpoint.window := head.first.refinement

theorem ProductiveFamilyCoverHead.refinement {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) :
    WindowRefinement received.window head.endpoint.window := head.chosen.leaf.refinement

theorem ProductiveFamilyPrecisionHead.extendsReceived {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision) :
    ProductiveFamilyExtension received head.endpoint :=
  ⟨⟨precision.half.denominator, head.first.runExact⟩,
    participant_responses_extend_every_received_prefix first participants.members head.responses⟩

theorem ProductiveFamilyCoverHead.extendsReceived {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) :
    ProductiveFamilyExtension received head.endpoint := by
  obtain ⟨steps, _, run⟩ := productive_cover_extends_only_its_received_prefix cover received.firstCertificate
  refine ⟨⟨steps, ?_⟩, participant_responses_extend_every_received_prefix first participants.members head.responses⟩
  change head.chosen.certificate.realization = _
  rw [head.chosenExact]
  exact run

theorem ProductiveFamilyPrecisionHead.allLaterInside {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision) (later : Nat) :
    received.window.Contains (head.endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      ParticipantBundleLaterInside participants.members head.endpoint.certificates received.window later :=
  ⟨head.first.refinement.contains (bracket_contains_endpoints (head.endpoint.firstCertificate.advance later).inside).1,
    participant_bundle_restrict_later_inside participants.members head.endpoint.certificates later head.first.refinement⟩

theorem ProductiveFamilyCoverHead.allLaterInside {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) (later : Nat) :
    received.window.Contains (head.endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      ParticipantBundleLaterInside participants.members head.endpoint.certificates received.window later :=
  ⟨head.chosen.leaf.refinement.contains (bracket_contains_endpoints (head.endpoint.firstCertificate.advance later).inside).1,
    participant_bundle_restrict_later_inside participants.members head.endpoint.certificates later head.chosen.leaf.refinement⟩

def ProductiveFamilyPrecisionHead.resumePrecision {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision) (next : Precision) :
    ProductiveFamilyPrecisionHead head.endpoint next := head.endpoint.continuePrecision next

def ProductiveFamilyCoverHead.resumePrecision {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) (next : Precision) :
    ProductiveFamilyPrecisionHead head.endpoint next := head.endpoint.continuePrecision next

theorem productive_family_resumed_first_is_the_actual_prefix {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover) (precision : Precision) :
    (head.resumePrecision precision).first.certificate.realization =
      head.endpoint.firstCertificate.realization.evolve first.presentation.rule precision.half.denominator := rfl

theorem productive_family_precision_cover_keeps_the_requested_bound {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (precision : Precision)
    (cover : InstrumentalReadingCover (received.continuePrecision precision).endpoint.window) :
    Rational.Le (((received.continuePrecision precision).endpoint.selectCover cover).endpoint.window.span)
      precision.value :=
  Rational.le_trans ((received.continuePrecision precision).endpoint.selectCover cover).refinement.span_le
    (received.continuePrecision precision).first.diameter

theorem productive_family_cover_precision_extends_every_original_prefix {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (cover : InstrumentalReadingCover received.window)
    (precision : Precision) :
    ProductiveFamilyExtension received ((received.selectCover cover).resumePrecision precision).endpoint :=
  productive_family_extensions_compose (received.selectCover cover).extendsReceived
    ((received.selectCover cover).resumePrecision precision).extendsReceived

/-- Read all three stored certificates. No new master or producer is invoked. -/
def ProductiveTripleEndpoint.asFamily {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ProductiveFamilyEndpoint (first := ⟨source, first⟩)
      (.step ⟨target, second⟩ firstAgreement (.step ⟨other, third⟩ secondAgreement (.done _))) :=
  ⟨received.window, received.firstCertificate, received.secondCertificate, received.thirdCertificate, ()⟩

theorem productive_three_precision_certificates_are_the_same
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third) (precision : Precision)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ((received.asFamily firstAgreement secondAgreement).continuePrecision precision).first =
        (received.continueSharedPrecision precision firstAgreement secondAgreement).first ∧
      ((received.asFamily firstAgreement secondAgreement).continuePrecision precision).endpoint.certificates.1 =
        (received.continueSharedPrecision precision firstAgreement secondAgreement).second.certificate ∧
      ((received.asFamily firstAgreement secondAgreement).continuePrecision precision).endpoint.certificates.2.1 =
        (received.continueSharedPrecision precision firstAgreement secondAgreement).third.certificate := ⟨rfl, rfl, rfl⟩

theorem productive_three_cover_certificates_are_the_same
    {source target other first second third}
    (received : @ProductiveTripleEndpoint source target other first second third)
    (cover : InstrumentalReadingCover received.window)
    (firstAgreement : Agreement first.numeric second.numeric)
    (secondAgreement : Agreement second.numeric third.numeric) :
    ((received.asFamily firstAgreement secondAgreement).selectCover cover).chosen =
        (received.selectSharedCover cover firstAgreement secondAgreement).chosen ∧
      ((received.asFamily firstAgreement secondAgreement).selectCover cover).endpoint.certificates.1 =
        (received.selectSharedCover cover firstAgreement secondAgreement).second.certificate ∧
      ((received.asFamily firstAgreement secondAgreement).selectCover cover).endpoint.certificates.2.1 =
        (received.selectSharedCover cover firstAgreement secondAgreement).third.certificate := ⟨rfl, rfl, rfl⟩

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.ProductiveParticipant
#print axioms RelationalPerimeter.Relativity.Production.ProductiveParticipant.Certificate
#print axioms RelationalPerimeter.Relativity.Production.participantAgreements
#print axioms RelationalPerimeter.Relativity.Production.ProductiveParticipants
#print axioms RelationalPerimeter.Relativity.Production.ProductiveParticipants.done
#print axioms RelationalPerimeter.Relativity.Production.ProductiveParticipants.step
#print axioms RelationalPerimeter.Relativity.Production.participantCertificates
#print axioms RelationalPerimeter.Relativity.Production.participantResponses
#print axioms RelationalPerimeter.Relativity.Production.matchParticipantCertificates
#print axioms RelationalPerimeter.Relativity.Production.returnedParticipantCertificates
#print axioms RelationalPerimeter.Relativity.Production.recordedParticipantBudgets
#print axioms RelationalPerimeter.Relativity.Production.ParticipantBundleExtension
#print axioms RelationalPerimeter.Relativity.Production.participant_responses_extend_every_received_prefix
#print axioms RelationalPerimeter.Relativity.Production.participant_response_budgets_cover_every_member
#print axioms RelationalPerimeter.Relativity.Production.participant_bundle_extensions_compose
#print axioms RelationalPerimeter.Relativity.Production.ParticipantBundleLaterInside
#print axioms RelationalPerimeter.Relativity.Production.participant_bundle_all_later_inside
#print axioms RelationalPerimeter.Relativity.Production.participant_bundle_restrict_later_inside
#print axioms RelationalPerimeter.Relativity.Production.productive_participant_head_and_successor_exact
#print axioms RelationalPerimeter.Relativity.Production.productive_participant_head_independent_of_other_members
#print axioms RelationalPerimeter.Relativity.Production.ParticipantBundleKeepsSources
#print axioms RelationalPerimeter.Relativity.Production.participant_bundle_keeps_every_source_distinction
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint.continuePrecision
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint.selectCover
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.endpoint
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyExtension
#print axioms RelationalPerimeter.Relativity.Production.productive_family_extensions_compose
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.refinement
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.extendsReceived
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.allLaterInside
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.allLaterInside
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.resumePrecision
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.resumePrecision
#print axioms RelationalPerimeter.Relativity.Production.productive_family_resumed_first_is_the_actual_prefix
#print axioms RelationalPerimeter.Relativity.Production.productive_family_precision_cover_keeps_the_requested_bound
#print axioms RelationalPerimeter.Relativity.Production.productive_family_cover_precision_extends_every_original_prefix
#print axioms RelationalPerimeter.Relativity.Production.ProductiveTripleEndpoint.asFamily
#print axioms RelationalPerimeter.Relativity.Production.productive_three_precision_certificates_are_the_same
#print axioms RelationalPerimeter.Relativity.Production.productive_three_cover_certificates_are_the_same
/- AXIOM_AUDIT_END -/
