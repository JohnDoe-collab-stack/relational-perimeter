import RelationalPerimeter.Relativity.Production.FiniteProductiveParticipants

/-!
# Enlarge an already produced family without replaying its prefix

New responses start at the actual last certificate of the retained responses.
Restriction returns the original rich records. Canonical enlargement equals
the whole produced chain, not merely its numerical readings. Extra agreements
and received certificates remain inputs; no physical grouping is licensed.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open Arithmetic Analysis

def lastParticipant (first : ProductiveParticipant) : List ProductiveParticipant → ProductiveParticipant
  | [] => first
  | second :: rest => lastParticipant second rest

def appendParticipantAgreements (first : ProductiveParticipant) (members : List ProductiveParticipant)
    (agreements : participantAgreements first members) (more : List ProductiveParticipant)
    (next : participantAgreements (lastParticipant first members) more) :
    participantAgreements first (members ++ more) :=
  match members with
  | [] => next
  | second :: rest => ⟨agreements.1, appendParticipantAgreements second rest agreements.2 more next⟩
termination_by structural members

def ProductiveParticipants.append {first} (participants : ProductiveParticipants first)
    (more : ProductiveParticipants (lastParticipant first participants.members)) : ProductiveParticipants first :=
  ⟨participants.members ++ more.members,
    appendParticipantAgreements first participants.members participants.agreements more.members more.agreements⟩

def appendParticipantCertificates (members more : List ProductiveParticipant) {window : ReadingWindow}
    (before : participantCertificates members window) (next : participantCertificates more window) :
    participantCertificates (members ++ more) window :=
  match members with
  | [] => next
  | _ :: rest => ⟨before.1, appendParticipantCertificates rest more before.2 next⟩
termination_by structural members

def prefixParticipantCertificates (members more : List ProductiveParticipant) {window : ReadingWindow}
    (certificates : participantCertificates (members ++ more) window) : participantCertificates members window :=
  match members with
  | [] => ()
  | _ :: rest => ⟨certificates.1, prefixParticipantCertificates rest more certificates.2⟩
termination_by structural members

theorem participant_certificate_append_returns_the_whole_prefix (members more : List ProductiveParticipant)
    {window : ReadingWindow} (before : participantCertificates members window)
    (next : participantCertificates more window) :
    prefixParticipantCertificates members more (appendParticipantCertificates members more before next) = before := by
  induction members with
  | nil => cases before; rfl
  | cons second rest ih => exact congrArg (fun tail => (before.1, tail)) (ih before.2)

def lastParticipantCertificate (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse : ReadingWindow} {produced : first.Certificate fine}
    {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received) : (lastParticipant first members).Certificate fine :=
  match members with
  | [] => produced
  | second :: rest => lastParticipantCertificate second rest responses.2
termination_by structural members

def appendParticipantResponses (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse : ReadingWindow} {produced : first.Certificate fine}
    {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received) (more : List ProductiveParticipant)
    {nextReceived : participantCertificates more coarse}
    (next : participantResponses (lastParticipant first members) more
      (lastParticipantCertificate first members responses) nextReceived) :
    participantResponses first (members ++ more) produced
      (appendParticipantCertificates members more received nextReceived) :=
  match members with
  | [] => next
  | second :: rest => ⟨responses.1, appendParticipantResponses second rest responses.2 more next⟩
termination_by structural members

def prefixParticipantResponses (first : ProductiveParticipant) (members more : List ProductiveParticipant)
    {fine coarse : ReadingWindow} {produced : first.Certificate fine}
    {received : participantCertificates members coarse} {nextReceived : participantCertificates more coarse}
    (responses : participantResponses first (members ++ more) produced
      (appendParticipantCertificates members more received nextReceived)) :
    participantResponses first members produced received :=
  match members with
  | [] => ()
  | second :: rest => ⟨responses.1, prefixParticipantResponses second rest more responses.2⟩
termination_by structural members

theorem participant_response_append_returns_the_whole_prefix
    (first : ProductiveParticipant) (members more : List ProductiveParticipant)
    {fine coarse} {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received)
    {nextReceived : participantCertificates more coarse}
    (next : participantResponses (lastParticipant first members) more
      (lastParticipantCertificate first members responses) nextReceived) :
    prefixParticipantResponses first members more (appendParticipantResponses first members responses more next) = responses := by
  induction members generalizing first with
  | nil => cases responses; rfl
  | cons second rest ih => exact congrArg (Sigma.mk responses.1) (ih second responses.2 next)

theorem participant_response_append_returns_all_certificates
    (first : ProductiveParticipant) (members more : List ProductiveParticipant)
    {fine coarse} {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received)
    {nextReceived : participantCertificates more coarse}
    (next : participantResponses (lastParticipant first members) more
      (lastParticipantCertificate first members responses) nextReceived) :
    returnedParticipantCertificates first (members ++ more) (appendParticipantResponses first members responses more next) =
      appendParticipantCertificates members more (returnedParticipantCertificates first members responses)
        (returnedParticipantCertificates (lastParticipant first members) more next) := by
  induction members generalizing first with
  | nil => rfl
  | cons second rest ih => exact congrArg (fun tail => (responses.1.certificate, tail)) (ih second responses.2 next)

theorem participant_response_append_keeps_all_budgets
    (first : ProductiveParticipant) (members more : List ProductiveParticipant)
    {fine coarse} {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received)
    {nextReceived : participantCertificates more coarse}
    (next : participantResponses (lastParticipant first members) more
      (lastParticipantCertificate first members responses) nextReceived) :
    recordedParticipantBudgets first (members ++ more) (appendParticipantResponses first members responses more next) =
      recordedParticipantBudgets first members responses ++
        recordedParticipantBudgets (lastParticipant first members) more next := by
  induction members generalizing first with
  | nil => rfl
  | cons second rest ih => exact congrArg (List.cons responses.1.steps) (ih second responses.2 next)

/-- Execute only the new suffix, using the certificate actually stored last. -/
def extendParticipantResponses (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse} {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received)
    (more : ProductiveParticipants (lastParticipant first members))
    (nextReceived : participantCertificates more.members coarse) :
    participantResponses first (members ++ more.members) produced
      (appendParticipantCertificates members more.members received nextReceived) :=
  let last := lastParticipantCertificate first members responses
  let next := matchParticipantCertificates (lastParticipant first members) more.members more.agreements last nextReceived
  appendParticipantResponses first members responses more.members next

theorem participant_extension_keeps_the_whole_prefix
    (first : ProductiveParticipant) (members : List ProductiveParticipant)
    {fine coarse} {produced : first.Certificate fine} {received : participantCertificates members coarse}
    (responses : participantResponses first members produced received)
    (more : ProductiveParticipants (lastParticipant first members))
    (nextReceived : participantCertificates more.members coarse) :
    prefixParticipantResponses first members more.members
      (extendParticipantResponses first members responses more nextReceived) = responses :=
  participant_response_append_returns_the_whole_prefix ..

theorem participant_match_append_is_the_same_whole_chain
    (first : ProductiveParticipant) (members : List ProductiveParticipant)
    (agreements : participantAgreements first members) {fine coarse}
    (produced : first.Certificate fine) (received : participantCertificates members coarse)
    (more : ProductiveParticipants (lastParticipant first members))
    (nextReceived : participantCertificates more.members coarse) :
    matchParticipantCertificates first (members ++ more.members)
        (appendParticipantAgreements first members agreements more.members more.agreements) produced
        (appendParticipantCertificates members more.members received nextReceived) =
      extendParticipantResponses first members (matchParticipantCertificates first members agreements produced received)
        more nextReceived := by
  induction members generalizing first with
  | nil => rfl
  | cons second rest ih =>
      exact congrArg (Sigma.mk (produced.matchFromReceived received.1 agreements.1))
        (ih second agreements.2 (produced.matchFromReceived received.1 agreements.1).certificate received.2 more nextReceived)

def ProductiveFamilyEndpoint.enlarge {first participants}
    (received : @ProductiveFamilyEndpoint first participants)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    ProductiveFamilyEndpoint (participants.append more) :=
  ⟨received.window, received.firstCertificate,
    appendParticipantCertificates participants.members more.members received.certificates certificates⟩

def ProductiveFamilyPrecisionHead.enlarge {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    ProductiveFamilyPrecisionHead (received.enlarge more certificates) precision :=
  ⟨head.first, extendParticipantResponses first participants.members head.responses more certificates⟩

def ProductiveFamilyCoverHead.enlarge {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    ProductiveFamilyCoverHead (received.enlarge more certificates) cover :=
  ⟨head.chosen, head.chosenExact, extendParticipantResponses first participants.members head.responses more certificates⟩

theorem productive_precision_enlargement_keeps_the_whole_prefix {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    (head.enlarge more certificates).first = head.first ∧
      prefixParticipantResponses first participants.members more.members (head.enlarge more certificates).responses = head.responses :=
  ⟨rfl, participant_extension_keeps_the_whole_prefix ..⟩

theorem productive_cover_enlargement_keeps_the_whole_prefix {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    (head.enlarge more certificates).chosen = head.chosen ∧
      prefixParticipantResponses first participants.members more.members (head.enlarge more certificates).responses = head.responses :=
  ⟨rfl, participant_extension_keeps_the_whole_prefix ..⟩

theorem productive_precision_enlargement_is_the_whole_production {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (precision : Precision)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    (received.enlarge more certificates).continuePrecision precision =
      (received.continuePrecision precision).enlarge more certificates := by
  dsimp only [ProductiveFamilyEndpoint.continuePrecision, ProductiveFamilyPrecisionHead.enlarge,
    ProductiveFamilyEndpoint.enlarge, ProductiveParticipants.append]
  exact congrArg (fun responses => @ProductiveFamilyPrecisionHead.mk first
    (participants.append more) (received.enlarge more certificates) precision
    (received.firstCertificate.continuePrecision precision) responses)
    (participant_match_append_is_the_same_whole_chain first participants.members participants.agreements
      (received.firstCertificate.continuePrecision precision).certificate received.certificates more certificates)

theorem productive_cover_enlargement_is_the_whole_production {first participants}
    (received : @ProductiveFamilyEndpoint first participants) (cover : InstrumentalReadingCover received.window)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    (received.enlarge more certificates).selectCover cover =
      (received.selectCover cover).enlarge more certificates := by
  dsimp only [ProductiveFamilyEndpoint.selectCover, ProductiveFamilyCoverHead.enlarge,
    ProductiveFamilyEndpoint.enlarge, ProductiveParticipants.append]
  exact congrArg (fun responses => @ProductiveFamilyCoverHead.mk first
    (participants.append more) (received.enlarge more certificates) cover
    (cover.selectProductive received.firstCertificate) rfl responses)
    (participant_match_append_is_the_same_whole_chain first participants.members participants.agreements
      (cover.selectProductive received.firstCertificate).certificate received.certificates more certificates)

theorem productive_precision_enlargement_returns_the_old_certificates {first participants received precision}
    (head : @ProductiveFamilyPrecisionHead first participants received precision)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    prefixParticipantCertificates participants.members more.members (head.enlarge more certificates).endpoint.certificates =
      head.endpoint.certificates := by
  rw [show (head.enlarge more certificates).endpoint.certificates =
    appendParticipantCertificates participants.members more.members
      head.endpoint.certificates (returnedParticipantCertificates _ _
        (matchParticipantCertificates _ more.members more.agreements
          (lastParticipantCertificate first participants.members head.responses) certificates)) from
    participant_response_append_returns_all_certificates ..]
  exact participant_certificate_append_returns_the_whole_prefix ..

theorem productive_cover_enlargement_returns_the_old_certificates {first participants received cover}
    (head : @ProductiveFamilyCoverHead first participants received cover)
    (more : ProductiveParticipants (lastParticipant first participants.members))
    (certificates : participantCertificates more.members received.window) :
    prefixParticipantCertificates participants.members more.members (head.enlarge more certificates).endpoint.certificates =
      head.endpoint.certificates := by
  rw [show (head.enlarge more certificates).endpoint.certificates =
    appendParticipantCertificates participants.members more.members
      head.endpoint.certificates (returnedParticipantCertificates _ _
        (matchParticipantCertificates _ more.members more.agreements
          (lastParticipantCertificate first participants.members head.responses) certificates)) from
    participant_response_append_returns_all_certificates ..]
  exact participant_certificate_append_returns_the_whole_prefix ..

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.lastParticipant
#print axioms RelationalPerimeter.Relativity.Production.appendParticipantAgreements
#print axioms RelationalPerimeter.Relativity.Production.ProductiveParticipants.append
#print axioms RelationalPerimeter.Relativity.Production.appendParticipantCertificates
#print axioms RelationalPerimeter.Relativity.Production.prefixParticipantCertificates
#print axioms RelationalPerimeter.Relativity.Production.participant_certificate_append_returns_the_whole_prefix
#print axioms RelationalPerimeter.Relativity.Production.lastParticipantCertificate
#print axioms RelationalPerimeter.Relativity.Production.appendParticipantResponses
#print axioms RelationalPerimeter.Relativity.Production.prefixParticipantResponses
#print axioms RelationalPerimeter.Relativity.Production.participant_response_append_returns_the_whole_prefix
#print axioms RelationalPerimeter.Relativity.Production.participant_response_append_returns_all_certificates
#print axioms RelationalPerimeter.Relativity.Production.participant_response_append_keeps_all_budgets
#print axioms RelationalPerimeter.Relativity.Production.extendParticipantResponses
#print axioms RelationalPerimeter.Relativity.Production.participant_extension_keeps_the_whole_prefix
#print axioms RelationalPerimeter.Relativity.Production.participant_match_append_is_the_same_whole_chain
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyEndpoint.enlarge
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyPrecisionHead.enlarge
#print axioms RelationalPerimeter.Relativity.Production.ProductiveFamilyCoverHead.enlarge
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_enlargement_keeps_the_whole_prefix
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_enlargement_keeps_the_whole_prefix
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_enlargement_is_the_whole_production
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_enlargement_is_the_whole_production
#print axioms RelationalPerimeter.Relativity.Production.productive_precision_enlargement_returns_the_old_certificates
#print axioms RelationalPerimeter.Relativity.Production.productive_cover_enlargement_returns_the_old_certificates
/- AXIOM_AUDIT_END -/
