import RelationalPerimeter
import Tests.Relativity.InterleavedProductiveWindowChecks

/-! Clients reuse the existing received prefixes. Repetition tests unbounded
finite length, not the existence of new distinct physical participants.
The general laws also cover heterogeneous participant lists. -/
set_option genInjectivity false
namespace Tests.Relativity.FiniteProductiveParticipantChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open SharedProductiveCoverChecks

def repeatedMembers (participant : ProductiveParticipant) : Nat → ProductiveParticipants participant
  | 0 => .done participant
  | count + 1 => .step participant (.reflexive participant.presentation.numeric) (repeatedMembers participant count)

def repeatedCertificates (participant : ProductiveParticipant) {window : ReadingWindow}
    (certificate : participant.Certificate window) :
    (count : Nat) → participantCertificates (repeatedMembers participant count).members window
  | 0 => ()
  | count + 1 => ⟨certificate, repeatedCertificates participant certificate count⟩

def receivedFamily (steps count : Nat) :
    ProductiveFamilyEndpoint (first := ⟨_, first⟩)
      (.step ⟨_, second⟩ agreement
        (.step ⟨_, third steps⟩ (secondThirdAgreement steps) (repeatedMembers ⟨_, third steps⟩ count))) :=
  ⟨initialWindow, firstCertificate, secondCertificate, thirdCertificate steps,
    repeatedCertificates ⟨_, third steps⟩ (thirdCertificate steps) count⟩

theorem every_finite_length_is_constructed (steps count : Nat) (precision : Precision) :
    (recordedParticipantBudgets _ _ ((receivedFamily steps count).continuePrecision precision).responses).length = count + 2 := by
  rw [participant_response_budgets_cover_every_member]
  change (repeatedMembers ⟨_, third steps⟩ count).members.length + 1 + 1 = count + 2
  have length : (repeatedMembers ⟨_, third steps⟩ count).members.length = count := by
    induction count with
    | zero => rfl
    | succ count ih => exact congrArg (fun size => size + 1) ih
  rw [length]

theorem every_received_prefix_is_extended (steps count : Nat) (precision : Precision) :
    ProductiveFamilyExtension (receivedFamily steps count)
      ((receivedFamily steps count).continuePrecision precision).endpoint :=
  ((receivedFamily steps count).continuePrecision precision).extendsReceived

theorem every_returned_source_distinction_survives (steps count : Nat) (precision : Precision) :
    ParticipantBundleKeepsSources _ ((receivedFamily steps count).continuePrecision precision).endpoint.certificates :=
  participant_bundle_keeps_every_source_distinction ..

theorem every_later_reading_remains_inside (steps count : Nat) (precision : Precision) (later : Nat) :
    initialWindow.Contains
        (((receivedFamily steps count).continuePrecision precision).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      ParticipantBundleLaterInside _ ((receivedFamily steps count).continuePrecision precision).endpoint.certificates
        initialWindow later :=
  ((receivedFamily steps count).continuePrecision precision).allLaterInside later

theorem three_precision_returns_the_same_complete_certificates (steps : Nat) (precision : Precision) :
    ((receivedFamily steps 0).continuePrecision precision).first =
        ((received steps).continueSharedPrecision precision agreement (secondThirdAgreement steps)).first ∧
      ((receivedFamily steps 0).continuePrecision precision).endpoint.certificates.1 =
        ((received steps).continueSharedPrecision precision agreement (secondThirdAgreement steps)).second.certificate ∧
      ((receivedFamily steps 0).continuePrecision precision).endpoint.certificates.2.1 =
        ((received steps).continueSharedPrecision precision agreement (secondThirdAgreement steps)).third.certificate :=
  productive_three_precision_certificates_are_the_same (received steps) precision agreement (secondThirdAgreement steps)

theorem three_cover_returns_the_same_complete_certificates (steps : Nat)
    (cover : InstrumentalReadingCover initialWindow) :
    ((receivedFamily steps 0).selectCover cover).chosen =
        ((received steps).selectSharedCover cover agreement (secondThirdAgreement steps)).chosen ∧
      ((receivedFamily steps 0).selectCover cover).endpoint.certificates.1 =
        ((received steps).selectSharedCover cover agreement (secondThirdAgreement steps)).second.certificate ∧
      ((receivedFamily steps 0).selectCover cover).endpoint.certificates.2.1 =
        ((received steps).selectSharedCover cover agreement (secondThirdAgreement steps)).third.certificate :=
  productive_three_cover_certificates_are_the_same (received steps) cover agreement (secondThirdAgreement steps)

theorem family_keeps_the_recorded_left_leaf (steps : Nat) :
    ((receivedFamily steps 0).selectCover (request steps (received steps))).chosen.leaf.branches = [true] := by
  change ((received steps).selectSharedCover (request steps (received steps)) agreement
    (secondThirdAgreement steps)).chosen.leaf.branches = [true]
  exact one_closed_cover_selects_left steps

theorem family_keeps_the_recorded_right_leaf (steps : Nat) :
    ((receivedFamily steps 0).selectCover (oppositeRequest steps (received steps))).chosen.leaf.branches = [false] := by
  change ((received steps).selectSharedCover (oppositeRequest steps (received steps)) agreement
    (secondThirdAgreement steps)).chosen.leaf.branches = [false]
  exact the_other_closed_cover_selects_right steps

theorem cover_then_precision_uses_the_received_family (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) (precision : Precision) :
    ProductiveFamilyExtension (receivedFamily steps count)
      (((receivedFamily steps count).selectCover cover).resumePrecision precision).endpoint :=
  productive_family_cover_precision_extends_every_original_prefix ..

theorem precision_then_cover_preserves_the_bound (steps count : Nat) (precision : Precision)
    (cover : InstrumentalReadingCover ((receivedFamily steps count).continuePrecision precision).endpoint.window) :
    Rational.Le ((((receivedFamily steps count).continuePrecision precision).endpoint.selectCover cover).endpoint.window.span)
      precision.value :=
  productive_family_precision_cover_keeps_the_requested_bound ..

theorem existing_mixed_endpoint_is_received_without_reproduction (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) :
    ((InterleavedProductiveWindowChecks.mixed steps requests).endpoint.asFamily
      agreement (secondThirdAgreement steps)).firstCertificate =
        (InterleavedProductiveWindowChecks.mixed steps requests).endpoint.firstCertificate ∧
      ((InterleavedProductiveWindowChecks.mixed steps requests).endpoint.asFamily
        agreement (secondThirdAgreement steps)).certificates.2.1 =
        (InterleavedProductiveWindowChecks.mixed steps requests).endpoint.thirdCertificate := ⟨rfl, rfl⟩

theorem resumption_extends_the_existing_mixed_endpoint (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) (precision : Precision) :
    ProductiveFamilyExtension
      ((InterleavedProductiveWindowChecks.mixed steps requests).endpoint.asFamily agreement (secondThirdAgreement steps))
      (((InterleavedProductiveWindowChecks.mixed steps requests).endpoint.asFamily
        agreement (secondThirdAgreement steps)).continuePrecision precision).endpoint :=
  (((InterleavedProductiveWindowChecks.mixed steps requests).endpoint.asFamily
    agreement (secondThirdAgreement steps)).continuePrecision precision).extendsReceived

end Tests.Relativity.FiniteProductiveParticipantChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.repeatedMembers
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.repeatedCertificates
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.receivedFamily
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.every_finite_length_is_constructed
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.every_received_prefix_is_extended
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.every_returned_source_distinction_survives
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.every_later_reading_remains_inside
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.three_precision_returns_the_same_complete_certificates
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.three_cover_returns_the_same_complete_certificates
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.family_keeps_the_recorded_left_leaf
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.family_keeps_the_recorded_right_leaf
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.cover_then_precision_uses_the_received_family
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.precision_then_cover_preserves_the_bound
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.existing_mixed_endpoint_is_received_without_reproduction
#print axioms Tests.Relativity.FiniteProductiveParticipantChecks.resumption_extends_the_existing_mixed_endpoint
/- AXIOM_AUDIT_END -/
