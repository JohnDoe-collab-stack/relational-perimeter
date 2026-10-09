import RelationalPerimeter
import Tests.Relativity.FiniteProductiveParticipantChecks

/-! Enlarge the already constituted three-participant client. Repetition
tests arbitrary finite suffix length, not additional physical sources. -/
set_option genInjectivity false
namespace Tests.Relativity.EnlargedProductiveParticipantChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open SharedProductiveCoverChecks FiniteProductiveParticipantChecks

def extraParticipants (steps count : Nat) := repeatedMembers ⟨_, third steps⟩ count

def extraCertificates (steps count : Nat) :=
  repeatedCertificates ⟨_, third steps⟩ (thirdCertificate steps) count

def enlargedReceived (steps count : Nat) :=
  (receivedFamily steps 0).enlarge (extraParticipants steps count) (extraCertificates steps count)

def enlargedPrecision (steps count : Nat) (precision : Precision) :=
  ((receivedFamily steps 0).continuePrecision precision).enlarge
    (extraParticipants steps count) (extraCertificates steps count)

def enlargedCover (steps count : Nat) (cover : InstrumentalReadingCover initialWindow) :=
  ((receivedFamily steps 0).selectCover cover).enlarge
    (extraParticipants steps count) (extraCertificates steps count)

theorem precision_enlargement_returns_the_whole_old_responses (steps count : Nat) (precision : Precision) :
    (enlargedPrecision steps count precision).first = ((receivedFamily steps 0).continuePrecision precision).first ∧
      prefixParticipantResponses _ _ (extraParticipants steps count).members
        (enlargedPrecision steps count precision).responses = ((receivedFamily steps 0).continuePrecision precision).responses :=
  productive_precision_enlargement_keeps_the_whole_prefix ..

theorem cover_enlargement_returns_the_whole_old_responses (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) :
    (enlargedCover steps count cover).chosen = ((receivedFamily steps 0).selectCover cover).chosen ∧
      prefixParticipantResponses _ _ (extraParticipants steps count).members
        (enlargedCover steps count cover).responses = ((receivedFamily steps 0).selectCover cover).responses :=
  productive_cover_enlargement_keeps_the_whole_prefix ..

theorem precision_enlargement_is_the_whole_production (steps count : Nat) (precision : Precision) :
    (enlargedReceived steps count).continuePrecision precision = enlargedPrecision steps count precision :=
  productive_precision_enlargement_is_the_whole_production ..

theorem cover_enlargement_is_the_whole_production (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) :
    (enlargedReceived steps count).selectCover cover = enlargedCover steps count cover :=
  productive_cover_enlargement_is_the_whole_production ..

theorem enlargement_returns_the_old_complete_certificates (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) :
    prefixParticipantCertificates _ (extraParticipants steps count).members
      (enlargedCover steps count cover).endpoint.certificates =
        ((receivedFamily steps 0).selectCover cover).endpoint.certificates :=
  productive_cover_enlargement_returns_the_old_certificates ..

theorem every_member_extends_its_received_prefix (steps count : Nat) (precision : Precision) :
    ProductiveFamilyExtension (enlargedReceived steps count) (enlargedPrecision steps count precision).endpoint :=
  (enlargedPrecision steps count precision).extendsReceived

theorem every_source_distinction_survives (steps count : Nat) (precision : Precision) :
    ParticipantBundleKeepsSources _ (enlargedPrecision steps count precision).endpoint.certificates :=
  participant_bundle_keeps_every_source_distinction ..

theorem every_later_reading_stays_in_the_received_window (steps count : Nat) (precision : Precision) (later : Nat) :
    initialWindow.Contains ((enlargedPrecision steps count precision).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      ParticipantBundleLaterInside _ (enlargedPrecision steps count precision).endpoint.certificates initialWindow later :=
  (enlargedPrecision steps count precision).allLaterInside later

theorem enlargement_keeps_the_requested_precision (steps count : Nat) (precision : Precision) :
    Rational.Le (enlargedPrecision steps count precision).endpoint.window.span precision.value :=
  (enlargedPrecision steps count precision).first.diameter

theorem enlargement_keeps_the_already_selected_left_leaf (steps count : Nat) :
    (enlargedCover steps count (request steps (received steps))).chosen.leaf.branches = [true] :=
  family_keeps_the_recorded_left_leaf steps

theorem enlargement_keeps_the_already_selected_right_leaf (steps count : Nat) :
    (enlargedCover steps count (oppositeRequest steps (received steps))).chosen.leaf.branches = [false] :=
  family_keeps_the_recorded_right_leaf steps

theorem resumption_uses_the_actual_enlarged_endpoint (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) (precision : Precision) :
    ProductiveFamilyExtension (enlargedReceived steps count)
      ((enlargedCover steps count cover).resumePrecision precision).endpoint :=
  productive_family_extensions_compose (enlargedCover steps count cover).extendsReceived
    ((enlargedCover steps count cover).resumePrecision precision).extendsReceived

end Tests.Relativity.EnlargedProductiveParticipantChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.extraParticipants
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.extraCertificates
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargedReceived
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargedPrecision
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargedCover
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.precision_enlargement_returns_the_whole_old_responses
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.cover_enlargement_returns_the_whole_old_responses
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.precision_enlargement_is_the_whole_production
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.cover_enlargement_is_the_whole_production
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargement_returns_the_old_complete_certificates
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.every_member_extends_its_received_prefix
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.every_source_distinction_survives
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.every_later_reading_stays_in_the_received_window
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargement_keeps_the_requested_precision
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargement_keeps_the_already_selected_left_leaf
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.enlargement_keeps_the_already_selected_right_leaf
#print axioms Tests.Relativity.EnlargedProductiveParticipantChecks.resumption_uses_the_actual_enlarged_endpoint
/- AXIOM_AUDIT_END -/
