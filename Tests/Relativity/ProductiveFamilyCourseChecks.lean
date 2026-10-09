import RelationalPerimeter
import Tests.Relativity.EnlargedProductiveParticipantChecks

/-! Reuse the received sources and their actual enlarged productions.
Arbitrary finite repetitions test suffix length, not new physical sources.
Mixed requests read the current window; no runtime complexity is claimed. -/
set_option genInjectivity false
namespace Tests.Relativity.ProductiveFamilyCourseChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open SharedProductiveCoverChecks FiniteProductiveParticipantChecks
open EnlargedProductiveParticipantChecks

abbrev participants (steps count : Nat) : ProductiveParticipants ⟨_, first⟩ :=
  .step ⟨_, second⟩ agreement
    (.step ⟨_, third steps⟩ (secondThirdAgreement steps) (repeatedMembers ⟨_, third steps⟩ count))

def precisionRequest {first} (participants : ProductiveParticipants first) (precision : Precision) :
    ProductiveFamilyRequest participants := fun _ => .precision precision

def adaptiveCoverRequest {first} (participants : ProductiveParticipants first) :
    ProductiveFamilyRequest participants := fun received => .cover (
  if lower : RationalStrictLess received.window.lower Rational.zero then
    if upper : RationalStrictLess Rational.one received.window.upper then
      .split ⟨Rational.zero, Rational.one, lower, by decide, upper⟩ (.identity _) (.identity _)
    else .identity _
  else .identity _)

def mixed (steps count : Nat) (requests : List (ProductiveFamilyRequest (participants steps count))) :=
  (receivedFamily steps count).runWindows requests

theorem head_is_independent_of_the_completed_horizon (steps count : Nat)
    (request : ProductiveFamilyRequest (participants steps count))
    (one two : List (ProductiveFamilyRequest (participants steps count))) :
    (mixed steps count (request :: one)).headProduction = (mixed steps count (request :: two)).headProduction :=
  productive_family_head_horizon_independent ..

theorem every_received_prefix_is_extended (steps count : Nat)
    (requests : List (ProductiveFamilyRequest (participants steps count))) :
    ProductiveFamilyExtension (receivedFamily steps count) (mixed steps count requests).endpoint :=
  (mixed steps count requests).extendsReceived

theorem every_requested_precision_survives (steps count : Nat)
    (requests : List (ProductiveFamilyRequest (participants steps count)))
    (precision : Precision) (present : precision ∈ (mixed steps count requests).requestedPrecisions) :
    Rational.Le (mixed steps count requests).endpoint.window.span precision.value :=
  (mixed steps count requests).allRequestedBounds precision present

theorem fine_cover_coarse_still_meets_the_first_precision (steps count : Nat) (fine coarse : Precision) :
    Rational.Le (mixed steps count [precisionRequest _ fine, adaptiveCoverRequest _,
      precisionRequest _ coarse]).endpoint.window.span fine.value :=
  (mixed steps count [precisionRequest _ fine, adaptiveCoverRequest _, precisionRequest _ coarse]).allRequestedBounds
    fine (.head _)

theorem every_later_reading_stays_in_the_received_window (steps count : Nat)
    (requests : List (ProductiveFamilyRequest (participants steps count))) (later : Nat) :
    initialWindow.Contains ((mixed steps count requests).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
      ParticipantBundleLaterInside _ (mixed steps count requests).endpoint.certificates initialWindow later :=
  (mixed steps count requests).allLaterReadings later

theorem every_source_distinction_survives (steps count : Nat)
    (requests : List (ProductiveFamilyRequest (participants steps count))) :
    ParticipantBundleKeepsSources _ (mixed steps count requests).endpoint.certificates :=
  (mixed steps count requests).keepsSources.2

theorem retaining_is_the_whole_course (steps count : Nat)
    (requests more : List (ProductiveFamilyRequest (participants steps count))) :
    (mixed steps count requests).resumeRetaining more = mixed steps count (requests ++ more) :=
  productive_family_retained_is_whole_continuous_course ..

theorem retaining_keeps_the_old_complete_head (steps count : Nat)
    (request : ProductiveFamilyRequest (participants steps count))
    (requests more : List (ProductiveFamilyRequest (participants steps count))) :
    ((mixed steps count (request :: requests)).resumeRetaining more).headProduction =
      (mixed steps count (request :: requests)).headProduction :=
  productive_family_append_keeps_whole_head ..

theorem retaining_keeps_all_recorded_choices (steps count : Nat)
    (requests more : List (ProductiveFamilyRequest (participants steps count))) :
    ((mixed steps count requests).resumeRetaining more).recordedChoices =
      (mixed steps count requests).recordedChoices ++
        ((mixed steps count requests).endpoint.runWindows more).recordedChoices :=
  productive_family_append_keeps_choices ..

theorem retaining_keeps_all_recorded_precisions (steps count : Nat)
    (requests more : List (ProductiveFamilyRequest (participants steps count))) :
    ((mixed steps count requests).resumeRetaining more).requestedPrecisions =
      (mixed steps count requests).requestedPrecisions ++
        ((mixed steps count requests).endpoint.runWindows more).requestedPrecisions :=
  productive_family_append_keeps_precisions ..

theorem three_returns_the_old_complete_endpoint (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) :
    (mixed steps 0 (requests.map (fun request => familyRequestOfTriple request agreement (secondThirdAgreement steps)))).endpoint =
      ((received steps).runWindows requests agreement (secondThirdAgreement steps)).endpoint.asFamily
        agreement (secondThirdAgreement steps) :=
  productive_three_mixed_course_returns_whole_endpoint (received steps) requests agreement (secondThirdAgreement steps)

theorem left_leaf_remains_recorded (steps count : Nat) :
    (mixed steps count [adaptiveCoverRequest _]).headProduction.recordedChoice = some [true] := by
  change some (((receivedFamily steps 0).selectCover (request steps (received steps))).chosen.leaf.branches) = some [true]
  exact congrArg some (family_keeps_the_recorded_left_leaf steps)

theorem right_leaf_remains_recorded (steps : Nat) :
    (mixed steps 0 [familyRequestOfTriple (coverWindowRequest (oppositeRequest steps))
      agreement (secondThirdAgreement steps)]).headProduction.recordedChoice = some [false] := by
  change some (((receivedFamily steps 0).selectCover (oppositeRequest steps (received steps))).chosen.leaf.branches) = some [false]
  exact congrArg some (family_keeps_the_recorded_right_leaf steps)

theorem enlarged_cover_feeds_the_actual_next_course (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) (precision : Precision) :
    (((enlargedCover steps count cover).endpoint.runWindows [precisionRequest _ precision]).headProduction).production.first =
      (enlargedCover steps count cover).endpoint.firstCertificate.continuePrecision precision := rfl

theorem enlarged_course_extends_all_original_prefixes (steps count : Nat)
    (cover : InstrumentalReadingCover initialWindow) (precision : Precision) :
    ProductiveFamilyExtension (enlargedReceived steps count)
      ((enlargedCover steps count cover).endpoint.runWindows
        [precisionRequest _ precision, adaptiveCoverRequest _]).endpoint :=
  productive_family_extensions_compose (enlargedCover steps count cover).extendsReceived
    (((enlargedCover steps count cover).endpoint.runWindows
      [precisionRequest _ precision, adaptiveCoverRequest _]).extendsReceived)

end Tests.Relativity.ProductiveFamilyCourseChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.participants
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.precisionRequest
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.adaptiveCoverRequest
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.mixed
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.head_is_independent_of_the_completed_horizon
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.every_received_prefix_is_extended
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.every_requested_precision_survives
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.fine_cover_coarse_still_meets_the_first_precision
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.every_later_reading_stays_in_the_received_window
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.every_source_distinction_survives
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.retaining_is_the_whole_course
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.retaining_keeps_the_old_complete_head
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.retaining_keeps_all_recorded_choices
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.retaining_keeps_all_recorded_precisions
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.three_returns_the_old_complete_endpoint
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.left_leaf_remains_recorded
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.right_leaf_remains_recorded
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.enlarged_cover_feeds_the_actual_next_course
#print axioms Tests.Relativity.ProductiveFamilyCourseChecks.enlarged_course_extends_all_original_prefixes
/- AXIOM_AUDIT_END -/
