import RelationalPerimeter
import Tests.Relativity.SharedProductiveCoverChecks

/-! Clients reuse the existing three received sources. Arbitrary finite mixed
requests keep their actual prefixes and all requested bounds. The only evaluated
smoke is empty; no physical or runtime-complexity claim is tested here. -/
set_option genInjectivity false
set_option maxRecDepth 4096
namespace Tests.Relativity.InterleavedProductiveWindowChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Analysis
open SharedProductiveCoverChecks

def precisionRequest (steps : Nat) (precision : Precision) :
    ProductiveWindowRequest first second (third steps) := fun _ => .precision precision

def mixed (steps : Nat) (requests : List (ProductiveWindowRequest first second (third steps))) :=
  (received steps).runWindows requests agreement (secondThirdAgreement steps)

theorem shared_precision_uses_the_actual_first (steps : Nat) (precision : Precision) :
    ((received steps).continueSharedPrecision precision agreement (secondThirdAgreement steps)).first =
      firstCertificate.continuePrecision precision := rfl

theorem shared_precision_uses_the_actual_second (steps : Nat) (precision : Precision) :
    ((received steps).continueSharedPrecision precision agreement (secondThirdAgreement steps)).third =
      ((received steps).continueSharedPrecision precision agreement (secondThirdAgreement steps)).second.certificate.matchFromReceived
        (thirdCertificate steps) (secondThirdAgreement steps) :=
  productive_shared_precision_third_consumes_actual_second ..

theorem head_is_independent_of_the_completed_horizon (steps : Nat)
    (request : ProductiveWindowRequest first second (third steps))
    (one two : List (ProductiveWindowRequest first second (third steps))) :
    (mixed steps (request :: one)).headProduction = (mixed steps (request :: two)).headProduction :=
  productive_window_head_horizon_independent ..

theorem all_mixed_prefixes_extend_the_received_ones (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) :
    ProductiveTripleExtension (received steps) (mixed steps requests).endpoint :=
  (mixed steps requests).extendsReceived

theorem every_requested_precision_survives (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps)))
    (precision : Precision) (present : precision ∈ (mixed steps requests).requestedPrecisions) :
    Rational.Le (mixed steps requests).endpoint.window.span precision.value :=
  (mixed steps requests).allRequestedBounds precision present

theorem fine_cover_coarse_still_meets_the_first_precision (steps : Nat) (fine coarse : Precision) :
    Rational.Le (mixed steps [precisionRequest steps fine, coverWindowRequest (request steps),
      precisionRequest steps coarse]).endpoint.window.span fine.value :=
  (mixed steps [precisionRequest steps fine, coverWindowRequest (request steps),
    precisionRequest steps coarse]).allRequestedBounds fine (.head _)

theorem all_three_later_readings_stay_inside (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) (later : Nat) :
    initialWindow.Contains ((mixed steps requests).endpoint.firstCertificate.advance later).realization.state.reading.value ∧
    initialWindow.Contains ((mixed steps requests).endpoint.secondCertificate.advance later).realization.state.reading.value ∧
    initialWindow.Contains ((mixed steps requests).endpoint.thirdCertificate.advance later).realization.state.reading.value :=
  (mixed steps requests).allLaterReadings later

theorem converted_cover_course_is_the_same_complete_course (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps requests).asWindowCourse = mixed steps (requests.map coverWindowRequest) :=
  productive_cover_only_is_same_whole_course ..

theorem conversion_keeps_all_three_actual_certificates (steps : Nat)
    (requests : List (ProductiveCoverRequest first second (third steps))) :
    (course steps requests).asWindowCourse.endpoint = (course steps requests).endpoint :=
  productive_cover_conversion_returns_whole_endpoint _

theorem conversion_keeps_the_recorded_left_leaf (steps : Nat) :
    (course steps [request steps]).asWindowCourse.headProduction.recordedChoice = some [true] := by
  rw [productive_cover_conversion_keeps_recorded_head, one_closed_cover_selects_left]

theorem conversion_keeps_the_recorded_right_leaf (steps : Nat) :
    (course steps [oppositeRequest steps]).asWindowCourse.headProduction.recordedChoice = some [false] := by
  rw [productive_cover_conversion_keeps_recorded_head, the_other_closed_cover_selects_right]

theorem retaining_is_the_whole_mixed_course (steps : Nat)
    (requests more : List (ProductiveWindowRequest first second (third steps))) :
    (mixed steps requests).resumeRetaining more agreement (secondThirdAgreement steps) =
      mixed steps (requests ++ more) :=
  productive_retained_windows_are_whole_continuous_course ..

theorem retaining_keeps_the_old_complete_head (steps : Nat)
    (request : ProductiveWindowRequest first second (third steps))
    (requests more : List (ProductiveWindowRequest first second (third steps))) :
    ((mixed steps (request :: requests)).resumeRetaining more agreement
      (secondThirdAgreement steps)).headProduction = (mixed steps (request :: requests)).headProduction :=
  productive_window_append_keeps_whole_head ..

theorem covering_then_precision_keeps_every_received_prefix (steps : Nat)
    (covers : List (ProductiveCoverRequest first second (third steps)))
    (requests : List (ProductiveWindowRequest first second (third steps))) :
    ProductiveTripleExtension (received steps)
      ((course steps covers).asWindowCourse.resumeRetaining requests agreement (secondThirdAgreement steps)).endpoint :=
  ((course steps covers).asWindowCourse.resumeRetaining requests agreement (secondThirdAgreement steps)).extendsReceived

theorem all_three_retained_precision_endpoints_feed_mixed_requests (steps : Nat)
    (requests more : List Precision)
    (mixedRequests : List (ProductiveWindowRequest first second (third steps))) :
    ProductiveTripleExtension (retainedEndpoint steps requests more)
      ((retainedEndpoint steps requests more).runWindows mixedRequests agreement (secondThirdAgreement steps)).endpoint :=
  ((retainedEndpoint steps requests more).runWindows mixedRequests agreement (secondThirdAgreement steps)).extendsReceived

theorem all_three_source_distinctions_persist (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) :
    (historyTransport (mixed steps requests).endpoint.firstCertificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (mixed steps requests).endpoint.firstCertificate.realization.chain.history).references
        leftSource.reading.arrivals.second ∧
    (historyTransport (mixed steps requests).endpoint.secondCertificate.realization.chain.history).references
        rightSource.reading.arrivals.first ≠
      (historyTransport (mixed steps requests).endpoint.secondCertificate.realization.chain.history).references
        rightSource.reading.arrivals.second ∧
    (historyTransport (mixed steps requests).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.first ≠
      (historyTransport (mixed steps requests).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.second :=
  ⟨relative_refinement_chain_keeps_sources _, relative_refinement_chain_keeps_sources _,
    relative_refinement_chain_keeps_sources _⟩

theorem third_source_record_stays_readable (steps : Nat)
    (requests : List (ProductiveWindowRequest first second (third steps))) :
    (mixed steps requests).endpoint.thirdCertificate.realization.state.cursor.read
      ((historyTransport (mixed steps requests).endpoint.thirdCertificate.realization.chain.history).references
        leftSource.reading.arrivals.secondSignal) = leftSource.cursor.read leftSource.reading.arrivals.secondSignal :=
  history_preserves_reads _ _

def emptySmoke : Nat := (mixed 1 []).endpoint.thirdCertificate.depth
#eval emptySmoke

end Tests.Relativity.InterleavedProductiveWindowChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.precisionRequest
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.mixed
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.shared_precision_uses_the_actual_first
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.shared_precision_uses_the_actual_second
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.head_is_independent_of_the_completed_horizon
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.all_mixed_prefixes_extend_the_received_ones
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.every_requested_precision_survives
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.fine_cover_coarse_still_meets_the_first_precision
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.all_three_later_readings_stay_inside
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.converted_cover_course_is_the_same_complete_course
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.conversion_keeps_all_three_actual_certificates
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.conversion_keeps_the_recorded_left_leaf
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.conversion_keeps_the_recorded_right_leaf
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.retaining_is_the_whole_mixed_course
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.retaining_keeps_the_old_complete_head
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.covering_then_precision_keeps_every_received_prefix
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.all_three_retained_precision_endpoints_feed_mixed_requests
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.all_three_source_distinctions_persist
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.third_source_record_stays_readable
#print axioms Tests.Relativity.InterleavedProductiveWindowChecks.emptySmoke
/- AXIOM_AUDIT_END -/
