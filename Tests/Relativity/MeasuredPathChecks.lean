import RelationalPerimeter

/-! Public consumers of the measured-path/encounter bridge. Concrete
evaluations are executability smoke checks, not physical experiments. -/
set_option genInjectivity false
set_option maxHeartbeats 1000000
namespace Tests.Relativity.MeasuredPathChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def input : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def paths := realizeRelativeReading (.received input) .here (.prior .here) (.prior (.prior .here)) rfl 1 1
def initial := RelativeState.attach
  (RelativePathState.fromExecution paths (.prior (.prior .here)) rfl)
def measured := measure initial
def upper := refine measured.next .upper

theorem first_ratio : measured.next.reading.value = Rational.ofParts 1 0 1 :=
  (measurement_keeps_ratio measured).trans (by rfl)

theorem first_raw_response : measured.head.head.determination.1 = Rational.one :=
  (measurement_raw_output measured).trans (by rfl)

theorem two_different_records : initial.coupling.cursor.read initial.reading.firstSignal ≠
    initial.coupling.cursor.read initial.reading.secondSignal := by
  intro same
  have impossible := congrArg (fun record : SignalRecord => record.increments.length) same
  change 1 = 2 at impossible
  exact Nat.noConfusion impossible (fun smaller => Nat.noConfusion smaller)

theorem distinct_arrivals : measured.reading.arrivals.first ≠ measured.reading.arrivals.second :=
  measured.reading.arrivals.distinct

def agreement_is_from_the_measured_encounter :
    LocationAgreement measured.head (measuredFirst measured .root) (measuredSecond measured .root) :=
  measuredEncounterAgreement measured .root

theorem ratio_is_from_the_consumed_record : measuredRelativeValue measured = Rational.ofParts 1 0 1 :=
  (measured_ratio_reads_consumed_effect measured).trans first_ratio

theorem arbitrary_finite_futures_keep_the_path_difference
    (requests : List RelationalPerimeter.Relativity.Continuation.Encounter.Request) :
    ¬ FutureEquivalent (RelationalPerimeter.Relativity.Continuation.Encounter.readerContract measured.head)
      ⟨(RelationalPerimeter.Relativity.Continuation.Encounter.run measured.head.next requests).state,
        measuredFirst measured (RelationalPerimeter.Relativity.Continuation.Encounter.run
          measured.head.next requests).history⟩
      ⟨(RelationalPerimeter.Relativity.Continuation.Encounter.run measured.head.next requests).state,
        measuredSecond measured (RelationalPerimeter.Relativity.Continuation.Encounter.run
          measured.head.next requests).history⟩ :=
  RelationalPerimeter.Relativity.Continuation.Encounter.measured_requests_preserve_path_distinctions
    measured requests two_different_records

theorem upper_uses_both_actual_path_counts :
    upper.next.reading.numerator.relayCount = 3 ∧ upper.next.reading.denominator.relayCount = 4 :=
  refinement_counts upper

theorem upper_is_three_quarters : upper.next.reading.value = Rational.ofParts 3 0 3 :=
  (upper.next.reading.count_ratio_exact).trans
    ((congrArg (fun n => Rational.mul (Rational.ofNat n)
      (Rational.inverseNatSucc (upper.next.reading.denominator.relayCount - 1)))
        upper_uses_both_actual_path_counts.1).trans
      ((congrArg (fun d => Rational.mul (Rational.ofNat 3) (Rational.inverseNatSucc (d - 1)))
        upper_uses_both_actual_path_counts.2).trans (by rfl)))

theorem second_request_restarts_from_the_returned_encounter (source : RelativeState)
    (requests : List RelativeSubdivision) :
    (measureThen source requests).2 = runMeasurements (measure source).next requests :=
  measurement_suffix_from_produced_successor source requests

theorem packet_composition (source : RelativeState) (first second : List RelativeSubdivision) :
    ((runMeasurements source first).runMore second) = runMeasurements source (first ++ second) :=
  measurement_runs_append _ first second

theorem whole_course_keeps_emitted_origin {source target : RelativeState}
    (chain : MeasurementChain source target) :
    target.reading.numerator.origin = chain.history.transport.references source.reading.numerator.origin :=
  measurement_chain_origin chain

theorem whole_course_keeps_old_effects {source target : RelativeState}
    (result : Measurement source) (chain : MeasurementChain result.next target) :
    AttachedEffects (measuredFirst result chain.history) =
      source.coupling.cursor.read source.reading.firstSignal ∧
    AttachedEffects (measuredSecond result chain.history) =
      source.coupling.cursor.read source.reading.secondSignal :=
  measured_encounter_keeps_effects result chain.history

theorem head_has_no_future_parameter (one two : List RelativeSubdivision) :
    (measureThen initial one).1 = (measureThen initial two).1 := measurement_head_independent initial one two

theorem exactly_three_new_local_productions : StrongPerimetralTurning.History.length measured.history = 3 :=
  measurement_length initial

theorem each_refinement_adds_only_its_relays_and_three_heads (source : RelativeState) (choice : RelativeSubdivision) :
    StrongPerimetralTurning.History.length (refine source choice).history =
      source.reading.numerator.relayCount + choice.extra + source.reading.denominator.relayCount + 3 :=
  refinement_length source choice

theorem no_reuse_of_consumed_availability : encounterEnabled measured.head.next = false := rfl

private def report (result : RelativeState) : Nat × Nat × Nat :=
  (result.reading.numerator.relayCount, result.reading.denominator.relayCount, result.reading.value.index)

def smokeReport : Nat × Nat × Nat :=
  let head := measure initial
  let result := runMeasurements head.next [.upper, .lower]
  report result.state

#eval smokeReport

end Tests.Relativity.MeasuredPathChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.MeasuredPathChecks.first_ratio
#print axioms Tests.Relativity.MeasuredPathChecks.first_raw_response
#print axioms Tests.Relativity.MeasuredPathChecks.two_different_records
#print axioms Tests.Relativity.MeasuredPathChecks.distinct_arrivals
#print axioms Tests.Relativity.MeasuredPathChecks.agreement_is_from_the_measured_encounter
#print axioms Tests.Relativity.MeasuredPathChecks.ratio_is_from_the_consumed_record
#print axioms Tests.Relativity.MeasuredPathChecks.arbitrary_finite_futures_keep_the_path_difference
#print axioms Tests.Relativity.MeasuredPathChecks.upper_uses_both_actual_path_counts
#print axioms Tests.Relativity.MeasuredPathChecks.upper_is_three_quarters
#print axioms Tests.Relativity.MeasuredPathChecks.second_request_restarts_from_the_returned_encounter
#print axioms Tests.Relativity.MeasuredPathChecks.packet_composition
#print axioms Tests.Relativity.MeasuredPathChecks.whole_course_keeps_emitted_origin
#print axioms Tests.Relativity.MeasuredPathChecks.whole_course_keeps_old_effects
#print axioms Tests.Relativity.MeasuredPathChecks.head_has_no_future_parameter
#print axioms Tests.Relativity.MeasuredPathChecks.exactly_three_new_local_productions
#print axioms Tests.Relativity.MeasuredPathChecks.each_refinement_adds_only_its_relays_and_three_heads
#print axioms Tests.Relativity.MeasuredPathChecks.no_reuse_of_consumed_availability
#print axioms Tests.Relativity.MeasuredPathChecks.smokeReport
/- AXIOM_AUDIT_END -/
