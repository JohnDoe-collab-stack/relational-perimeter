import RelationalPerimeter

/-! Public clients of P3's measured constraints. Evaluations are only
executability smoke checks, not physical experiments or cost measurements. -/
set_option genInjectivity false
set_option maxHeartbeats 1000000
namespace Tests.Relativity.MeasuredConstraintChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

def received : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def paths := realizeRelativeReading (.received received) .here (.prior .here) (.prior (.prior .here)) rfl 1 1
def initial := RelativeState.attach
  (RelativePathState.fromExecution paths (.prior (.prior .here)) rfl)
def measured := measure initial
def reading : MeasuredPathConstraint measured .root
    (ReadingWindow.atPrecision (measuredPathValue measured .root) Precision.unit) :=
  ⟨measuredPathValue measured .root, rfl, precision_window_contains _ _⟩
def started := MeasuredDescriptionRun.start reading
def request : MeasuredPrecisionRequest := ⟨.upper, Precision.unit.half⟩

theorem old_determination_remains_one_half :
    (started.advance request).reading.value = Rational.ofParts 1 0 1 :=
  (measured_description_run_keeps_old_determination started [request]).trans
    ((measured_ratio_reads_consumed_effect measured).trans
      ((measurement_keeps_ratio measured).trans (by rfl)))

theorem new_ratio_requires_its_produced_correction {source result coarse choice}
    (prior : @MeasuredDescriptionRun source result coarse)
    (head : Refinement prior.realization.state choice) :
    correctedRefinementValue prior head = measuredPathValue result prior.realization.chain.history :=
  corrected_refinement_reads_old_determination prior head _

theorem successive_encounters_are_not_identified {source choice}
    (head : Refinement source choice) (old : Ref source.coupling.cursor.kinds .reading) :
    comparisonAnchor head.measurement.head.head ≠ head.history.transport.references old :=
  refined_encounter_is_not_an_old_occurrence head old

theorem all_finite_precision_requests_return_the_old_constraint {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest) :
    (prior.runMore requests).reading.restrict (measured_description_run_refines prior requests) =
      prior.reading.atHistory (prior.runMore requests).realization.chain.history :=
  measured_description_run_returns_exactly prior requests

theorem every_requested_precision_is_met {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest)
    (chosen : MeasuredPrecisionRequest) (included : chosen ∈ requests) :
    Rational.Le (prior.runMore requests).window.span chosen.precision.value :=
  measured_description_bounds_every_request prior requests chosen included

theorem common_description_returns_both_received_constraints {source result coarse}
    (first second : @MeasuredDescriptionRun source result coarse) :
    (commonMeasuredDescriptions first second).reading.restrict
        (window_intersection_left first.window second.window) = first.reading ∧
      (commonMeasuredDescriptions first second).reading.restrict
        (window_intersection_right first.window second.window) =
          second.reading.atHistory first.realization.chain.history :=
  common_measured_descriptions_return_both first second

theorem repeated_description_resumes_the_whole_packet {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (one two : List MeasuredPrecisionRequest) :
    (prior.runMore one).runMore two = prior.runMore (one ++ two) :=
  measured_description_runs_append prior one two

theorem description_uses_the_actual_measurement_successor {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (next : MeasuredPrecisionRequest) :
    (prior.advance next).realization.state = (refine prior.realization.state next.subdivision).next :=
  measured_description_step_uses_produced_successor prior next

def common_description_keeps_the_old_local_agreement {source result coarse}
    (first second : @MeasuredDescriptionRun source result coarse) :=
  measuredConstraintLocationAgreement (commonMeasuredDescriptions first second)

theorem precisions_do_not_authorize_erasing_the_path_difference {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse)
    (requests : List RelationalPerimeter.Relativity.Continuation.Encounter.Request)
    (different : source.coupling.cursor.read source.reading.firstSignal ≠
      source.coupling.cursor.read source.reading.secondSignal) :
    let suffix := RelationalPerimeter.Relativity.Continuation.Encounter.run
      description.realization.state.coupling requests
    let history := StrongPerimetralTurning.History.append description.realization.chain.history suffix.history
    ¬ FutureEquivalent (RelationalPerimeter.Relativity.Continuation.Encounter.readerContract result.head)
      ⟨suffix.state, measuredFirst result history⟩ ⟨suffix.state, measuredSecond result history⟩ :=
  RelationalPerimeter.Relativity.Continuation.Encounter.measured_description_futures_keep_distinctions
    description requests different

private def report {source result coarse} (description : @MeasuredDescriptionRun source result coarse) :
    Nat × Nat × Bool × Nat :=
  (description.realization.state.reading.numerator.relayCount,
    description.realization.state.reading.denominator.relayCount,
    decide (description.reading.value = Rational.ofParts 1 0 1),
    description.realization.chain.requests.length)

def smokeReport :=
  let first := started.advance request
  let final := first.runMore [⟨.lower, Precision.unit.half.half⟩]
  report final

#eval smokeReport

end Tests.Relativity.MeasuredConstraintChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.MeasuredConstraintChecks.old_determination_remains_one_half
#print axioms Tests.Relativity.MeasuredConstraintChecks.new_ratio_requires_its_produced_correction
#print axioms Tests.Relativity.MeasuredConstraintChecks.successive_encounters_are_not_identified
#print axioms Tests.Relativity.MeasuredConstraintChecks.all_finite_precision_requests_return_the_old_constraint
#print axioms Tests.Relativity.MeasuredConstraintChecks.every_requested_precision_is_met
#print axioms Tests.Relativity.MeasuredConstraintChecks.common_description_returns_both_received_constraints
#print axioms Tests.Relativity.MeasuredConstraintChecks.repeated_description_resumes_the_whole_packet
#print axioms Tests.Relativity.MeasuredConstraintChecks.description_uses_the_actual_measurement_successor
#print axioms Tests.Relativity.MeasuredConstraintChecks.common_description_keeps_the_old_local_agreement
#print axioms Tests.Relativity.MeasuredConstraintChecks.precisions_do_not_authorize_erasing_the_path_difference
#print axioms Tests.Relativity.MeasuredConstraintChecks.smokeReport
/- AXIOM_AUDIT_END -/
