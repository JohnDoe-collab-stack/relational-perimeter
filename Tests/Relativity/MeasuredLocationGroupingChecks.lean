import RelationalPerimeter

/-! Public clients of checked local grouping. The evaluations test execution
only, not physical location, a continuum or a complexity bound. -/
set_option genInjectivity false
set_option maxHeartbeats 1000000
namespace Tests.Relativity.MeasuredLocationGroupingChecks
open RelationalPerimeter.Relativity
open RelationalPerimeter.Relativity.Production
open RelationalPerimeter.Relativity.Production.Encounter
open RelationalPerimeter.Relativity.Reconstruction
open RelationalPerimeter.Relativity.Analysis
open ConstitutiveSearch.Resources

theorem both_readers_factor {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) (request : MeasuredLocationRequest) :
    (groupMeasuredLocations found).signature.read request = one.signature.read request ∧
    (groupMeasuredLocations found).signature.read request = two.signature.read request :=
  grouped_measured_reader_factorization found request

theorem exact_restrictions_return_both {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) :
    (groupMeasuredLocations found).restrict (window_intersection_left one.window two.window) = one.project ∧
    (groupMeasuredLocations found).restrict (window_intersection_right one.window two.window) = two.project :=
  grouped_measured_locations_return_both found

theorem all_actual_continuations_keep_readers {current target} (signature : MeasuredLocationSignature current)
    (history : Encounter.History current target) (request : MeasuredLocationRequest) :
    (signature.prolong history).read request = signature.read request :=
  measured_signature_readers_prolong signature history request

theorem prolonging_does_not_merge_different_signatures {current target}
    (one two : MeasuredLocationSignature current) (history : Encounter.History current target)
    (same : one.prolong history = two.prolong history) : one = two :=
  measured_signature_prolong_returns one two history same

def oldAfterRemeasure {source} (result : Measurement source)
    {window} (reading : MeasuredPathConstraint result .root window)
    (next : Measurement result.next) : MeasuredLocationSource next.head.next :=
  ⟨source, result, next.history, .left, window, reading.atHistory next.history⟩

def newAfterRemeasure {source} (result : Measurement source) (next : Measurement result.next) :
    MeasuredLocationSource next.head.next :=
  ⟨result.next, next, .root, .right, ReadingWindow.atPrecision (measuredPathValue next .root) Precision.unit,
    ⟨measuredPathValue next .root, rfl, precision_window_contains _ _⟩⟩

theorem repeated_measurement_has_same_relative_value {source} (result : Measurement source)
    {window} (reading : MeasuredPathConstraint result .root window) (next : Measurement result.next) :
    (oldAfterRemeasure result reading next).signature.read .relative =
      (newAfterRemeasure result next).signature.read .relative := by
  change measuredPathValue result next.history = measuredPathValue next .root
  have old : measuredPathValue result next.history = measuredRelativeValue result :=
    measured_path_value_persists result next.history
  have fresh : measuredPathValue next .root = measuredRelativeValue next :=
    measured_path_value_persists next .root
  have ratios : measuredRelativeValue result = measuredRelativeValue next :=
    (measured_ratio_reads_consumed_effect result).trans
      ((measurement_keeps_ratio next).symm.trans (measured_ratio_reads_consumed_effect next).symm)
  exact old.trans (ratios.trans fresh.symm)

theorem repeated_measurement_still_refuses_grouping {source} (result : Measurement source)
    {window} (reading : MeasuredPathConstraint result .root window) (next : Measurement result.next)
    (found : MeasuredLocationRaccord (oldAfterRemeasure result reading next) (newAfterRemeasure result next)) : False := by
  apply different_anchor_refuses_measured_grouping _ _ ?_ found
  intro same
  have carried := localized_prolong_location (localizeParticipant result.head .left) next.history
  exact measurement_anchor_is_fresh next (commonEncounterLocation result.head) (same.symm.trans carried)

theorem every_finite_precision_is_kept {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest)
    (request : MeasuredPrecisionRequest) (included : request ∈ requests) :
    Rational.Le (groupedMeasuredDescription (description.runMore requests)).window.span request.precision.value :=
  grouped_measured_description_every_precision description requests request included

def received : Received := ⟨Rational.zero, 7, Calibration.unit⟩
def paths := realizeRelativeReading (.received received) .here (.prior .here) (.prior (.prior .here)) rfl 1 1
def initial := RelativeState.attach (RelativePathState.fromExecution paths (.prior (.prior .here)) rfl)
def measured := measure initial
def reading : MeasuredPathConstraint measured .root
    (ReadingWindow.atPrecision (measuredPathValue measured .root) Precision.unit) :=
  ⟨measuredPathValue measured .root, rfl, precision_window_contains _ _⟩
def started := MeasuredDescriptionRun.start reading

private def report {source} {result : Measurement source} {window}
    (reading : MeasuredPathConstraint result .root window) : Bool × Bool × Bool :=
  let start := MeasuredDescriptionRun.start reading
  let first := measuredDescriptionPort start .left
  let second := measuredDescriptionPort start .right
  let grouped := match checkAndGroupMeasuredLocations first second with | .inl _ => true | .inr _ => false
  let next := measure result.next
  let old := oldAfterRemeasure result reading next
  let fresh := newAfterRemeasure result next
  let sameNumber := decide (old.signature.read .relative = fresh.signature.read .relative)
  let refused := match checkAndGroupMeasuredLocations old fresh with | .inl _ => false | .inr _ => true
  (grouped, sameNumber, refused)

def smokeReport := report reading

#eval smokeReport

end Tests.Relativity.MeasuredLocationGroupingChecks
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.both_readers_factor
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.exact_restrictions_return_both
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.all_actual_continuations_keep_readers
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.prolonging_does_not_merge_different_signatures
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.repeated_measurement_has_same_relative_value
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.repeated_measurement_still_refuses_grouping
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.every_finite_precision_is_kept
#print axioms Tests.Relativity.MeasuredLocationGroupingChecks.smokeReport
/- AXIOM_AUDIT_END -/
