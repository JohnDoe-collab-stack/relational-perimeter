import RelationalPerimeter.Relativity.Production.EncounterMeasurementLaws
import RelationalPerimeter.Relativity.Production.PreciseReadingRefinements
import RelationalPerimeter.Relativity.Reconstruction.MeasuredEncounterDescriptions

/-!
# Constraints on a measured determination, not on a future encounter

The old encounter, its attachment, calibrated origin and reference scale are
fixed by the received measurement. Later actual measurements have their own
occurrences and ratios. Their produced affine change reexpresses the old
determination; it never identifies the old and new events. A precision request
produces one refinement, consumes its recorded effect, then refines the old
description and returns the whole live successor. Common constraints require
the same constituted measurement, not merely coincident numbers. They do not
join distinct future histories or create physical neighborhoods.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Reconstruction
open Production Production.Encounter Analysis

def measuredPathValue {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) : Rational :=
  Rational.mul (Rational.sub (AttachedEffects (measuredFirst result history)).reading
    (target.cursor.read (history.transport.references
      (result.history.transport.references source.reading.numerator.origin))).reading)
    (Rational.inverseNatSucc (result.reading.denominator.relayCount - 1))

theorem measured_path_value_persists {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) :
    measuredPathValue result history = measuredRelativeValue result := by
  have origin := history_keeps_reads history
    (result.history.transport.references source.reading.numerator.origin)
  have origins := origin.trans (history_keeps_reads result.history source.reading.numerator.origin)
  have effects : AttachedEffects (measuredFirst result history) = result.head.effects.1 :=
    (measured_encounter_keeps_effects result history).1.trans (measurement_first_effect result).symm
  exact (congrArg (fun effect : SignalRecord =>
    Rational.mul (Rational.sub effect.reading (target.cursor.read
      (history.transport.references (result.history.transport.references source.reading.numerator.origin))).reading)
      (Rational.inverseNatSucc (result.reading.denominator.relayCount - 1)))
    effects).trans
    (congrArg (fun start : SignalRecord =>
      Rational.mul (Rational.sub result.head.effects.1.reading start.reading)
        (Rational.inverseNatSucc (result.reading.denominator.relayCount - 1))) origins)

structure MeasuredPathConstraint {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) (window : ReadingWindow) where
  value : Rational
  exactValue : value = measuredPathValue result history
  inside : window.Contains value

theorem measured_constraint_ext {source result target history window}
    (first second : @MeasuredPathConstraint source result target history window)
    (same : first.value = second.value) : first = second := by
  cases first; cases second; cases same; rfl

def certifyMeasuredPath {source} (result : Measurement source) {target}
    (history : Encounter.History result.head.next target) (window : ReadingWindow) :
    PSum (MeasuredPathConstraint result history window)
      (¬ window.Contains (measuredPathValue result history)) :=
  let value := measuredPathValue result history
  if inside : window.Contains value then .inl ⟨value, rfl, inside⟩ else .inr inside

def MeasuredPathConstraint.restrict {source result target history coarse fine}
    (reading : @MeasuredPathConstraint source result target history fine)
    (refinement : WindowRefinement coarse fine) : MeasuredPathConstraint result history coarse :=
  ⟨reading.value, reading.exactValue, refinement.contains reading.inside⟩

theorem measured_restriction_composes {source result target history one two three}
    (reading : @MeasuredPathConstraint source result target history three)
    (first : WindowRefinement one two) (second : WindowRefinement two three) :
    (reading.restrict second).restrict first = reading.restrict (first.compose second) := rfl

/-- Both histories positively transport the same old measurement. This does
not assert that their newly produced events or live states agree. -/
def MeasuredPathConstraint.atHistory {source result current target history window}
    (reading : @MeasuredPathConstraint source result current history window)
    (next : Encounter.History result.head.next target) : MeasuredPathConstraint result next window :=
  ⟨reading.value, reading.exactValue.trans
    ((measured_path_value_persists result history).trans (measured_path_value_persists result next).symm),
    reading.inside⟩

theorem measured_history_restriction_square {source result current target history coarse fine}
    (reading : @MeasuredPathConstraint source result current history fine)
    (next : Encounter.History result.head.next target) (refinement : WindowRefinement coarse fine) :
    (reading.restrict refinement).atHistory next = (reading.atHistory next).restrict refinement := rfl

def MeasuredPathConstraint.common {source result target history one two}
    (first : @MeasuredPathConstraint source result target history one)
    (second : MeasuredPathConstraint result history two) :
    MeasuredPathConstraint result history (one.intersection two) :=
  ⟨first.value, first.exactValue, window_intersection_contains first.inside
    ((second.exactValue.trans first.exactValue.symm) ▸ second.inside)⟩

theorem measured_common_returns_both {source result target history one two}
    (first : @MeasuredPathConstraint source result target history one)
    (second : MeasuredPathConstraint result history two) :
    (first.common second).restrict (window_intersection_left one two) = first ∧
      (first.common second).restrict (window_intersection_right one two) = second := by
  constructor
  · cases first; rfl
  · cases first with | mk first exactFirst insideFirst =>
      cases second with | mk second exactSecond insideSecond =>
        cases exactSecond.trans exactFirst.symm; rfl

structure MeasuredDescriptionRun {source} (result : Measurement source) (coarse : ReadingWindow) where
  realization : MeasurementRun result.next
  window : ReadingWindow
  refinement : WindowRefinement coarse window
  reading : MeasuredPathConstraint result realization.chain.history window

def MeasuredDescriptionRun.start {source result window}
    (reading : @MeasuredPathConstraint source result result.head.next .root window) :
    MeasuredDescriptionRun result window :=
  ⟨⟨result.next, .root result.next⟩, window, .identity window, reading⟩

structure MeasuredPrecisionRequest where
  subdivision : RelativeSubdivision
  precision : Precision

def correctedRefinementValue {source result coarse choice}
    (prior : @MeasuredDescriptionRun source result coarse)
    (head : Refinement prior.realization.state choice) : Rational :=
  Rational.sub (measuredRelativeValue head.measurement)
    (Rational.add prior.realization.chain.drift head.drift)

theorem corrected_refinement_reads_old_determination {source result coarse choice}
    (prior : @MeasuredDescriptionRun source result coarse)
    (head : Refinement prior.realization.state choice) {target}
    (history : Encounter.History result.head.next target) :
    correctedRefinementValue prior head = measuredPathValue result history := by
  unfold correctedRefinementValue
  rw [measured_ratio_reads_consumed_effect]
  change Rational.sub head.next.reading.value _ = _
  rw [refinement_affine_reading, measurement_chain_affine_reading]
  rw [Rational.add_assoc]
  unfold Rational.sub
  rw [Rational.add_assoc, Rational.add_neg, Rational.add_zero,
    ← measured_ratio_reads_consumed_effect, measured_path_value_persists]

/-- This consumer receives the already executed head, not a numerical target. -/
def describeMeasuredRefinement {source result coarse choice}
    (prior : @MeasuredDescriptionRun source result coarse)
    (head : Refinement prior.realization.state choice)
    (headExact : head = refine prior.realization.state choice) (precision : Precision) :
    MeasuredDescriptionRun result coarse :=
  let produced : MeasurementRun result.next :=
    ⟨head.next, .step prior.realization.chain choice head headExact⟩
  let value := correctedRefinementValue prior head
  let centered : MeasuredPathConstraint result produced.chain.history
      (ReadingWindow.atPrecision value precision) :=
    ⟨value, corrected_refinement_reads_old_determination prior head _, precision_window_contains value precision⟩
  let old := prior.reading.atHistory produced.chain.history
  let fine := centered.common old
  ⟨produced, (ReadingWindow.atPrecision value precision).intersection prior.window,
    prior.refinement.compose (window_intersection_right _ _), fine⟩

theorem measured_step_restricts_exactly {source result coarse choice}
    (prior : @MeasuredDescriptionRun source result coarse)
    (head : Refinement prior.realization.state choice)
    (headExact : head = refine prior.realization.state choice) (precision : Precision) :
    (describeMeasuredRefinement prior head headExact precision).reading.restrict
      (window_intersection_right _ prior.window) =
      prior.reading.atHistory (describeMeasuredRefinement prior head headExact precision).realization.chain.history :=
  (measured_common_returns_both _ _).2

theorem measured_step_precision_bound {source result coarse choice}
    (prior : @MeasuredDescriptionRun source result coarse)
    (head : Refinement prior.realization.state choice)
    (headExact : head = refine prior.realization.state choice) (precision : Precision) :
    Rational.Le (describeMeasuredRefinement prior head headExact precision).window.span precision.value := by
  exact Rational.le_trans (window_intersection_left _ _).span_le (by
    rw [precision_window_span]
    exact Rational.le_refl _)

def MeasuredDescriptionRun.advance {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (request : MeasuredPrecisionRequest) :
    MeasuredDescriptionRun result coarse :=
  let head := refine prior.realization.state request.subdivision
  describeMeasuredRefinement prior head rfl request.precision

def MeasuredDescriptionRun.runMore {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) :
    List MeasuredPrecisionRequest → MeasuredDescriptionRun result coarse
  | [] => prior
  | request :: tail =>
    let head := prior.advance request
    head.runMore tail

theorem measured_description_runs_append {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (first second : List MeasuredPrecisionRequest) :
    (prior.runMore first).runMore second = prior.runMore (first ++ second) := by
  induction first generalizing prior with
  | nil => rfl
  | cons request tail ih => exact ih (prior.advance request)

theorem measured_description_step_uses_produced_successor {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (request : MeasuredPrecisionRequest) :
    (prior.advance request).realization.state =
      (refine prior.realization.state request.subdivision).next := rfl

theorem measured_description_run_keeps_old_determination {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest) :
    (prior.runMore requests).reading.value = measuredRelativeValue result :=
  (prior.runMore requests).reading.exactValue.trans (measured_path_value_persists result _)

theorem measured_description_run_refines {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest) :
    WindowRefinement prior.window (prior.runMore requests).window := by
  induction requests generalizing prior with
  | nil => exact .identity _
  | cons request tail ih =>
    exact (window_intersection_right _ _).compose (ih (prior.advance request))

theorem measured_description_run_returns_exactly {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest) :
    (prior.runMore requests).reading.restrict (measured_description_run_refines prior requests) =
      prior.reading.atHistory (prior.runMore requests).realization.chain.history := by
  apply measured_constraint_ext
  exact (measured_description_run_keeps_old_determination prior requests).trans
    (prior.reading.exactValue.trans (measured_path_value_persists result _)).symm

theorem measured_description_bounds_every_request {source result coarse}
    (prior : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest)
    (request : MeasuredPrecisionRequest) (requested : request ∈ requests) :
    Rational.Le (prior.runMore requests).window.span request.precision.value := by
  induction requests generalizing prior with
  | nil => cases requested
  | cons first tail ih =>
    cases requested with
    | head =>
      exact Rational.le_trans (measured_description_run_refines (prior.advance request) tail).span_le
        (measured_step_precision_bound prior _ rfl request.precision)
    | tail _ later => exact ih (prior.advance first) later

/-- Compatibility is the common constituted measurement in the indices, not
the existence of an intersection or equality of two unrelated readouts. -/
def commonMeasuredDescriptions {source result coarse}
    (first second : @MeasuredDescriptionRun source result coarse) :
    MeasuredDescriptionRun result coarse :=
  let other := second.reading.atHistory first.realization.chain.history
  ⟨first.realization, first.window.intersection second.window,
    first.refinement.compose (window_intersection_left _ _), first.reading.common other⟩

theorem common_measured_descriptions_return_both {source result coarse}
    (first second : @MeasuredDescriptionRun source result coarse) :
    (commonMeasuredDescriptions first second).reading.restrict
        (window_intersection_left first.window second.window) = first.reading ∧
      (commonMeasuredDescriptions first second).reading.restrict
        (window_intersection_right first.window second.window) =
          second.reading.atHistory first.realization.chain.history :=
  measured_common_returns_both _ _

theorem common_measured_descriptions_keep_bounds {source result coarse}
    (first second : @MeasuredDescriptionRun source result coarse) (one two : Precision)
    (firstBound : Rational.Le first.window.span one.value)
    (secondBound : Rational.Le second.window.span two.value) :
    Rational.Le (commonMeasuredDescriptions first second).window.span one.value ∧
      Rational.Le (commonMeasuredDescriptions first second).window.span two.value :=
  ⟨Rational.le_trans (window_intersection_left _ _).span_le firstBound,
    Rational.le_trans (window_intersection_right _ _).span_le secondBound⟩

def measuredConstraintLocationAgreement {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) :
    LocationAgreement result.head (measuredFirst result description.realization.chain.history)
      (measuredSecond result description.realization.chain.history) :=
  measuredEncounterAgreement result description.realization.chain.history

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_path_value_persists
#print axioms RelationalPerimeter.Relativity.Reconstruction.certifyMeasuredPath
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_constraint_ext
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_restriction_composes
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredPathConstraint.atHistory
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_history_restriction_square
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_common_returns_both
#print axioms RelationalPerimeter.Relativity.Reconstruction.corrected_refinement_reads_old_determination
#print axioms RelationalPerimeter.Relativity.Reconstruction.describeMeasuredRefinement
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_step_restricts_exactly
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_step_precision_bound
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredDescriptionRun.advance
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredDescriptionRun.runMore
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_runs_append
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_step_uses_produced_successor
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_run_keeps_old_determination
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_run_refines
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_run_returns_exactly
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_bounds_every_request
#print axioms RelationalPerimeter.Relativity.Reconstruction.commonMeasuredDescriptions
#print axioms RelationalPerimeter.Relativity.Reconstruction.common_measured_descriptions_return_both
#print axioms RelationalPerimeter.Relativity.Reconstruction.common_measured_descriptions_keep_bounds
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredConstraintLocationAgreement
/- AXIOM_AUDIT_END -/
