import RelationalPerimeter.Relativity.Reconstruction.MeasuredPathConstraints

/-!
# Checked grouping of local measured descriptions

The readers are fixed before the check: the old interaction reading and its
joint relative reading. The check compares constituted references and the
received positive scale, not equality of numbers or overlap of windows.
An accepted raccord is consumed to form the common constrained description.
Its restrictions return the two projected descriptions exactly. Participant
records and the live state are not quotiented; this is not a memory reduction.
The location reference denotes an admitted encounter, not an ideal spacetime
point. No physical localization law between distinct encounters is supplied.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Reconstruction
open Production Production.Encounter
open ConstitutiveSearch.Resources

structure MeasuredLocationSignature (current : State) where
  anchor : Ref current.cursor.kinds .reading
  numerator : Ref current.cursor.kinds .signal
  origin : Ref current.cursor.kinds .signal
  scale : Nat
  positive : 0 < scale

def MeasuredLocationSignature.code {current} (signature : MeasuredLocationSignature current) :
    Nat × Nat × Nat × Nat :=
  (signature.anchor.position, signature.numerator.position, signature.origin.position, signature.scale)

theorem measured_signature_code_injective {current}
    (one two : MeasuredLocationSignature current) (same : one.code = two.code) : one = two := by
  have anchor := reference_position_injective one.anchor two.anchor (congrArg (fun code => code.1) same)
  have numerator := reference_position_injective one.numerator two.numerator (congrArg (fun code => code.2.1) same)
  have origin := reference_position_injective one.origin two.origin (congrArg (fun code => code.2.2.1) same)
  have scale := congrArg (fun code => code.2.2.2) same
  cases one; cases two
  cases anchor; cases numerator; cases origin; cases scale
  rfl

inductive MeasuredLocationRequest where
  | interaction
  | relative

def MeasuredLocationSignature.read {current} (signature : MeasuredLocationSignature current) :
    MeasuredLocationRequest → Rational
  | .interaction => current.cursor.read signature.anchor
  | .relative => Rational.mul
      (Rational.sub (current.cursor.read signature.numerator).reading
        (current.cursor.read signature.origin).reading)
      (Rational.inverseNatSucc (signature.scale - 1))

def MeasuredLocationSignature.prolong {current target} (signature : MeasuredLocationSignature current)
    (history : Encounter.History current target) : MeasuredLocationSignature target :=
  ⟨history.transport.references signature.anchor, history.transport.references signature.numerator,
    history.transport.references signature.origin, signature.scale, signature.positive⟩

theorem measured_signature_readers_prolong {current target} (signature : MeasuredLocationSignature current)
    (history : Encounter.History current target) (request : MeasuredLocationRequest) :
    (signature.prolong history).read request = signature.read request := by
  cases request with
  | interaction => exact history_keeps_reads history _
  | relative =>
    change Rational.mul (Rational.sub
      (target.cursor.read (history.transport.references signature.numerator)).reading
      (target.cursor.read (history.transport.references signature.origin)).reading)
      (Rational.inverseNatSucc (signature.scale - 1)) = _
    rw [history_keeps_reads history signature.numerator, history_keeps_reads history signature.origin]
    rfl

theorem measured_signature_prolong_returns {current target}
    (one two : MeasuredLocationSignature current) (history : Encounter.History current target)
    (same : one.prolong history = two.prolong history) : one = two := by
  have anchor := history.transport.injective one.anchor two.anchor
    (congrArg (fun signature : MeasuredLocationSignature target => signature.anchor) same)
  have numerator := history.transport.injective one.numerator two.numerator
    (congrArg (fun signature : MeasuredLocationSignature target => signature.numerator) same)
  have origin := history.transport.injective one.origin two.origin
    (congrArg (fun signature : MeasuredLocationSignature target => signature.origin) same)
  have scale : one.scale = two.scale := congrArg (fun signature : MeasuredLocationSignature target => signature.scale) same
  cases one; cases two
  cases anchor; cases numerator; cases origin; cases scale
  rfl

/-- A received description contains its positive rooted history and the exact
P3 certificate. The participant still selects its own rich attached record. -/
structure MeasuredLocationSource (current : State) where
  source : RelativeState
  result : Measurement source
  history : Encounter.History result.head.next current
  participant : Port
  window : ReadingWindow
  reading : MeasuredPathConstraint result history window

def MeasuredLocationSource.presentation {current} (description : MeasuredLocationSource current) :=
  (localizeParticipant description.result.head description.participant).prolong description.history

def MeasuredLocationSource.signature {current} (description : MeasuredLocationSource current) :
    MeasuredLocationSignature current :=
  ⟨(measuredFirst description.result description.history).location,
    (measuredFirst description.result description.history).attachment.signalReference,
    description.history.transport.references
      (description.result.history.transport.references description.source.reading.numerator.origin),
    description.result.reading.denominator.relayCount, description.result.reading.positiveScale⟩

theorem measured_signature_reads_constraint {current} (description : MeasuredLocationSource current) :
    description.signature.read .relative = description.reading.value := description.reading.exactValue.symm

structure ConstrainedMeasuredLocation (current : State) (window : ReadingWindow) where
  signature : MeasuredLocationSignature current
  value : Rational
  exactValue : value = signature.read .relative
  inside : window.Contains value

def ConstrainedMeasuredLocation.window {current window}
    (_description : ConstrainedMeasuredLocation current window) : ReadingWindow := window

def MeasuredLocationSource.project {current} (description : MeasuredLocationSource current) :
    ConstrainedMeasuredLocation current description.window :=
  ⟨description.signature, description.reading.value, description.reading.exactValue, description.reading.inside⟩

def ConstrainedMeasuredLocation.restrict {current coarse fine}
    (description : ConstrainedMeasuredLocation current fine) (refinement : WindowRefinement coarse fine) :
    ConstrainedMeasuredLocation current coarse :=
  ⟨description.signature, description.value, description.exactValue, refinement.contains description.inside⟩

def ConstrainedMeasuredLocation.prolong {current target window}
    (description : ConstrainedMeasuredLocation current window) (history : Encounter.History current target) :
    ConstrainedMeasuredLocation target window :=
  ⟨description.signature.prolong history, description.value,
    description.exactValue.trans (measured_signature_readers_prolong description.signature history .relative).symm,
    description.inside⟩

theorem measured_grouping_restriction_continuation_square {current target coarse fine}
    (description : ConstrainedMeasuredLocation current fine) (history : Encounter.History current target)
    (refinement : WindowRefinement coarse fine) :
    (description.restrict refinement).prolong history = (description.prolong history).restrict refinement := rfl

theorem constrained_measured_location_ext {current window}
    (one two : ConstrainedMeasuredLocation current window)
    (same : one.signature = two.signature) : one = two := by
  cases one with | mk one oneValue oneExact oneInside =>
    cases two with | mk two twoValue twoExact twoInside =>
      cases same
      cases twoExact.trans oneExact.symm
      rfl

/-- Its law is exact reference correspondence on one received support. The
positive measured sources are the indices; no free physical point is given. -/
inductive MeasuredLocationRaccord {current} (one two : MeasuredLocationSource current) : Type where
  | checked (same : one.signature.code = two.signature.code)

def searchMeasuredLocationRaccord {current} (one two : MeasuredLocationSource current) :
    PSum (MeasuredLocationRaccord one two) (MeasuredLocationRaccord one two → False) :=
  if same : one.signature.code = two.signature.code then .inl (.checked same)
  else .inr (fun found => by cases found with | checked exactCode => exact same exactCode)

theorem measured_location_raccord_exact {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) : one.signature = two.signature := by
  cases found with | checked same => exact measured_signature_code_injective _ _ same

/-- Preservation is a separate proof. Equality of scalar readings alone is
not an input to the checker or a sufficient authorization. -/
theorem measured_location_raccord_preserves_readers {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) (request : MeasuredLocationRequest) :
    one.signature.read request = two.signature.read request :=
  congrArg (fun signature => signature.read request) (measured_location_raccord_exact found)

def groupMeasuredLocations {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) :
    ConstrainedMeasuredLocation current (one.window.intersection two.window) :=
  match found with
  | .checked same =>
    let value := one.signature.read .relative
    let correspondence := measured_signature_code_injective one.signature two.signature same
    ⟨one.signature, value, rfl, window_intersection_contains (by
      change one.window.Contains (one.signature.read .relative)
      rw [measured_signature_reads_constraint]
      exact one.reading.inside) (by
      change two.window.Contains (one.signature.read .relative)
      rw [correspondence, measured_signature_reads_constraint]
      exact two.reading.inside)⟩

theorem grouped_measured_locations_return_both {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) :
    (groupMeasuredLocations found).restrict (window_intersection_left one.window two.window) = one.project ∧
    (groupMeasuredLocations found).restrict (window_intersection_right one.window two.window) = two.project := by
  constructor
  · apply constrained_measured_location_ext
    cases found; rfl
  · apply constrained_measured_location_ext
    cases found with | checked same => exact measured_signature_code_injective _ _ same

theorem grouped_measured_reader_factorization {current} {one two : MeasuredLocationSource current}
    (found : MeasuredLocationRaccord one two) (request : MeasuredLocationRequest) :
    (groupMeasuredLocations found).signature.read request = one.signature.read request ∧
    (groupMeasuredLocations found).signature.read request = two.signature.read request := by
  cases found with | checked same =>
    exact ⟨rfl, congrArg (fun signature => signature.read request) (measured_signature_code_injective _ _ same)⟩

theorem different_anchor_refuses_measured_grouping {current} (one two : MeasuredLocationSource current)
    (different : one.signature.anchor ≠ two.signature.anchor) (found : MeasuredLocationRaccord one two) : False :=
  different (congrArg MeasuredLocationSignature.anchor (measured_location_raccord_exact found))

theorem measured_grouping_decision_exact {current} (one two : MeasuredLocationSource current) :
    (match searchMeasuredLocationRaccord one two with | .inl _ => true | .inr _ => false) = true ↔
      one.signature = two.signature := by
  constructor
  · intro accepted
    cases decision : searchMeasuredLocationRaccord one two with
    | inl found => exact measured_location_raccord_exact found
    | inr _ => rw [decision] at accepted; cases accepted
  · intro same
    have code := congrArg MeasuredLocationSignature.code same
    unfold searchMeasuredLocationRaccord
    rw [dif_pos code]

/-- Action and refusals consume the executed recognition. Neither branch
changes the live support or substitutes a singleton for the common target. -/
def checkAndGroupMeasuredLocations {current} (one two : MeasuredLocationSource current) :
    PSum (ConstrainedMeasuredLocation current (one.window.intersection two.window))
      (MeasuredLocationRaccord one two → False) :=
  match searchMeasuredLocationRaccord one two with
  | .inl found => .inl (groupMeasuredLocations found)
  | .inr refused => .inr refused

def measuredDescriptionPort {source result coarse} (description : @MeasuredDescriptionRun source result coarse)
    (participant : Port) : MeasuredLocationSource description.realization.state.coupling :=
  ⟨source, result, description.realization.chain.history, participant, description.window, description.reading⟩

def measuredDescriptionRaccord {source result coarse} (description : @MeasuredDescriptionRun source result coarse) :
    MeasuredLocationRaccord (measuredDescriptionPort description .left) (measuredDescriptionPort description .right) :=
  .checked rfl

theorem grouped_measured_sources_remain_distinct {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) :
    measuredDescriptionPort description .left ≠ measuredDescriptionPort description .right := by
  intro same
  have participants := congrArg MeasuredLocationSource.participant same
  cases participants

theorem measured_description_checker_accepts {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) :
    searchMeasuredLocationRaccord (measuredDescriptionPort description .left) (measuredDescriptionPort description .right) =
      .inl (measuredDescriptionRaccord description) := by
  unfold searchMeasuredLocationRaccord
  split
  · rfl
  · rename_i impossible
    exact False.elim (impossible rfl)

/-- Consumer for arbitrary finite P3 precision courses. It receives their
returned packet and never calls a measurement producer. -/
def groupedMeasuredDescription {source result coarse} (description : @MeasuredDescriptionRun source result coarse) :
    ConstrainedMeasuredLocation description.realization.state.coupling
      (description.window.intersection description.window) :=
  match checkAndGroupMeasuredLocations (measuredDescriptionPort description .left)
      (measuredDescriptionPort description .right) with
  | .inl common => common
  | .inr refused => False.elim (refused (measuredDescriptionRaccord description))

theorem grouped_measured_description_is_authorized {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) :
    groupedMeasuredDescription description = groupMeasuredLocations (measuredDescriptionRaccord description) := by
  unfold groupedMeasuredDescription checkAndGroupMeasuredLocations
  rw [measured_description_checker_accepts]

theorem measured_description_grouping_is_checker_output {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) :
    checkAndGroupMeasuredLocations (measuredDescriptionPort description .left) (measuredDescriptionPort description .right) =
      .inl (groupedMeasuredDescription description) := by
  unfold checkAndGroupMeasuredLocations
  rw [measured_description_checker_accepts]
  exact congrArg PSum.inl (grouped_measured_description_is_authorized description).symm

theorem measured_description_grouping_keeps_location {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) :
    (groupedMeasuredDescription description).signature.anchor =
      (measuredFirst result description.realization.chain.history).location ∧
    (groupedMeasuredDescription description).signature.anchor =
      (measuredSecond result description.realization.chain.history).location := by
  rw [grouped_measured_description_is_authorized]
  exact ⟨rfl, rfl⟩

theorem grouped_measured_description_every_precision {source result coarse}
    (description : @MeasuredDescriptionRun source result coarse) (requests : List MeasuredPrecisionRequest)
    (request : MeasuredPrecisionRequest) (requested : request ∈ requests) :
    Rational.Le (groupedMeasuredDescription (description.runMore requests)).window.span request.precision.value := by
  rw [grouped_measured_description_is_authorized]
  exact Rational.le_trans (window_intersection_left _ _).span_le
    (measured_description_bounds_every_request description requests request requested)

end RelationalPerimeter.Relativity.Reconstruction
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_signature_code_injective
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredLocationSignature.read
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredLocationSignature.prolong
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_signature_readers_prolong
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_signature_prolong_returns
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredLocationSource.signature
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_signature_reads_constraint
#print axioms RelationalPerimeter.Relativity.Reconstruction.MeasuredLocationSource.project
#print axioms RelationalPerimeter.Relativity.Reconstruction.ConstrainedMeasuredLocation.restrict
#print axioms RelationalPerimeter.Relativity.Reconstruction.ConstrainedMeasuredLocation.prolong
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_grouping_restriction_continuation_square
#print axioms RelationalPerimeter.Relativity.Reconstruction.constrained_measured_location_ext
#print axioms RelationalPerimeter.Relativity.Reconstruction.searchMeasuredLocationRaccord
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_location_raccord_exact
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_location_raccord_preserves_readers
#print axioms RelationalPerimeter.Relativity.Reconstruction.groupMeasuredLocations
#print axioms RelationalPerimeter.Relativity.Reconstruction.grouped_measured_locations_return_both
#print axioms RelationalPerimeter.Relativity.Reconstruction.grouped_measured_reader_factorization
#print axioms RelationalPerimeter.Relativity.Reconstruction.different_anchor_refuses_measured_grouping
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_grouping_decision_exact
#print axioms RelationalPerimeter.Relativity.Reconstruction.checkAndGroupMeasuredLocations
#print axioms RelationalPerimeter.Relativity.Reconstruction.measuredDescriptionRaccord
#print axioms RelationalPerimeter.Relativity.Reconstruction.grouped_measured_sources_remain_distinct
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_checker_accepts
#print axioms RelationalPerimeter.Relativity.Reconstruction.groupedMeasuredDescription
#print axioms RelationalPerimeter.Relativity.Reconstruction.grouped_measured_description_is_authorized
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_grouping_is_checker_output
#print axioms RelationalPerimeter.Relativity.Reconstruction.measured_description_grouping_keeps_location
#print axioms RelationalPerimeter.Relativity.Reconstruction.grouped_measured_description_every_precision
/- AXIOM_AUDIT_END -/
