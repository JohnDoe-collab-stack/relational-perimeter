import RelationalPerimeter.Relativity.Production.ArrivalComparisons

/-!
# Relative readings of two actually received calibrated paths

The numerator is read from an actual reception relative to its emitted
origin. The unit of the reader is another received path from that same
emission, containing a positive number of unit-calibrated relays. Counts
are eliminated from the stored positive journeys, not received as readings.
This downstream instrumental reader is neither a new signal primitive nor
a spacetime coordinate. No rich path effect or source distinction is erased.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

/-- Positive evidence that each relay in this stored journey consumed a
unit calibration. Merely having the same final number does not supply it. -/
inductive UnitJourney : {context : List Kind} → {values : Values Value context} →
    {formation : Formed (context := context) values} → {signal : Ref context .signal} →
    SignalJourney formation signal → Type where
  | emitted {context} {values : Values Value context}
      (past : Formed (context := context) values)
      (reading : Ref context .reading) (payload : Ref context .payload) :
      UnitJourney (.emitted past reading payload)
  | relayed {context} {values : Values Value context} {past : Formed (context := context) values}
      {signal : Ref context .signal} {calibration : Ref context .calibration}
      {journey : SignalJourney past signal} (prior : UnitJourney journey)
      (unit : (read values calibration).increment = Rational.one) :
      UnitJourney (.relayed calibration journey)
  | inherited {context} {values : Values Value context} {past : Formed (context := context) values}
      {kind} {instruction : Instruction context kind} {output : Value kind}
      (role : Produces values instruction output) {signal : Ref context .signal}
      {journey : SignalJourney past signal} (prior : UnitJourney journey) :
      UnitJourney (.inherited role journey)

theorem UnitJourney.reading_exact {context} {values : Values Value context}
    {formation : Formed (context := context) values} {signal : Ref context .signal}
    {journey : SignalJourney formation signal} (unit : UnitJourney journey) :
    (read values signal).reading =
      Rational.add (read values journey.origin).reading (Rational.ofNat journey.relayCount) := by
  induction unit with
  | emitted past reading payload => exact (Rational.add_zero _).symm
  | @relayed context values past signal calibration journey prior unit ih =>
    change Rational.add (read values signal).reading (read values calibration).increment =
      Rational.add (read values journey.origin).reading (Rational.ofNat (journey.relayCount + 1))
    have one : Rational.one = Rational.ofNat 1 := rfl
    rw [unit, ih, Rational.add_assoc, one, Rational.nat_add]
  | inherited role prior ih => exact ih

def SignalJourney.transport {source target : Cursor} (history : LocalHistory source target)
    {signal : Ref source.kinds .signal} (journey : SignalJourney source.formation signal) :
    SignalJourney target.formation ((historyTransport history).references signal) :=
  match history with
  | .root => journey
  | .extend past step => by
    cases step with
    | mk kind instruction determination exactTarget =>
      cases exactTarget
      exact .inherited determination.2 (journey.transport past)
termination_by structural history

theorem SignalJourney.transport_origin {source target : Cursor} (history : LocalHistory source target)
    {signal : Ref source.kinds .signal} (journey : SignalJourney source.formation signal) :
    (journey.transport history).origin = (historyTransport history).references journey.origin := by
  induction history with
  | root => rfl
  | extend past step ih =>
    cases step with
    | mk kind instruction determination exactTarget =>
      cases exactTarget
      exact congrArg Ref.prior ih

theorem SignalJourney.transport_count {source target : Cursor} (history : LocalHistory source target)
    {signal : Ref source.kinds .signal} (journey : SignalJourney source.formation signal) :
    (journey.transport history).relayCount = journey.relayCount := by
  induction history with
  | root => rfl
  | extend past step ih =>
    cases step with
    | mk kind instruction determination exactTarget => cases exactTarget; exact ih

def UnitJourney.transport {source target : Cursor} (history : LocalHistory source target)
    {signal : Ref source.kinds .signal} {journey : SignalJourney source.formation signal}
    (unit : UnitJourney journey) : UnitJourney (journey.transport history) :=
  match history with
  | .root => unit
  | .extend past step => by
    cases step with
    | mk kind instruction determination exactTarget =>
      cases exactTarget
      exact .inherited determination.2 (unit.transport past)
termination_by structural history

/-- Both reception contexts and both positive journeys belong to this exact
formed support. A positive reference path supplies the scale. Neither an
independent output nor a prescribed rational target is a constructor input. -/
structure RelativePathReading (source : Cursor) where
  arrivals : ArrivalPair source
  numerator : SignalJourney source.formation arrivals.firstSignal
  denominator : SignalJourney source.formation arrivals.secondSignal
  numeratorUnit : UnitJourney numerator
  denominatorUnit : UnitJourney denominator
  commonOrigin : numerator.origin = denominator.origin
  positiveScale : 0 < denominator.relayCount

def RelativePathReading.numeratorGap {source : Cursor} (reading : RelativePathReading source) : Rational :=
  Rational.sub reading.arrivals.firstArrival.measure (source.read reading.numerator.origin).reading

def RelativePathReading.denominatorGap {source : Cursor} (reading : RelativePathReading source) : Rational :=
  Rational.sub reading.arrivals.secondArrival.measure (source.read reading.numerator.origin).reading

def RelativePathReading.value {source : Cursor} (reading : RelativePathReading source) : Rational :=
  Rational.mul reading.numeratorGap (Rational.inverseNatSucc (reading.denominator.relayCount - 1))

private theorem subtract_origin (origin value : Rational) :
    Rational.sub (Rational.add origin value) origin = value := by
  unfold Rational.sub
  rw [Rational.add_comm origin value, Rational.add_assoc, Rational.add_neg, Rational.add_zero]

theorem RelativePathReading.numerator_gap_exact {source : Cursor} (reading : RelativePathReading source) :
    reading.numeratorGap = Rational.ofNat reading.numerator.relayCount := by
  unfold numeratorGap
  rw [reading.arrivals.firstArrival.measure_exact]
  change Rational.sub (read source.values reading.arrivals.first)
    (read source.values reading.numerator.origin).reading = _
  rw [reading.arrivals.firstArrival.reading_exact, reading.numeratorUnit.reading_exact]
  exact subtract_origin _ _

theorem RelativePathReading.denominator_gap_exact {source : Cursor} (reading : RelativePathReading source) :
    reading.denominatorGap = Rational.ofNat reading.denominator.relayCount := by
  unfold denominatorGap
  rw [reading.arrivals.secondArrival.measure_exact]
  change Rational.sub (read source.values reading.arrivals.second)
    (read source.values reading.numerator.origin).reading = _
  rw [reading.arrivals.secondArrival.reading_exact, reading.denominatorUnit.reading_exact,
    reading.commonOrigin]
  exact subtract_origin _ _

theorem RelativePathReading.scale_inverse {source : Cursor} (reading : RelativePathReading source) :
    Rational.mul reading.denominatorGap
      (Rational.inverseNatSucc (reading.denominator.relayCount - 1)) = Rational.one := by
  rw [reading.denominator_gap_exact]
  have count : reading.denominator.relayCount - 1 + 1 = reading.denominator.relayCount := by
    cases value : reading.denominator.relayCount with
    | zero => exact False.elim (Nat.not_lt_zero 0 (value ▸ reading.positiveScale))
    | succ n => rfl
  exact (congrArg (fun n => Rational.mul (Rational.ofNat n)
      (Rational.inverseNatSucc (reading.denominator.relayCount - 1))) count).symm.trans
    (Rational.nat_succ_inverse _)

/-- The reader is licensed by the actual received reference interval. -/
theorem RelativePathReading.measured_ratio_exact {source : Cursor} (reading : RelativePathReading source) :
    Rational.mul reading.value reading.denominatorGap = reading.numeratorGap := by
  unfold value
  rw [Rational.mul_assoc, Rational.mul_comm _ reading.denominatorGap,
    reading.scale_inverse, Rational.mul_one]

theorem RelativePathReading.count_ratio_exact {source : Cursor} (reading : RelativePathReading source) :
    reading.value = Rational.mul (Rational.ofNat reading.numerator.relayCount)
      (Rational.inverseNatSucc (reading.denominator.relayCount - 1)) :=
  congrArg (fun gap => Rational.mul gap
    (Rational.inverseNatSucc (reading.denominator.relayCount - 1))) reading.numerator_gap_exact

def RelativePathReading.transport {source target : Cursor} (history : LocalHistory source target)
    (reading : RelativePathReading source) : RelativePathReading target where
  arrivals :=
    ⟨(historyTransport history).references reading.arrivals.first,
      (historyTransport history).references reading.arrivals.second,
      (historyTransport history).references reading.arrivals.firstSignal,
      (historyTransport history).references reading.arrivals.secondSignal,
      historyTransportArrival history reading.arrivals.firstArrival,
      historyTransportArrival history reading.arrivals.secondArrival,
      history_preserves_distinction history _ _ reading.arrivals.distinct⟩
  numerator := reading.numerator.transport history
  denominator := reading.denominator.transport history
  numeratorUnit := reading.numeratorUnit.transport history
  denominatorUnit := reading.denominatorUnit.transport history
  commonOrigin := (reading.numerator.transport_origin history).trans
    ((congrArg (historyTransport history).references reading.commonOrigin).trans
      (reading.denominator.transport_origin history).symm)
  positiveScale := (reading.denominator.transport_count history).symm ▸ reading.positiveScale

theorem RelativePathReading.transport_value {source target : Cursor} (history : LocalHistory source target)
    (reading : RelativePathReading source) : (reading.transport history).value = reading.value := by
  rw [(reading.transport history).count_ratio_exact, reading.count_ratio_exact]
  change Rational.mul (Rational.ofNat (reading.numerator.transport history).relayCount)
    (Rational.inverseNatSucc ((reading.denominator.transport history).relayCount - 1)) = _
  rw [reading.numerator.transport_count history, reading.denominator.transport_count history]

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.UnitJourney
#print axioms RelationalPerimeter.Relativity.Production.UnitJourney.reading_exact
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.transport
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.transport_origin
#print axioms RelationalPerimeter.Relativity.Production.SignalJourney.transport_count
#print axioms RelationalPerimeter.Relativity.Production.UnitJourney.transport
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.value
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.numerator_gap_exact
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.denominator_gap_exact
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.scale_inverse
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.measured_ratio_exact
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.count_ratio_exact
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.transport
#print axioms RelationalPerimeter.Relativity.Production.RelativePathReading.transport_value
/- AXIOM_AUDIT_END -/
