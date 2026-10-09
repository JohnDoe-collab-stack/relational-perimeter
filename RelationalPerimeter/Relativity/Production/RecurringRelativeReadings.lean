import RelationalPerimeter.Relativity.Production.RecurringSignalJourneys

/-!
# Received relative paths on the interacting support

The ratio reads actual arrivals and their positive common-origin calibrated
journeys. It remains a downstream instrumental reading. History transport
preserves it through comparisons as well as signals, without rerunning a
producer or supplying a target number.
-/
set_option genInjectivity false
set_option genSizeOf false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure RecurringRelativeReading (source : RecurringCursor) where
  arrivals : RecurringPair source
  numerator : RecurringJourney source.formation arrivals.firstSignal
  denominator : RecurringJourney source.formation arrivals.secondSignal
  numeratorUnit : RecurringUnitJourney numerator
  denominatorUnit : RecurringUnitJourney denominator
  commonOrigin : numerator.origin = denominator.origin
  positiveScale : 0 < denominator.relayCount

def RecurringRelativeReading.fromReading {source : Cursor} (reading : RelativePathReading source) :
    RecurringRelativeReading (.fromCursor source) :=
  ⟨⟨reading.arrivals.first, reading.arrivals.second, reading.arrivals.firstSignal,
      reading.arrivals.secondSignal, .fromCursor reading.arrivals.firstArrival,
      .fromCursor reading.arrivals.secondArrival, reading.arrivals.distinct⟩,
    .fromCursor reading.numerator, .fromCursor reading.denominator,
    .fromCursor reading.numeratorUnit, .fromCursor reading.denominatorUnit,
    reading.commonOrigin, reading.positiveScale⟩

def RecurringRelativeReading.numeratorGap {source} (reading : RecurringRelativeReading source) : Rational :=
  Rational.sub reading.arrivals.firstArrival.measure (source.read reading.numerator.origin).reading

def RecurringRelativeReading.denominatorGap {source} (reading : RecurringRelativeReading source) : Rational :=
  Rational.sub reading.arrivals.secondArrival.measure (source.read reading.numerator.origin).reading

def RecurringRelativeReading.value {source} (reading : RecurringRelativeReading source) : Rational :=
  Rational.mul reading.numeratorGap (Rational.inverseNatSucc (reading.denominator.relayCount - 1))

private theorem subtract_origin (origin value : Rational) :
    Rational.sub (Rational.add origin value) origin = value := by
  unfold Rational.sub
  rw [Rational.add_comm origin value, Rational.add_assoc, Rational.add_neg, Rational.add_zero]

theorem RecurringRelativeReading.numerator_gap_exact {source} (reading : RecurringRelativeReading source) :
    reading.numeratorGap = Rational.ofNat reading.numerator.relayCount := by
  unfold numeratorGap
  rw [reading.arrivals.firstArrival.measure_exact, reading.arrivals.firstArrival.signal_reading,
    reading.numeratorUnit.reading_exact]
  exact subtract_origin _ _

theorem RecurringRelativeReading.denominator_gap_exact {source} (reading : RecurringRelativeReading source) :
    reading.denominatorGap = Rational.ofNat reading.denominator.relayCount := by
  unfold denominatorGap
  rw [reading.arrivals.secondArrival.measure_exact, reading.arrivals.secondArrival.signal_reading,
    reading.denominatorUnit.reading_exact, reading.commonOrigin]
  exact subtract_origin _ _

theorem RecurringRelativeReading.count_ratio_exact {source} (reading : RecurringRelativeReading source) :
    reading.value = Rational.mul (Rational.ofNat reading.numerator.relayCount)
      (Rational.inverseNatSucc (reading.denominator.relayCount - 1)) :=
  congrArg (fun gap => Rational.mul gap (Rational.inverseNatSucc (reading.denominator.relayCount - 1)))
    reading.numerator_gap_exact

theorem RecurringRelativeReading.scale_inverse {source} (reading : RecurringRelativeReading source) :
    Rational.mul reading.denominatorGap (Rational.inverseNatSucc (reading.denominator.relayCount - 1)) =
      Rational.one := by
  rw [reading.denominator_gap_exact]
  have count : reading.denominator.relayCount - 1 + 1 = reading.denominator.relayCount := by
    cases value : reading.denominator.relayCount with
    | zero => exact False.elim (Nat.not_lt_zero 0 (value ▸ reading.positiveScale))
    | succ n => rfl
  exact (congrArg (fun n => Rational.mul (Rational.ofNat n)
      (Rational.inverseNatSucc (reading.denominator.relayCount - 1))) count).symm.trans
    (Rational.nat_succ_inverse _)

theorem RecurringRelativeReading.measured_ratio_exact {source} (reading : RecurringRelativeReading source) :
    Rational.mul reading.value reading.denominatorGap = reading.numeratorGap := by
  unfold value
  rw [Rational.mul_assoc, Rational.mul_comm _ reading.denominatorGap, reading.scale_inverse, Rational.mul_one]

def RecurringRelativeReading.transport {source target} (reading : RecurringRelativeReading source)
    (history : RecurringHistory source target) : RecurringRelativeReading target :=
  ⟨reading.arrivals.transport history, reading.numerator.transport history,
    reading.denominator.transport history, reading.numeratorUnit.transport history,
    reading.denominatorUnit.transport history,
    (reading.numerator.transport_origin history).trans
      ((congrArg (recurringHistoryTransport history).references reading.commonOrigin).trans
        (reading.denominator.transport_origin history).symm),
    (reading.denominator.transport_count history).symm ▸ reading.positiveScale⟩

theorem RecurringRelativeReading.transport_value {source target} (reading : RecurringRelativeReading source)
    (history : RecurringHistory source target) : (reading.transport history).value = reading.value := by
  rw [(reading.transport history).count_ratio_exact, reading.count_ratio_exact]
  change Rational.mul (Rational.ofNat (reading.numerator.transport history).relayCount)
    (Rational.inverseNatSucc ((reading.denominator.transport history).relayCount - 1)) = _
  rw [reading.numerator.transport_count history, reading.denominator.transport_count history]

theorem recurring_lift_reads_same_ratio {source : Cursor} (reading : RelativePathReading source) :
    (RecurringRelativeReading.fromReading reading).value = reading.value := rfl

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.fromReading
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.value
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.numerator_gap_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.denominator_gap_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.count_ratio_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.scale_inverse
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.measured_ratio_exact
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.transport
#print axioms RelationalPerimeter.Relativity.Production.RecurringRelativeReading.transport_value
#print axioms RelationalPerimeter.Relativity.Production.recurring_lift_reads_same_ratio
/- AXIOM_AUDIT_END -/
