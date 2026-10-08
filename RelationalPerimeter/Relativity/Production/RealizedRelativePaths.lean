import RelationalPerimeter.Relativity.Production.RelativePathReadings

/-!
# Finite realizations of relative path readings

One actual emission is prolonged into two received paths on the same formed
support. The second path resumes from the original emission, not from the
first path's endpoint. Every paired production is bound once, then reused
for its successor, role, path and history. The length parameters schedule
finite relays; they do not supply output readings or geometric points.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure UnitRelayExecution (source : Cursor) {signal : Ref source.kinds .signal}
    (origin : SignalJourney source.formation signal) (count : Nat) where
  cursor : Cursor
  history : LocalHistory source cursor
  lastSignal : Ref cursor.kinds .signal
  calibration : Ref cursor.kinds .calibration
  calibrationUnit : (cursor.read calibration).increment = Rational.one
  journey : SignalJourney cursor.formation lastSignal
  unitJourney : UnitJourney journey
  originExact : journey.origin = (historyTransport history).references origin.origin
  countExact : journey.relayCount = origin.relayCount + count

/-- This runner receives the already formed origin and unit calibration.
Its recursive prefix is evaluated once; only its returned cursor supplies
the next relay. No completed future or independent reading is an input. -/
def runUnitRelays (source : Cursor) {signal : Ref source.kinds .signal}
    (origin : SignalJourney source.formation signal) (unit : UnitJourney origin)
    (calibration : Ref source.kinds .calibration)
    (calibrationUnit : (source.read calibration).increment = Rational.one) :
    (count : Nat) → UnitRelayExecution source origin count
  | 0 => ⟨source, .root, signal, calibration, calibrationUnit, origin, unit, rfl,
      (Nat.add_zero _).symm⟩
  | count + 1 =>
    let prior := runUnitRelays source origin unit calibration calibrationUnit count
    let head := perform prior.cursor (.relay prior.lastSignal prior.calibration)
    let history : LocalHistory source head.successor :=
      .extend prior.history ⟨.signal, .relay prior.lastSignal prior.calibration,
        head.determination, head.successorExact⟩
    ⟨head.successor, history, .here, .prior prior.calibration, prior.calibrationUnit,
      .relayed prior.calibration prior.journey, .relayed prior.unitJourney prior.calibrationUnit,
      congrArg Ref.prior prior.originExact,
      (congrArg (fun n => n + 1) prior.countExact).trans (Nat.add_assoc _ _ _)⟩

theorem unit_relays_history_length (source : Cursor) {signal : Ref source.kinds .signal}
    (origin : SignalJourney source.formation signal) (unit : UnitJourney origin)
    (calibration : Ref source.kinds .calibration)
    (calibrationUnit : (source.read calibration).increment = Rational.one) (count : Nat) :
    StrongPerimetralTurning.History.length
      (runUnitRelays source origin unit calibration calibrationUnit count).history = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (fun n => n + 1) ih

structure RelativeReadingExecution (source : Cursor) (numerator denominatorMinusOne : Nat) where
  cursor : Cursor
  history : LocalHistory source cursor
  reading : RelativePathReading cursor
  numeratorCount : reading.numerator.relayCount = numerator
  denominatorCount : reading.denominator.relayCount = denominatorMinusOne + 1

/-- Execute both branches from the same cached emission. The second branch
and both receptions retain the first branch in their actual prefix. -/
def realizeRelativeReading (source : Cursor)
    (reading : Ref source.kinds .reading) (payload : Ref source.kinds .payload)
    (calibration : Ref source.kinds .calibration)
    (calibrationUnit : (source.read calibration).increment = Rational.one)
    (numerator denominatorMinusOne : Nat) : RelativeReadingExecution source numerator denominatorMinusOne := by
  let emitted := perform source (.emit reading payload)
  let emittedHistory : LocalHistory source emitted.successor :=
    .extend .root ⟨.signal, .emit reading payload, emitted.determination, emitted.successorExact⟩
  let origin : SignalJourney emitted.successor.formation .here := .emitted source.formation reading payload
  let unitOrigin : UnitJourney origin := .emitted source.formation reading payload
  let first := runUnitRelays emitted.successor origin unitOrigin (.prior calibration) calibrationUnit numerator
  let firstReception := perform first.cursor (.receive first.lastSignal)
  let firstReceivedHistory : LocalHistory emitted.successor firstReception.successor :=
    .extend first.history ⟨.reading, .receive first.lastSignal,
      firstReception.determination, firstReception.successorExact⟩
  let firstJourney : SignalJourney firstReception.successor.formation (.prior first.lastSignal) :=
    .inherited firstReception.determination.2 first.journey
  let firstUnit : UnitJourney firstJourney := .inherited firstReception.determination.2 first.unitJourney
  let receivedOrigin := origin.transport firstReceivedHistory
  let receivedCalibration := (historyTransport firstReceivedHistory).references (.prior calibration)
  have receivedUnit : (firstReception.successor.read receivedCalibration).increment = Rational.one :=
    (congrArg Calibration.increment (history_preserves_reads firstReceivedHistory (.prior calibration))).trans
      calibrationUnit
  let second := runUnitRelays firstReception.successor receivedOrigin
    (unitOrigin.transport firstReceivedHistory) receivedCalibration receivedUnit (denominatorMinusOne + 1)
  let secondReception := perform second.cursor (.receive second.lastSignal)
  let suffix : LocalHistory firstReception.successor secondReception.successor :=
    .extend second.history ⟨.reading, .receive second.lastSignal,
      secondReception.determination, secondReception.successorExact⟩
  let firstArrival := historyTransportArrival suffix (arrivalOfProduction firstReception)
  let secondArrival := arrivalOfProduction secondReception
  let arrivals : ArrivalPair secondReception.successor :=
    ⟨(historyTransport suffix).references .here, .here,
      (historyTransport suffix).references (.prior first.lastSignal), .prior second.lastSignal,
      firstArrival, secondArrival, fun same =>
        fresh_position_distinct ((historyTransport second.history).references .here)
          (congrArg Ref.position same.symm)⟩
  let numeratorJourney := firstJourney.transport suffix
  let denominatorJourney : SignalJourney secondReception.successor.formation (.prior second.lastSignal) :=
    .inherited secondReception.determination.2 second.journey
  have firstOrigin : firstJourney.origin = (historyTransport firstReceivedHistory).references origin.origin :=
    congrArg Ref.prior first.originExact
  have common : numeratorJourney.origin = denominatorJourney.origin :=
    (firstJourney.transport_origin suffix).trans
      ((congrArg (historyTransport suffix).references firstOrigin).trans
        ((congrArg (historyTransport suffix).references
          (origin.transport_origin firstReceivedHistory).symm).trans
          (congrArg Ref.prior second.originExact).symm))
  have firstCount : numeratorJourney.relayCount = numerator :=
    (firstJourney.transport_count suffix).trans (first.countExact.trans (Nat.zero_add numerator))
  have secondCount : denominatorJourney.relayCount = denominatorMinusOne + 1 :=
    second.countExact.trans ((congrArg (fun n => n + (denominatorMinusOne + 1))
      (origin.transport_count firstReceivedHistory)).trans (Nat.zero_add _))
  let result : RelativePathReading secondReception.successor :=
    ⟨arrivals, numeratorJourney, denominatorJourney, firstUnit.transport suffix,
      .inherited secondReception.determination.2 second.unitJourney, common,
      secondCount.symm ▸ Nat.zero_lt_succ denominatorMinusOne⟩
  exact ⟨secondReception.successor,
    StrongPerimetralTurning.History.append emittedHistory
      (StrongPerimetralTurning.History.append firstReceivedHistory suffix),
    result, firstCount, secondCount⟩

theorem RelativeReadingExecution.value_exact {source : Cursor} {numerator denominatorMinusOne : Nat}
    (result : RelativeReadingExecution source numerator denominatorMinusOne) :
    result.reading.value = Rational.mul (Rational.ofNat numerator)
      (Rational.inverseNatSucc denominatorMinusOne) := by
  rw [result.reading.count_ratio_exact, result.numeratorCount, result.denominatorCount,
    Nat.succ_sub_succ, Nat.sub_zero]

theorem realized_relative_reading_exact (source : Cursor)
    (reading : Ref source.kinds .reading) (payload : Ref source.kinds .payload)
    (calibration : Ref source.kinds .calibration)
    (calibrationUnit : (source.read calibration).increment = Rational.one)
    (numerator denominatorMinusOne : Nat) :
    (realizeRelativeReading source reading payload calibration calibrationUnit
      numerator denominatorMinusOne).reading.value =
        Rational.mul (Rational.ofNat numerator) (Rational.inverseNatSucc denominatorMinusOne) :=
  RelativeReadingExecution.value_exact _

theorem path_count_fraction (numerator denominatorMinusOne : Nat) :
    Rational.mul (Rational.ofNat numerator) (Rational.inverseNatSucc denominatorMinusOne) =
      Rational.ofParts numerator 0 denominatorMinusOne := by
  apply Rational.normalize_congr
  apply Arithmetic.Fraction.trans (Arithmetic.Fraction.mul_congr
    (Rational.normalize_agrees _) (Rational.normalize_agrees _))
  unfold Arithmetic.Fraction.Agree Arithmetic.Fraction.mul Arithmetic.Fraction.nat
    Arithmetic.Fraction.ofParts Arithmetic.Balance.Agree Arithmetic.Balance.scale
    Arithmetic.Balance.mul Arithmetic.Balance.nat
  exact_natural

theorem realized_relative_fraction_exact (source : Cursor)
    (reading : Ref source.kinds .reading) (payload : Ref source.kinds .payload)
    (calibration : Ref source.kinds .calibration)
    (calibrationUnit : (source.read calibration).increment = Rational.one)
    (numerator denominatorMinusOne : Nat) :
    (realizeRelativeReading source reading payload calibration calibrationUnit
      numerator denominatorMinusOne).reading.value = Rational.ofParts numerator 0 denominatorMinusOne :=
  (realized_relative_reading_exact ..).trans (path_count_fraction ..)

theorem realized_relative_history_length (source : Cursor)
    (reading : Ref source.kinds .reading) (payload : Ref source.kinds .payload)
    (calibration : Ref source.kinds .calibration)
    (calibrationUnit : (source.read calibration).increment = Rational.one)
    (numerator denominatorMinusOne : Nat) :
    StrongPerimetralTurning.History.length
      (realizeRelativeReading source reading payload calibration calibrationUnit
        numerator denominatorMinusOne).history = numerator + (denominatorMinusOne + 1) + 3 := by
  dsimp only [realizeRelativeReading]
  rw [StrongPerimetralTurning.History.length_append, StrongPerimetralTurning.History.length_append]
  change 1 + ((_ + 1) + (_ + 1)) = _
  rw [unit_relays_history_length]
  have firstLength := unit_relays_history_length (perform source (.emit reading payload)).successor
    (.emitted source.formation reading payload) (.emitted source.formation reading payload)
    (.prior calibration) calibrationUnit numerator
  exact (congrArg (fun n => 1 + ((n + 1) + (denominatorMinusOne + 1 + 1))) firstLength).trans
    (by exact_natural)

/-- The stored realization supplies the actual cursor for one new suffix.
Transport reads the returned suffix history; it executes no prefix again. -/
def RelativeReadingExecution.continue {source : Cursor} {numerator denominatorMinusOne : Nat}
    (result : RelativeReadingExecution source numerator denominatorMinusOne)
    (schedule : Program result.cursor.kinds) : RelativeReadingExecution source numerator denominatorMinusOne :=
  let resumed := run result.cursor schedule
  let reading := result.reading.transport resumed.history
  ⟨resumed.cursor, StrongPerimetralTurning.History.append result.history resumed.history, reading,
    (result.reading.numerator.transport_count resumed.history).trans result.numeratorCount,
    (result.reading.denominator.transport_count resumed.history).trans result.denominatorCount⟩

theorem relative_continuation_reading_exact {source : Cursor} {numerator denominatorMinusOne : Nat}
    (result : RelativeReadingExecution source numerator denominatorMinusOne)
    (schedule : Program result.cursor.kinds) :
    (result.continue schedule).reading =
      result.reading.transport (run result.cursor schedule).history := rfl

theorem relative_continuation_value_exact {source : Cursor} {numerator denominatorMinusOne : Nat}
    (result : RelativeReadingExecution source numerator denominatorMinusOne)
    (schedule : Program result.cursor.kinds) : (result.continue schedule).reading.value = result.reading.value :=
  result.reading.transport_value (run result.cursor schedule).history

theorem relative_continuation_keeps_both_sources {source : Cursor} {numerator denominatorMinusOne : Nat}
    (result : RelativeReadingExecution source numerator denominatorMinusOne)
    (schedule : Program result.cursor.kinds) :
    (result.continue schedule).reading.arrivals.first ≠ (result.continue schedule).reading.arrivals.second :=
  (result.continue schedule).reading.arrivals.distinct

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.UnitRelayExecution
#print axioms RelationalPerimeter.Relativity.Production.runUnitRelays
#print axioms RelationalPerimeter.Relativity.Production.unit_relays_history_length
#print axioms RelationalPerimeter.Relativity.Production.RelativeReadingExecution
#print axioms RelationalPerimeter.Relativity.Production.realizeRelativeReading
#print axioms RelationalPerimeter.Relativity.Production.RelativeReadingExecution.value_exact
#print axioms RelationalPerimeter.Relativity.Production.realized_relative_reading_exact
#print axioms RelationalPerimeter.Relativity.Production.path_count_fraction
#print axioms RelationalPerimeter.Relativity.Production.realized_relative_fraction_exact
#print axioms RelationalPerimeter.Relativity.Production.realized_relative_history_length
#print axioms RelationalPerimeter.Relativity.Production.RelativeReadingExecution.continue
#print axioms RelationalPerimeter.Relativity.Production.relative_continuation_reading_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_continuation_value_exact
#print axioms RelationalPerimeter.Relativity.Production.relative_continuation_keeps_both_sources
/- AXIOM_AUDIT_END -/
