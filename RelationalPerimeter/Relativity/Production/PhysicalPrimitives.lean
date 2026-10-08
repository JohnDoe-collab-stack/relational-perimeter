import RelationalPerimeter.Relativity.Arithmetic.OrderedFractions
import RelationalPerimeter.Constitution.Resources.TypedReferences

/-!
# Declared local law: calibrated signal records

This is a first non-geometric candidate, not a spacetime model. An instrument
supplies a rational reading, a payload and a positively calibrated increment.
Emission copies the local reading; relay adds the received increment and
records it; reception produces a reading from the received record. No shared
clock, proper time, distance, propagation speed or metric is asserted.

Calibration is received, not discovered. The numerical backend is used only
for these declared readings; it does not constitute resource occurrences.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

structure Calibration where
  increment : Rational
  nonnegative : Rational.Le Rational.zero increment
  nonzero : increment ≠ Rational.zero

def Calibration.unit : Calibration where
  increment := Rational.one
  nonnegative := by
    change Rational.Le Rational.zero (Rational.ofNat 1)
    exact Rational.nat_nonnegative 1
  nonzero := Rational.one_ne_zero

structure SignalRecord where
  payload : Nat
  reading : Rational
  increments : List Rational

def SignalRecord.emit (reading : Rational) (payload : Nat) : SignalRecord :=
  ⟨payload, reading, []⟩

def SignalRecord.relay (record : SignalRecord) (calibration : Calibration) : SignalRecord :=
  ⟨record.payload, Rational.add record.reading calibration.increment,
    record.increments ++ [calibration.increment]⟩

theorem relay_preserves_payload (record : SignalRecord) (calibration : Calibration) :
    (record.relay calibration).payload = record.payload := rfl

theorem relay_changes_reading (record : SignalRecord) (calibration : Calibration) :
    (record.relay calibration).reading ≠ record.reading := by
  intro same
  have cancelled := congrArg (fun reading => Rational.add (Rational.neg record.reading) reading) same
  change Rational.add (Rational.neg record.reading)
    (Rational.add record.reading calibration.increment) =
      Rational.add (Rational.neg record.reading) record.reading at cancelled
  rw [← Rational.add_assoc, Rational.neg_add_cancel, Rational.zero_add] at cancelled
  exact calibration.nonzero cancelled

theorem relay_composition_reading (record : SignalRecord) (one two : Calibration) :
    ((record.relay one).relay two).reading =
      Rational.add record.reading (Rational.add one.increment two.increment) :=
  Rational.add_assoc ..

inductive Kind where
  | reading | payload | calibration | signal

def Value : Kind → Type
  | .reading => Rational
  | .payload => Nat
  | .calibration => Calibration
  | .signal => SignalRecord

structure Received where
  reading : Rational
  payload : Nat
  calibration : Calibration

def receivedKinds : List Kind := [.reading, .payload, .calibration]

def Received.values (input : Received) : Values Value receivedKinds :=
  (input.reading, input.payload, input.calibration, PUnit.unit)

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.Calibration
#print axioms RelationalPerimeter.Relativity.Production.Calibration.unit
#print axioms RelationalPerimeter.Relativity.Production.SignalRecord.emit
#print axioms RelationalPerimeter.Relativity.Production.SignalRecord.relay
#print axioms RelationalPerimeter.Relativity.Production.relay_preserves_payload
#print axioms RelationalPerimeter.Relativity.Production.relay_changes_reading
#print axioms RelationalPerimeter.Relativity.Production.relay_composition_reading
#print axioms RelationalPerimeter.Relativity.Production.Value
#print axioms RelationalPerimeter.Relativity.Production.Received.values
/- AXIOM_AUDIT_END -/
