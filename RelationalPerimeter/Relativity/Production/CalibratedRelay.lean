import RelationalPerimeter.Relativity.Production.ConstitutedEvents

/-!
# A closed, parameterized family of local productions

All initial readings, payloads and calibrations are declared received data.
Emission, arbitrarily many relays and reception use the same closed interpreter.
The relay count describes this finite schedule, not physical duration or a
maximum history length. No grouping or relativistic reconstruction is claimed.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources

def relayProgram {context} (signal : Ref context .signal) (calibration : Ref context .calibration) :
    Nat → Program context
  | 0 => .done
  | count + 1 => .step (.relay signal calibration)
      (relayProgram .here (.prior calibration) count)

theorem relayProgram_steps {context : List Kind} (signal : Ref context .signal)
    (calibration : Ref context .calibration) (count : Nat) :
    (relayProgram signal calibration count).steps = count := by
  induction count generalizing context with
  | zero => rfl
  | succ count ih => exact congrArg (fun n => n + 1) (ih .here (.prior calibration))

def emission : Instruction receivedKinds .signal := .emit .here (.prior .here)

def relayScenario (count : Nat) : Program receivedKinds :=
  .step emission (relayProgram .here (.prior (.prior (.prior .here))) count)

def relayExecution (input : Received) (count : Nat) : Execution (Cursor.received input) :=
  run (Cursor.received input) (relayScenario count)

theorem relay_history_length (input : Received) (count : Nat) :
    StrongPerimetralTurning.History.length (relayExecution input count).history = count + 1 :=
  (run_history_length (Cursor.received input) (relayScenario count)).trans
    (congrArg (fun n => n + 1) (relayProgram_steps .here (.prior (.prior (.prior .here))) count))

def emittedCursor (input : Received) : Cursor :=
  (perform (Cursor.received input) emission).successor

def reception (input : Received) : Instruction (emittedCursor input).kinds .reading := .receive .here

def receiveEmission (input : Received) := perform (emittedCursor input) (reception input)

theorem reception_reads_produced_emission (input : Received) :
    (receiveEmission input).determination.1 = input.reading := rfl

theorem equal_readings_distinct_occurrences (input : Received) :
    (receiveEmission input).successor.read (Ref.here : Ref (.reading :: (emittedCursor input).kinds) .reading) =
      (receiveEmission input).successor.read (.prior (.prior .here)) ∧
    (Ref.here : Ref (.reading :: (emittedCursor input).kinds) .reading) ≠ .prior (.prior .here) :=
  ⟨rfl, fresh_distinct (emittedCursor input) (receiveEmission input).determination (.prior .here)⟩

theorem emission_depends_on_received_reading (first second : Received)
    (distinct : first.reading ≠ second.reading) :
    (perform (Cursor.received first) emission).determination.1 ≠
      (perform (Cursor.received second) emission).determination.1 :=
  fun same => distinct (congrArg SignalRecord.reading same)

def latestSignal : (context : List Kind) → Values Value context → Option SignalRecord
  | [], _ => none
  | .reading :: _, _ => none
  | .payload :: _, _ => none
  | .calibration :: _, _ => none
  | .signal :: _, values => some values.1

def Cursor.latestSignal (cursor : Cursor) : Option SignalRecord :=
  RelationalPerimeter.Relativity.Production.latestSignal cursor.kinds cursor.values

def relaySmoke (count : Nat) : Option Nat :=
  match (relayExecution ⟨Rational.zero, 7, Calibration.unit⟩ count).cursor.latestSignal with
  | some signal => some signal.increments.length
  | none => none

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.relayProgram
#print axioms RelationalPerimeter.Relativity.Production.relayProgram_steps
#print axioms RelationalPerimeter.Relativity.Production.relayScenario
#print axioms RelationalPerimeter.Relativity.Production.relayExecution
#print axioms RelationalPerimeter.Relativity.Production.relay_history_length
#print axioms RelationalPerimeter.Relativity.Production.emittedCursor
#print axioms RelationalPerimeter.Relativity.Production.receiveEmission
#print axioms RelationalPerimeter.Relativity.Production.reception_reads_produced_emission
#print axioms RelationalPerimeter.Relativity.Production.equal_readings_distinct_occurrences
#print axioms RelationalPerimeter.Relativity.Production.emission_depends_on_received_reading
#print axioms RelationalPerimeter.Relativity.Production.latestSignal
#print axioms RelationalPerimeter.Relativity.Production.Cursor.latestSignal
#print axioms RelationalPerimeter.Relativity.Production.relaySmoke
/- AXIOM_AUDIT_END -/
