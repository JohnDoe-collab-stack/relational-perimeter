import RelationalPerimeter.Relativity.Production.PortAdmissions
import RelationalPerimeter.Constitution.Continuation.Behavior

/-!
# Fixed request contract of the calibrated-record candidate

The contract includes arbitrary finite interleavings of emission, relay,
reception and inspection of any currently available typed resource. Inspection
of a signal exposes its payload, reading and complete increment list: paths
with different such records cannot be erased using a reading-only agreement.
There is no passive observation beyond explicit requests. Addresses are local
resource selectors, not coordinates. This is not the final physical contract.

`referenceNext` and `referenceEvent` are separate specification projections;
the executable paired runner is provided downstream, not this generic outcome.
-/
set_option genInjectivity false
namespace RelationalPerimeter.Relativity.Production
open ConstitutiveSearch.Resources
open ConstitutiveSearch.ContinuationSignatures

inductive LocalReadout where
  | reading (value : Rational)
  | payload (value : Nat)
  | calibration (increment : Rational)
  | signal (record : SignalRecord)

def localReadout : (kind : Kind) → Value kind → LocalReadout
  | .reading, value => .reading value
  | .payload, value => .payload value
  | .calibration, value => .calibration value.increment
  | .signal, value => .signal value

inductive LocalEvent where
  | emitted (record : SignalRecord)
  | relayed (record : SignalRecord)
  | received (reading : Rational)
  | inspected (value : LocalReadout)
  | refused

def admittedNext (source : Cursor) : (request : LocalRequest) → LocalAdmission source request → Cursor
  | .emit _ _, admitted => source.extend (execute source.values (.emit admitted.1.ref admitted.2.ref))
  | .relay _ _, admitted => source.extend (execute source.values (.relay admitted.1.ref admitted.2.ref))
  | .receive _, admitted => source.extend (execute source.values (.receive admitted.ref))
  | .inspect _ _, _ => source

def admittedEvent (source : Cursor) : (request : LocalRequest) → LocalAdmission source request → LocalEvent
  | .emit _ _, admitted => .emitted ((Instruction.emit admitted.1.ref admitted.2.ref).interpret source.values)
  | .relay _ _, admitted => .relayed ((Instruction.relay admitted.1.ref admitted.2.ref).interpret source.values)
  | .receive _, admitted => .received ((Instruction.receive admitted.ref).interpret source.values)
  | .inspect kind _, admitted => .inspected (localReadout kind (source.read admitted.ref))

def referenceNext (source : Cursor) (request : LocalRequest) : Cursor :=
  match decideAdmission source request with
  | .inl admitted => admittedNext source request admitted
  | .inr _ => source

def referenceEvent (source : Cursor) (request : LocalRequest) : LocalEvent :=
  match decideAdmission source request with
  | .inl admitted => admittedEvent source request admitted
  | .inr _ => .refused

def localContract : FutureContract Cursor LocalRequest LocalEvent Unit where
  next := referenceNext
  event := referenceEvent
  read := fun _ => ()
  Allow := LocalAdmission
  decision := decideAdmission

theorem contract_enabled_exact (source : Cursor) (request : LocalRequest) :
    localContract.enabled source request = admissionEnabled source request := by
  dsimp only [FutureContract.enabled, admissionEnabled, localContract, FutureContract.decision]
  cases decideAdmission source request <;> rfl

theorem refused_cursor_unchanged (source : Cursor) (request : LocalRequest)
    (no : admissionEnabled source request = false) : referenceNext source request = source := by
  unfold referenceNext
  cases chosen : decideAdmission source request with
  | inl admitted => exact False.elim (refusal_refutes_admission source request no admitted)
  | inr _ => rfl

theorem refused_event_exact (source : Cursor) (request : LocalRequest)
    (no : admissionEnabled source request = false) : referenceEvent source request = .refused := by
  unfold referenceEvent
  cases chosen : decideAdmission source request with
  | inl admitted => exact False.elim (refusal_refutes_admission source request no admitted)
  | inr _ => rfl

theorem inspection_reference_exact (source : Cursor) {kind} (ref : Ref source.kinds kind) :
    referenceEvent source (.inspect kind ref.position) = .inspected (localReadout kind (source.read ref)) := by
  unfold referenceEvent
  cases chosen : decideAdmission source (.inspect kind ref.position) with
  | inl admitted =>
    dsimp only [admittedEvent]
    rw [reference_position_injective admitted.ref ref admitted.exactPosition]
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

theorem inspection_reference_enabled (source : Cursor) {kind} (ref : Ref source.kinds kind) :
    admissionEnabled source (.inspect kind ref.position) = true := by
  unfold admissionEnabled
  cases chosen : decideAdmission source (.inspect kind ref.position) with
  | inl _ => rfl
  | inr impossible => exact False.elim (impossible ⟨ref, rfl⟩)

def firstInspection : Outcome LocalEvent Unit → Option LocalReadout
  | .stop _ => none
  | .step _ _ (.inspected value) _ => some value
  | .step _ _ (.emitted _) _ => none
  | .step _ _ (.relayed _) _ => none
  | .step _ _ (.received _) _ => none
  | .step _ _ .refused _ => none

/-- Necessary readout agreement at a common typed address. This is not an
equality of the source occurrences or a complete memory-minimality result. -/
theorem futures_preserve_available_readout (source target : Cursor) {kind}
    (one : Ref source.kinds kind) (two : Ref target.kinds kind)
    (samePosition : two.position = one.position)
    (same : FutureEquivalent localContract source target) :
    localReadout kind (source.read one) = localReadout kind (target.read two) := by
  have observed := congrArg firstInspection (same [.inspect kind one.position])
  dsimp only [FutureContract.outcome, localContract] at observed
  rw [inspection_reference_exact source one, ← samePosition,
    inspection_reference_exact target two] at observed
  exact Option.some.inj observed

def LocalEvent.observedSignal : LocalEvent → Option SignalRecord
  | .emitted record => some record
  | .relayed record => some record
  | .received _ => none
  | .inspected (.reading _) => none
  | .inspected (.payload _) => none
  | .inspected (.calibration _) => none
  | .inspected (.signal record) => some record
  | .refused => none

end RelationalPerimeter.Relativity.Production
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Relativity.Production.localReadout
#print axioms RelationalPerimeter.Relativity.Production.admittedNext
#print axioms RelationalPerimeter.Relativity.Production.admittedEvent
#print axioms RelationalPerimeter.Relativity.Production.referenceNext
#print axioms RelationalPerimeter.Relativity.Production.referenceEvent
#print axioms RelationalPerimeter.Relativity.Production.localContract
#print axioms RelationalPerimeter.Relativity.Production.contract_enabled_exact
#print axioms RelationalPerimeter.Relativity.Production.refused_cursor_unchanged
#print axioms RelationalPerimeter.Relativity.Production.refused_event_exact
#print axioms RelationalPerimeter.Relativity.Production.inspection_reference_exact
#print axioms RelationalPerimeter.Relativity.Production.inspection_reference_enabled
#print axioms RelationalPerimeter.Relativity.Production.firstInspection
#print axioms RelationalPerimeter.Relativity.Production.futures_preserve_available_readout
#print axioms RelationalPerimeter.Relativity.Production.LocalEvent.observedSignal
/- AXIOM_AUDIT_END -/
