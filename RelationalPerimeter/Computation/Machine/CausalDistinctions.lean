import RelationalPerimeter.Computation.Machine.MemoryInvariant

/-! Complete behavioral characterization for the unchanged V2 future language.
The advance orbit is a specification, NOT a runtime archive or an executable
decision of equivalence of arbitrary live search states. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine
open EndogenousDecomposition ContinuationSignatures ConnectedFabric

def zeroSignals (count : Nat) : Signals := List.replicate count false

def decodeConnections (signals : Signals) : List Gate := signals.map Gate.mk

theorem gate_false_reads_configuration (gate : Gate) : gate.fire false = gate.invert := by
  cases gate with
  | mk invert => cases invert <;> rfl

theorem decode_calibration (gates : List Gate) :
    decodeConnections (fire gates (zeroSignals gates.length)) = gates := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change Gate.mk (gate.fire false) :: decodeConnections (fire rest (zeroSignals rest.length)) = _
      rw [gate_false_reads_configuration, ih]

theorem zero_length (count : Nat) : (zeroSignals count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ ih

theorem calibration_admitted (scope : Scope) :
    pulseFits scope (zeroSignals scope.length) (zeroSignals scope.length) = true := by
  unfold pulseFits
  rw [zero_length]
  change (decide (scope.length = scope.length) && decide (scope.length = scope.length)) = true
  rw [decide_eq_true (Eq.refl scope.length)]
  rfl

theorem futures_determine_connections (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : FutureEquivalent (runtimeContract scope) one two) : one.gates = two.gates := by
  have observed := (same.next ⟨.pulse (zeroSignals scope.length) (zeroSignals scope.length)⟩).read
  have outputs := congrArg (fun view : View => view.2.1) observed
  change (pulse scope one _ _).1.bank.read .transformed =
    (pulse scope two _ _).1.bank.read .transformed at outputs
  dsimp only [pulse] at outputs
  rw [calibration_admitted] at outputs
  change (drive one.gates _ _).read .transformed = (drive two.gates _ _).read .transformed at outputs
  rw [drive, drive, route_reads_transformed, route_reads_transformed] at outputs
  have decoded := congrArg decodeConnections outputs
  have readOne : decodeConnections (fire one.gates (zeroSignals scope.length)) = one.gates := by
    rw [← first.1]; exact decode_calibration one.gates
  have readTwo : decodeConnections (fire two.gates (zeroSignals scope.length)) = two.gates := by
    rw [← second.1]; exact decode_calibration two.gates
  exact readOne.symm.trans (decoded.trans readTwo)

def afterAdvances (scope : Scope) : Nat → Memory → Memory
  | 0, memory => memory
  | count + 1, memory => afterAdvances scope count (advance scope memory.live).1

def SnapshotAgreement (one two : Memory) : Prop :=
  one.view = two.view ∧ one.gates = two.gates

def CausalAgreement (scope : Scope) (one two : Memory) : Prop :=
  ∀ count, SnapshotAgreement (afterAdvances scope count one) (afterAdvances scope count two)

theorem advance_orbit_coherent (scope : Scope) (count : Nat) (memory : Memory)
    (coherent : Coherent scope memory) : Coherent scope (afterAdvances scope count memory) := by
  induction count generalizing memory with
  | zero => exact coherent
  | succ count ih => exact ih _ (install_coherent scope (LiveContinuation.produce memory.live))

theorem futures_after_advances (scope : Scope) (count : Nat) {one two : Memory}
    (same : FutureEquivalent (runtimeContract scope) one two) :
    FutureEquivalent (runtimeContract scope) (afterAdvances scope count one)
      (afterAdvances scope count two) := by
  induction count generalizing one two with
  | zero => exact same
  | succ count ih => exact ih (same.next ⟨.advance⟩)

theorem futures_imply_causal_agreement (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : FutureEquivalent (runtimeContract scope) one two) : CausalAgreement scope one two := by
  intro count
  have future := futures_after_advances scope count same
  exact ⟨future.read, futures_determine_connections scope
    (advance_orbit_coherent scope count one first)
    (advance_orbit_coherent scope count two second) future⟩

theorem orbit_ignores_current_storage (scope : Scope) (count : Nat)
    (one two : Memory) (same : one.live = two.live) :
    afterAdvances scope (count + 1) one = afterAdvances scope (count + 1) two := by
  change afterAdvances scope count (advance scope one.live).1 =
    afterAdvances scope count (advance scope two.live).1
  rw [same]

theorem pulse_snapshot (scope : Scope) {one two : Memory}
    (same : SnapshotAgreement one two) (left right : Signals) :
    SnapshotAgreement (pulse scope one left right).1 (pulse scope two left right).1 := by
  unfold pulse
  split
  · constructor
    · change (LiveContinuation.read one.live, _, _) = (LiveContinuation.read two.live, _, _)
      have liveRead : LiveContinuation.read one.live = LiveContinuation.read two.live :=
        congrArg Prod.fst same.1
      rw [same.2, liveRead]
    · exact same.2
  · exact same

theorem causal_agreement_next (scope : Scope) {one two : Memory}
    (same : CausalAgreement scope one two) (request : Request) :
    CausalAgreement scope (perform scope one request).1 (perform scope two request).1 := by
  cases request with
  | advance => intro count; exact same (count + 1)
  | sample inlet => exact same
  | pulse left right =>
      intro count
      cases count with
      | zero => exact pulse_snapshot scope (same 0) left right
      | succ count =>
          rw [orbit_ignores_current_storage scope count _ one (pulse_keeps_engine scope one left right),
            orbit_ignores_current_storage scope count _ two (pulse_keeps_engine scope two left right)]
          exact same (count + 1)

theorem snapshot_events (scope : Scope) {one two : Memory}
    (same : SnapshotAgreement one two) (request : Request) :
    (perform scope one request).2 = (perform scope two request).2 := by
  cases request with
  | advance => rfl
  | sample inlet =>
      cases inlet with
      | transformed => exact congrArg Event.sampled (congrArg (fun view : View => view.2.1) same.1)
      | retained => exact congrArg Event.sampled (congrArg (fun view : View => view.2.2) same.1)
  | pulse left right =>
      dsimp only [perform, pulse]
      split
      · rw [same.2]
      · rfl

theorem causal_agreement_implies_futures (scope : Scope) {one two : Memory}
    (same : CausalAgreement scope one two) : FutureEquivalent (runtimeContract scope) one two := by
  intro requests
  induction requests generalizing one two with
  | nil => exact congrArg Outcome.stop (same 0).1
  | cons request rest ih =>
      have read : (runtimeContract scope).read one = (runtimeContract scope).read two := (same 0).1
      have enabled : (runtimeContract scope).enabled one request =
          (runtimeContract scope).enabled two request := by
        unfold FutureContract.enabled
        dsimp only [runtimeContract]
        cases chosen : admission scope request.down <;> rfl
      have event : (runtimeContract scope).event one request =
          (runtimeContract scope).event two request := snapshot_events scope (same 0) request.down
      change Outcome.step ((runtimeContract scope).read one) _ _ _ =
        Outcome.step ((runtimeContract scope).read two) _ _ _
      rw [read, enabled, event]
      exact congrArg (Outcome.step _ _ _) (ih (causal_agreement_next scope same request.down))

theorem causal_agreement_iff_futures (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) :
    CausalAgreement scope one two ↔ FutureEquivalent (runtimeContract scope) one two :=
  ⟨causal_agreement_implies_futures scope,
    futures_imply_causal_agreement scope first second⟩

/-- Necessary in ANY exact realization, without observing the connection field. -/
theorem any_exact_realization_retains_connections (scope : Scope) {Other : Type 3}
    (realization : ExactRealization (runtimeContract scope) Other) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : realization.project one = realization.project two) : one.gates = two.gates :=
  futures_determine_connections scope first second (realization.equal_memory_same_futures same)

theorem any_exact_realization_retains_orbit (scope : Scope) {Other : Type 3}
    (realization : ExactRealization (runtimeContract scope) Other) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : realization.project one = realization.project two) : CausalAgreement scope one two :=
  futures_imply_causal_agreement scope first second (realization.equal_memory_same_futures same)

theorem unequal_connections_have_distinguishing_pulse (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) (different : one.gates ≠ two.gates) :
    (perform scope one (.pulse (zeroSignals scope.length) (zeroSignals scope.length))).1.bank.read .transformed ≠
      (perform scope two (.pulse (zeroSignals scope.length) (zeroSignals scope.length))).1.bank.read .transformed := by
  intro equal
  dsimp only [perform, pulse] at equal
  rw [calibration_admitted] at equal
  change (drive one.gates _ _).read .transformed = (drive two.gates _ _).read .transformed at equal
  rw [drive, drive, route_reads_transformed, route_reads_transformed] at equal
  have decoded := congrArg decodeConnections equal
  have readOne : decodeConnections (fire one.gates (zeroSignals scope.length)) = one.gates := by
    rw [← first.1]; exact decode_calibration one.gates
  have readTwo : decodeConnections (fire two.gates (zeroSignals scope.length)) = two.gates := by
    rw [← second.1]; exact decode_calibration two.gates
  exact different (readOne.symm.trans (decoded.trans readTwo))

end ConstitutiveSearch.ReconfigurableMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.unequal_connections_have_distinguishing_pulse
#print axioms ConstitutiveSearch.ReconfigurableMachine.decode_calibration
#print axioms ConstitutiveSearch.ReconfigurableMachine.futures_determine_connections
#print axioms ConstitutiveSearch.ReconfigurableMachine.advance_orbit_coherent
#print axioms ConstitutiveSearch.ReconfigurableMachine.futures_after_advances
#print axioms ConstitutiveSearch.ReconfigurableMachine.futures_imply_causal_agreement
#print axioms ConstitutiveSearch.ReconfigurableMachine.causal_agreement_next
#print axioms ConstitutiveSearch.ReconfigurableMachine.causal_agreement_implies_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.causal_agreement_iff_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.any_exact_realization_retains_connections
#print axioms ConstitutiveSearch.ReconfigurableMachine.any_exact_realization_retains_orbit
/- AXIOM_AUDIT_END -/
