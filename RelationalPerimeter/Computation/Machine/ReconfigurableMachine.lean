import RelationalPerimeter.Computation.Machine.Fabric

/-! Software model of a reconfigurable two-inlet circuit bank.
Search produces the next wiring before the next engine step. Later pulses use
that wiring, not a saved assignment callback or a cached answer. Physical
fabrication and a bound on total engine work are not asserted here. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine
open SAT EndogenousDecomposition ContinuationSignatures ConnectedFabric

/-- Independent address-interpreting specification, not the configured evaluator. -/
def referenceAction (scope : Scope) (selected : Var) (bits : Signals) : Signals :=
  match scope with
  | [] => []
  | channel :: rest => match bits with
    | [] => []
    | bit :: tail =>
        (if channel.query = selected then !bit else bit) :: referenceAction rest selected tail
termination_by structural scope

theorem configured_action_exact (scope : Scope) (selected : Var) (bits : Signals) :
    fire (configure scope selected) bits = referenceAction scope selected bits := by
  induction scope generalizing bits with
  | nil => rfl
  | cons channel rest ih =>
      cases bits with
      | nil => rfl
      | cons bit tail =>
          have head : (configureGate selected channel.query).fire bit =
              (if channel.query = selected then !bit else bit) := by
            by_cases same : channel.query = selected
            · rw [configureGate, if_pos same, if_pos same]; rfl
            · rw [configureGate, if_neg same, if_neg same]; rfl
          change (configureGate selected channel.query).fire bit :: fire (configure rest selected) tail = _
          rw [head, ih]
          rfl

/-- Rich executed material for the current wiring; it is NOT a runtime field. -/
structure Frame : Type 3 where
  origin : LiveContinuation.Memory
  production : LiveContinuation.Production origin
  transformedInput : Signals
  retainedInput : Signals

def Frame.selected (frame : Frame) : Var :=
  (causalStageOfThreadedStage frame.production.built.run).selected

def Frame.targets (scope : Scope) (frame : Frame) : Signals × Signals :=
  (referenceAction scope frame.selected frame.transformedInput, frame.retainedInput)

/-- No history, source assignment, continuation callback or frame in runtime. -/
structure Memory : Type 3 where
  live : LiveContinuation.Memory
  gates : List Gate
  bank : Bank

def Memory.view (memory : Memory) :
    (Nat × List Var × Nat) × Signals × Signals :=
  (LiveContinuation.read memory.live,
    memory.bank.read .transformed, memory.bank.read .retained)

def project (scope : Scope) (frame : Frame) : Memory :=
  ⟨frame.production.next, compile scope frame.production,
    route (frame.targets scope).1 (frame.targets scope).2⟩

/-- Canonical sources come from the constituted role, not two supplied booleans. -/
def canonicalFrame (scope : Scope) (live : LiveContinuation.Memory)
    (production : LiveContinuation.Production live) : Frame :=
  ⟨live, production, sense scope production.decomposition.role.executedInput.1,
    sense scope production.decomposition.role.completedOutput.1⟩

def install (scope : Scope) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) : Memory :=
  let left := sense scope production.decomposition.role.executedInput.1
  let right := sense scope production.decomposition.role.completedOutput.1
  let gates := compile scope production
  ⟨production.next, gates, drive gates left right⟩

theorem install_exact (scope : Scope) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    install scope production = project scope (canonicalFrame scope live production) := by
  unfold install project canonicalFrame Frame.targets Frame.selected drive
  rw [← configured_action_exact]
  rfl

/-- Canonical convergence consumes the action equation of this executed license. -/
theorem canonical_targets_converge (scope : Scope) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    fire (compile scope production) (sense scope production.decomposition.role.executedInput.1) =
      sense scope production.decomposition.role.completedOutput.1 := by
  rw [compile_total_action]
  have actual : (compileRoleStageAtom production.decomposition.role).action
      production.decomposition.role.executedInput = production.decomposition.role.completedOutput := by
    exact producedRoleOutput_exact production.decomposition.license
      (roleConstitutedOccurrenceAt production.decomposition.role .left)
  exact congrArg (fun result => sense scope result.1) actual

theorem canonical_bank_shared (scope : Scope) {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) : (install scope production).bank.cells = 1 :=
  (drive_cells_iff _ _ _).mpr (canonical_targets_converge scope production)

/-- Acceptance does not follow from equality of observed signal banks. -/
def canonicalAccepted {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :=
  acceptedAction production production.decomposition.role.executedInput
    (production.decomposition.role.executedInputExact ▸
      (causalStageOfThreadedStage production.built.run).sourceAccepted)

theorem canonicalAccepted_output {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    (canonicalAccepted production).1 = production.decomposition.role.completedOutput := by
  exact producedRoleOutput_exact production.decomposition.license
    (roleConstitutedOccurrenceAt production.decomposition.role .left)

theorem canonical_occurrences_distinct {live : LiveContinuation.Memory}
    (production : LiveContinuation.Production live) :
    production.decomposition.license.transformedOccurrence ≠
      production.decomposition.license.retainedOccurrence :=
  production.decomposition.license.occurrencesRemainDistinct

inductive Request where
  | advance
  | sample (inlet : Inlet)
  | pulse (transformed retained : Signals)

inductive Event where
  | advanced
  | sampled (signals : Signals)
  | driven (transformed retained : Signals)
  | refused

def pulseFits (scope : Scope) (left right : Signals) : Bool :=
  (left.length == scope.length) && (right.length == scope.length)

/-- One search, then compilation, then routing, all before the next recursion. -/
def advance (scope : Scope) (live : LiveContinuation.Memory) : Memory × Event :=
  let production := LiveContinuation.produce live
  let memory := install scope production
  (memory, .advanced)

def pulse (scope : Scope) (memory : Memory) (left right : Signals) : Memory × Event :=
  if pulseFits scope left right then
    let bank := drive memory.gates left right
    (⟨memory.live, memory.gates, bank⟩,
      .driven (bank.read .transformed) (bank.read .retained))
  else (memory, .refused)

def perform (scope : Scope) (memory : Memory) : Request → Memory × Event
  | .advance => advance scope memory.live
  | .sample inlet => (memory, .sampled (memory.bank.read inlet))
  | .pulse left right => pulse scope memory left right

def referenceAdvance (scope : Scope) (live : LiveContinuation.Memory) : Frame × Event :=
  let production := LiveContinuation.produce live
  let frame := canonicalFrame scope live production
  (frame, .advanced)

def referencePerform (scope : Scope) (frame : Frame) : Request → Frame × Event
  | .advance => referenceAdvance scope frame.production.next
  | .sample inlet => (frame, .sampled ((project scope frame).bank.read inlet))
  | .pulse left right =>
      if pulseFits scope left right then
        let next := { frame with transformedInput := left, retainedInput := right }
        let bank := (project scope next).bank
        (next, .driven (bank.read .transformed) (bank.read .retained))
      else (frame, .refused)

theorem advance_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (project scope (referenceAdvance scope live).1, (referenceAdvance scope live).2) =
      advance scope live := by
  dsimp only [referenceAdvance, advance]
  rw [← install_exact]

theorem perform_exact (scope : Scope) (frame : Frame) (request : Request) :
    (project scope (referencePerform scope frame request).1,
      (referencePerform scope frame request).2) = perform scope (project scope frame) request := by
  cases request with
  | advance => exact advance_exact scope frame.production.next
  | sample inlet => rfl
  | pulse left right =>
      dsimp only [referencePerform, perform, pulse]
      split
      · unfold project Frame.targets drive compile
        rw [configured_action_exact]
        rfl
      · rfl

def execute (scope : Scope) : Memory → List Request → Memory × List Event
  | memory, [] => (memory, [])
  | memory, request :: rest =>
      let head := perform scope memory request
      let tail := execute scope head.1 rest
      (tail.1, head.2 :: tail.2)

def referenceExecute (scope : Scope) : Frame → List Request → Frame × List Event
  | frame, [] => (frame, [])
  | frame, request :: rest =>
      let head := referencePerform scope frame request
      let tail := referenceExecute scope head.1 rest
      (tail.1, head.2 :: tail.2)

theorem execute_exact (scope : Scope) (frame : Frame) (requests : List Request) :
    (project scope (referenceExecute scope frame requests).1,
      (referenceExecute scope frame requests).2) = execute scope (project scope frame) requests := by
  induction requests generalizing frame with
  | nil => rfl
  | cons request rest ih =>
      let head := referencePerform scope frame request
      have exactHead := perform_exact scope frame request
      have exactTail := ih head.1
      change (project scope (referenceExecute scope head.1 rest).1,
        head.2 :: (referenceExecute scope head.1 rest).2) = _
      have result := congrArg (fun pair : Memory × List Event => (pair.1, head.2 :: pair.2)) exactTail
      exact result.trans (by
        dsimp only [execute]
        rw [← congrArg Prod.fst exactHead, ← congrArg Prod.snd exactHead])

/-- A refusal is part of the contract, not silently missing from the outputs. -/
def Admitted (scope : Scope) : Request → Type 3
  | .advance => ULift.{3} Unit
  | .sample _ => ULift.{3} Unit
  | .pulse left right => ULift.{3} (PLift (pulseFits scope left right = true))

def admission (scope : Scope) (request : Request) :
    PSum (Admitted scope request) (Admitted scope request → False) := by
  cases request with
  | advance => exact .inl ⟨()⟩
  | sample _ => exact .inl ⟨()⟩
  | pulse left right =>
      cases check : pulseFits scope left right with
      | true => exact .inl ⟨⟨check⟩⟩
      | false => exact .inr (fun witness => Bool.noConfusion (check.symm.trans witness.down.down))

abbrev View := (Nat × List Var × Nat) × Signals × Signals

def sourceContract (scope : Scope) : FutureContract Frame (ULift.{3} Request) Event View where
  next frame request := (referencePerform scope frame request.down).1
  event frame request := (referencePerform scope frame request.down).2
  read frame := (project scope frame).view
  Allow _ request := Admitted scope request.down
  decision _ request := admission scope request.down

def runtimeContract (scope : Scope) : FutureContract Memory (ULift.{3} Request) Event View where
  next memory request := (perform scope memory request.down).1
  event memory request := (perform scope memory request.down).2
  read := Memory.view
  Allow _ request := Admitted scope request.down
  decision _ request := admission scope request.down

def realization (scope : Scope) : ExactRealization (sourceContract scope) Memory where
  reduced := runtimeContract scope
  project := project scope
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact frame request := congrArg Prod.fst (perform_exact scope frame request.down)
  event_exact frame request := congrArg Prod.snd (perform_exact scope frame request.down)
  read_exact _ := rfl

theorem all_futures_exact (scope : Scope) (frame : Frame) (requests : List (ULift.{3} Request)) :
    (sourceContract scope).outcome frame requests =
      (runtimeContract scope).outcome (project scope frame) requests :=
  (realization scope).outcome_exact frame requests

theorem same_realized_state_same_futures (scope : Scope) {one two : Frame}
    (same : project scope one = project scope two) : FutureEquivalent (sourceContract scope) one two :=
  (realization scope).equal_memory_same_futures same

theorem refusal_keeps_memory (scope : Scope) (memory : Memory) (left right : Signals)
    (wrong : pulseFits scope left right = false) :
    perform scope memory (.pulse left right) = (memory, .refused) := by
  dsimp only [perform, pulse]
  rw [wrong]
  rfl

theorem pulse_keeps_engine (scope : Scope) (memory : Memory) (left right : Signals) :
    (perform scope memory (.pulse left right)).1.live = memory.live := by
  dsimp only [perform, pulse]
  split <;> rfl

theorem pulse_keeps_connections (scope : Scope) (memory : Memory) (left right : Signals) :
    (perform scope memory (.pulse left right)).1.gates = memory.gates := by
  dsimp only [perform, pulse]
  split <;> rfl

theorem advance_uses_produced_successor (scope : Scope) (live : LiveContinuation.Memory) :
    (advance scope live).1.live = (LiveContinuation.produce live).next := rfl

theorem advance_uses_produced_connections (scope : Scope) (live : LiveContinuation.Memory) :
    (advance scope live).1.gates = compile scope (LiveContinuation.produce live) := rfl

def bootMaster {input : Nat} (scope : Scope) (master : UnifiedMaster.Instance input) : Memory × Event :=
  advance scope (LiveContinuation.project master.cursor)

end ConstitutiveSearch.ReconfigurableMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.referenceAction
#print axioms ConstitutiveSearch.ReconfigurableMachine.configured_action_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.install
#print axioms ConstitutiveSearch.ReconfigurableMachine.install_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.canonical_targets_converge
#print axioms ConstitutiveSearch.ReconfigurableMachine.canonical_bank_shared
#print axioms ConstitutiveSearch.ReconfigurableMachine.canonicalAccepted
#print axioms ConstitutiveSearch.ReconfigurableMachine.canonicalAccepted_output
#print axioms ConstitutiveSearch.ReconfigurableMachine.canonical_occurrences_distinct
#print axioms ConstitutiveSearch.ReconfigurableMachine.advance
#print axioms ConstitutiveSearch.ReconfigurableMachine.pulse
#print axioms ConstitutiveSearch.ReconfigurableMachine.perform_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.execute
#print axioms ConstitutiveSearch.ReconfigurableMachine.execute_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.admission
#print axioms ConstitutiveSearch.ReconfigurableMachine.realization
#print axioms ConstitutiveSearch.ReconfigurableMachine.all_futures_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.same_realized_state_same_futures
#print axioms ConstitutiveSearch.ReconfigurableMachine.refusal_keeps_memory
#print axioms ConstitutiveSearch.ReconfigurableMachine.pulse_keeps_engine
#print axioms ConstitutiveSearch.ReconfigurableMachine.pulse_keeps_connections
#print axioms ConstitutiveSearch.ReconfigurableMachine.advance_uses_produced_successor
#print axioms ConstitutiveSearch.ReconfigurableMachine.advance_uses_produced_connections
#print axioms ConstitutiveSearch.ReconfigurableMachine.bootMaster
/- AXIOM_AUDIT_END -/
