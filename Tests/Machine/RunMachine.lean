import Tests.Machine.Checks
/-! NON-CONFIRMATORY development demonstration. No performance claim. -/
namespace ConstitutiveSearch.ReconfigurableMachine.Demo
open SAT EndogenousDecomposition ConnectedFabric

def refusedEvent : Event → Bool
  | .advanced => false
  | .sampled _ => false
  | .driven _ _ => false
  | .refused => true

def line (text : String) : IO Unit := do
  IO.print text
  IO.print "\n"

def showSignals : Signals → IO Unit
  | [] => IO.print "\n"
  | bit :: rest => do
      IO.print (if bit then "1 " else "0 ")
      showSignals rest

def requireSignals (actual expected : Signals) : IO Unit :=
  match signalsDecision actual expected with
  | .isTrue _ => pure ()
  | .isFalse _ => throw (IO.userError "unexpected signal/configuration vector")

def requireCells (memory : Memory) (expected : Nat) : IO Unit :=
  if memory.bank.cells == expected then pure ()
  else throw (IO.userError "unexpected number of signal buffers")

def showMemory (memory : Memory) : IO Unit := do
  line "connections (1=inversion, 0=direct)"
  showSignals (memory.gates.map Gate.invert)
  line "transformed inlet output"
  showSignals (memory.bank.read .transformed)
  line "retained inlet output"
  showSignals (memory.bank.read .retained)
  line "stored signal buffers"
  line (Nat.repr memory.bank.cells)
  line "live depth"
  line (Nat.repr memory.live.depth)

/-- Stream events as they happen; this observer holds no growing event list. -/
def stream (scope : Scope) : Memory → List Request → IO Unit
  | memory, [] => do
      line "final depth"
      line (Nat.repr memory.live.depth)
  | memory, request :: rest => do
      let head := perform scope memory request
      match head.2 with
      | .advanced => line "actual discovery advanced and reconfigured"
      | .sampled bits => do line "sample"; showSignals bits
      | .driven _ _ => line "pulse applied to installed connections"
      | .refused => line "malformed pulse refused"
      showMemory head.1
      stream scope head.1 rest

def main : IO Unit := do
  let master := UnifiedMaster.publicInstance 0
  let live := LiveContinuation.project master.cursor
  -- One real production, shared by configuration and the initial state.
  let production := LiveContinuation.produce live
  let selected := (causalStageOfThreadedStage production.built.run).selected
  let scope := [Channel.singleton selected, Channel.singleton (selected + 1)]
  let initial := install scope production
  line "NON-CONFIRMATORY SOFTWARE MACHINE DEMONSTRATION"
  line "first selected query"
  line (Nat.repr selected)
  requireSignals (initial.gates.map Gate.invert) [true, false]
  requireCells initial 1
  showMemory initial

  let joined := (perform scope initial (.pulse [false, false] [true, false])).1
  requireCells joined 1
  let split := (perform scope joined (.pulse [false, true] [false, false])).1
  requireCells split 2
  requireSignals (split.bank.read .transformed) [true, true]
  requireSignals (split.bank.read .retained) [false, false]
  line "VARIABLE_INPUT_AND_MEMORY_ORGANIZATION_OK"

  let refused := perform scope split (.pulse [] [true, false])
  if refusedEvent refused.2 then pure ()
  else throw (IO.userError "malformed pulse was not refused")
  requireSignals (refused.1.bank.read .transformed) [true, true]
  line "REFUSAL_PRESERVES_CURRENT_MEMORY_OK"

  let advanced := (perform scope split .advance).1
  requireSignals (advanced.gates.map Gate.invert) [false, false]
  let samePulse := (perform scope advanced (.pulse [false, false] [true, false])).1
  requireCells samePulse 2
  line "PUBLIC_SEARCH_RECONFIGURATION_CHANGES_THE_SAME_PULSE_OK"

  stream scope initial [.pulse [false, false] [true, false],
    .sample .transformed, .pulse [false, true] [false, false], .sample .retained,
    .pulse [] [true, false], .advance, .pulse [false, false] [true, false],
    .advance, .sample .transformed]
  let failed := attemptBank [Channel.singleton 0] 0 Checks.closedLeft Checks.closedLeft [false] [false]
  let found := attemptBank [Channel.singleton 0] 0 Checks.closedLeft Checks.closedRight [false] [true]
  if failed.cells == 2 && found.cells == 1 then
    line "REAL_RELATION_FINDER_FAILURE_AND_SUCCESS_OK"
  else throw (IO.userError "connection discovery control failed")

end ConstitutiveSearch.ReconfigurableMachine.Demo
def reconfigurableMachineDemo : IO Unit := ConstitutiveSearch.ReconfigurableMachine.Demo.main
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.line
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.refusedEvent
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.showSignals
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.requireSignals
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.requireCells
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.showMemory
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.stream
#print axioms ConstitutiveSearch.ReconfigurableMachine.Demo.main
#print axioms reconfigurableMachineDemo
/- AXIOM_AUDIT_END -/
