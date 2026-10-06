import RelationalPerimeter.Computation.Machine.LiveRoot

/-! NON-CONFIRMATORY executable demonstration, not a cost experiment. -/
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Smoke
open SAT EndogenousDecomposition ConnectedFabric

def requireSignals (actual expected : Signals) : IO Unit :=
  match signalsDecision actual expected with
  | .isTrue _ => pure ()
  | .isFalse _ => throw (IO.userError "unexpected reduced live signals")

def run : IO Unit := do
  let source := LiveContinuation.project (UnifiedMaster.publicInstance 0).cursor
  let query := stageSelectedVar (source.depth + 2)
  let scope := [Channel.singleton query, Channel.singleton query, Channel.singleton (query + 1)]
  -- Rich construction is used once to obtain the received source state.
  let installed := install scope (LiveContinuation.produce source)
  let initial := projectMemory scope installed
  let first := (performReduced initial .advance).1
  requireSignals (first.gates.map Gate.invert) [true, true, false]
  requireSignals first.live.values [true, true, true]
  let joined := (performReduced first (.pulse [false, true, false] [true, false, false])).1
  if joined.bank.cells != 1 then throw (IO.userError "expected shared pulse bank")
  let separated := (performReduced joined (.pulse [false, true, false] [false, false, false])).1
  if separated.bank.cells != 2 then throw (IO.userError "expected distinct pulse outputs")
  let refused := performReduced separated (.pulse [] [false, false, false])
  match refused.2 with
  | .refused => pure ()
  | .advanced => throw (IO.userError "invalid pulse advanced")
  | .sampled _ => throw (IO.userError "invalid pulse sampled")
  | .driven _ _ => throw (IO.userError "invalid pulse was driven")
  requireSignals refused.1.live.values [true, true, true]
  let second := (performReduced refused.1 .advance).1
  requireSignals (second.gates.map Gate.invert) [false, false, false]
  requireSignals second.live.values [true, true, true]
  let sampled := performReduced second (.sample .transformed)
  match sampled.2 with
  | .sampled bits => requireSignals bits [true, true, true]
  | .advanced => throw (IO.userError "sample advanced")
  | .driven _ _ => throw (IO.userError "sample was driven")
  | .refused => throw (IO.userError "sample refused")
  IO.print "NON-CONFIRMATORY V4 SMOKE: actual discovery, repeated ports, pulse separation, refusal, two reduced advances, sample OK"
  IO.print "\n"

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Smoke
#eval ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Smoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Smoke.requireSignals
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.Smoke.run
/- AXIOM_AUDIT_END -/
