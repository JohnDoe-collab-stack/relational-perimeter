import RelationalPerimeter.Computation.Machine.LiveRoot

/-! NON-CONFIRMATORY fixed demonstration of the shared sequence entry point. -/
set_option genInjectivity false
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures

def requireSignals (actual expected : Signals) : IO Unit :=
  match signalsDecision actual expected with
  | .isTrue _ => pure ()
  | .isFalse _ => throw (IO.userError "unexpected shared-run signals")

def eventSignature : Event → Nat × Signals × Signals
  | .advanced => (0, [], [])
  | .sampled bits => (1, bits, [])
  | .driven left right => (2, left, right)
  | .refused => (3, [], [])

def checkTrace (trace : Outcome Event View) (expected : List (Bool × Event))
    (final : Signals) : IO Unit :=
  match expected with
  | [] => match trace with
    | .stop view => do
        requireSignals view.2.1 final
        requireSignals view.2.2 final
    | .step _ _ _ _ => throw (IO.userError "extra shared-run step")
  | (allowed, event) :: rest => match trace with
    | .stop _ => throw (IO.userError "missing shared-run step")
    | .step _ actualAllowed actualEvent tail => do
        if actualAllowed != allowed then throw (IO.userError "wrong admission")
        let actual := eventSignature actualEvent
        let expected := eventSignature event
        if actual.1 != expected.1 then throw (IO.userError "wrong event")
        requireSignals actual.2.1 expected.2.1
        requireSignals actual.2.2 expected.2.2
        checkTrace tail rest final
termination_by structural expected

def run : IO Unit := do
  let source := LiveContinuation.project (UnifiedMaster.publicInstance 0).cursor
  let query := stageSelectedVar (source.depth + 2)
  let scope := [Channel.singleton query, Channel.singleton query, Channel.singleton (query + 1)]
  -- Source installation is initialisation only, not a parallel runner.
  let installed := install scope (LiveContinuation.produce source)
  let initial := projectMemory scope installed
  let requests : List (ULift.{3} Request) := [⟨.advance⟩,
    ⟨.pulse [false, true, false] [true, false, false]⟩,
    ⟨.pulse [false, true, false] [false, false, false]⟩,
    ⟨.pulse [] [false, false, false]⟩, ⟨.advance⟩, ⟨.sample .transformed⟩]
  let result := runReduced initial requests
  checkTrace result [(true, .advanced),
    (true, .driven [true, false, false] [true, false, false]),
    (true, .driven [true, false, false] [false, false, false]),
    (false, .refused), (true, .advanced), (true, .sampled [true, true, true])]
    [true, true, true]
  let empty := runReduced (projectMemory [] installed)
    [⟨.advance⟩, ⟨.pulse [true] []⟩, ⟨.sample .retained⟩]
  checkTrace empty [(true, .advanced), (false, .refused), (true, .sampled [])] []
  IO.print "NON-CONFIRMATORY SHARED RUN: complete mixed trace, refusal continuation, repeated ports, empty scope OK\n"

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke
#eval ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke.run
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke.requireSignals
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke.eventSignature
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke.checkTrace
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.RunnerSmoke.run
/- AXIOM_AUDIT_END -/
