import RelationalPerimeter.Computation.Machine.ReducedLiveMinimality

/-! Shared executable evaluation. The generic contract remains a specification;
each nonempty execution step consumes one paired transition, never its two
specification callbacks. The returned observation trace is not persistent memory. -/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open ConnectedFabric ContinuationSignatures

def enabledReduced (scope : Scope) (request : ULift.{3} Request) : Bool :=
  match admission scope request.down with
  | .inl _ => true
  | .inr _ => false

theorem enabledReduced_exact {scope : Scope} (memory : Runtime scope)
    (request : ULift.{3} Request) :
    enabledReduced scope request = (contract scope).enabled memory request := by
  dsimp only [enabledReduced, FutureContract.enabled, contract]
  cases admission scope request.down <;> rfl

def runReduced {scope : Scope} : Runtime scope → List (ULift.{3} Request) → Outcome Event View
  | memory, [] => .stop (readRuntime memory)
  | memory, request :: rest =>
      let observation := readRuntime memory
      let allowed := enabledReduced scope request
      let transition := performReduced memory request.down
      .step observation allowed transition.2 (runReduced transition.1 rest)

theorem runReduced_nil {scope : Scope} (memory : Runtime scope) :
    runReduced memory [] = .stop (readRuntime memory) := rfl

theorem runReduced_cons {scope : Scope} (memory : Runtime scope)
    (request : ULift.{3} Request) (rest : List (ULift.{3} Request)) :
    runReduced memory (request :: rest) =
      .step (readRuntime memory) (enabledReduced scope request)
        (performReduced memory request.down).2
        (runReduced (performReduced memory request.down).1 rest) := rfl

theorem runReduced_exact_outcome {scope : Scope} (memory : Runtime scope)
    (requests : List (ULift.{3} Request)) :
    runReduced memory requests = (contract scope).outcome memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih =>
      change Outcome.step _ _ _ (runReduced _ rest) = Outcome.step _ _ _ _
      rw [ih, enabledReduced_exact memory request]
      rfl

theorem executed_all_futures_exact (scope : Scope) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests =
      runReduced (projectMemory scope memory) requests :=
  (all_futures_exact scope memory requests).trans (runReduced_exact_outcome _ requests).symm

theorem executed_source_futures_exact (scope : Scope) (frame : Frame)
    (requests : List (ULift.{3} Request)) :
    (sourceContract scope).outcome frame requests =
      runReduced (projectMemory scope (project scope frame)) requests :=
  (source_futures_exact scope frame requests).trans (runReduced_exact_outcome _ requests).symm

theorem minimal_projection_iff_executed_futures (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) :
    projectMemory scope one = projectMemory scope two ↔
      ∀ requests, runReduced (projectMemory scope one) requests =
        runReduced (projectMemory scope two) requests := by
  constructor
  · intro same requests
    exact congrArg (fun memory => runReduced memory requests) same
  · intro same
    apply future_determines_projection scope first second
    intro requests
    exact (executed_all_futures_exact scope one requests).trans
      ((same requests).trans (executed_all_futures_exact scope two requests).symm)

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.enabledReduced
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.enabledReduced_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_nil
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_cons
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.runReduced_exact_outcome
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.executed_all_futures_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.executed_source_futures_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.minimal_projection_iff_executed_futures
/- AXIOM_AUDIT_END -/
