import RelationalPerimeter.Computation.Machine.MasterRuntime

/-! Full interleavings of the core requests and configured SAT routing. The
source contract is fixed on rich memory before projection. Its SAT contexts
are retained verbatim: this is not a new minimality claim about SAT search.
`run` is the executable entry; the split next/event contract is a specification. -/
set_option genInjectivity false
set_option autoImplicit false
namespace ConstitutiveSearch.MasterMachine
open SAT ConnectedFabric ContinuationSignatures

inductive Request where
  | core (request : ReconfigurableMachine.Request)
  | route (slot : Nat) (bits : Signals)
  | sampleProblem

inductive Event where
  | core (event : ReconfigurableMachine.Event)
  | routed (slot : Nat) (bits : Signals)
  | sampledProblem (value : Option (Nat × Signals))
  | refused

abbrev View := ReconfigurableMachine.View × Nat × Option (Nat × Signals)

def routeFits {formula : Cnf} (scope : Scope) (problem : ProblemMemory formula) (slot : Nat) (bits : Signals) : Bool :=
  (slot < problem.routing.sourceWidth) && (bits.length == scope.length)

def routeProblem {formula : Cnf} (scope : Scope) (problem : ProblemMemory formula)
    (slot : Nat) (bits : Signals) : ProblemMemory formula × Event :=
  if routeFits scope problem slot bits then
    match problem.routing.apply slot bits with
    | none => (problem, .refused)
    | some output => ({ problem with routed := some output }, .routed output.1 output.2)
  else (problem, .refused)

def perform {scope : Scope} {formula : Cnf} (memory : Memory scope formula) :
    Request → Memory scope formula × Event
  | .core .advance => (advance memory, .core .advanced)
  | .core (.sample inlet) =>
      let transition := ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform memory.core (.sample inlet)
      (⟨transition.1, memory.problem⟩, .core transition.2)
  | .core (.pulse left right) =>
      let transition := ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform memory.core (.pulse left right)
      (⟨transition.1, memory.problem⟩, .core transition.2)
  | .route slot bits =>
      let transition := routeProblem scope memory.problem slot bits
      (⟨memory.core, transition.1⟩, transition.2)
  | .sampleProblem => (memory, .sampledProblem memory.problem.routed)

def richPerform {formula : Cnf} (scope : Scope) (memory : RichMemory formula) :
    Request → RichMemory formula × Event
  | .core .advance => (richAdvance scope memory, .core .advanced)
  | .core (.sample inlet) =>
      let transition := ReconfigurableMachine.perform scope memory.core (.sample inlet)
      (⟨transition.1, memory.problem⟩, .core transition.2)
  | .core (.pulse left right) =>
      let transition := ReconfigurableMachine.perform scope memory.core (.pulse left right)
      (⟨transition.1, memory.problem⟩, .core transition.2)
  | .route slot bits =>
      let transition := routeProblem scope memory.problem slot bits
      (⟨memory.core, transition.1⟩, transition.2)
  | .sampleProblem => (memory, .sampledProblem memory.problem.routed)

def read {scope : Scope} {formula : Cnf} (memory : Memory scope formula) : View :=
  (ReconfigurableMachine.LiveReduction.readRuntime memory.core,
    memory.problem.frontier.length, memory.problem.routed)

def richRead {formula : Cnf} (memory : RichMemory formula) : View :=
  (memory.core.view, memory.problem.frontier.length, memory.problem.routed)

def Admitted {formula : Cnf} (scope : Scope) (problem : ProblemMemory formula) : Request → Type 3
  | .core request => ReconfigurableMachine.Admitted scope request
  | .route slot bits => ULift.{3} (PLift (routeFits scope problem slot bits = true))
  | .sampleProblem => ULift.{3} Unit

def admission {formula : Cnf} (scope : Scope) (problem : ProblemMemory formula) (request : Request) :
    PSum (Admitted scope problem request) (Admitted scope problem request → False) := by
  cases request with
  | core request => exact ReconfigurableMachine.admission scope request
  | sampleProblem => exact .inl ⟨()⟩
  | route slot bits =>
      cases check : routeFits scope problem slot bits with
      | true => exact .inl ⟨⟨check⟩⟩
      | false => exact .inr (fun witness => Bool.noConfusion (check.symm.trans witness.down.down))

def contract (scope : Scope) (formula : Cnf) :
    FutureContract (Memory scope formula) (ULift.{3} Request) Event View where
  next memory request := (perform memory request.down).1
  event memory request := (perform memory request.down).2
  read := read
  Allow memory request := Admitted scope memory.problem request.down
  decision memory request := admission scope memory.problem request.down

def richContract (scope : Scope) (formula : Cnf) :
    FutureContract (RichMemory formula) (ULift.{3} Request) Event View where
  next memory request := (richPerform scope memory request.down).1
  event memory request := (richPerform scope memory request.down).2
  read := richRead
  Allow memory request := Admitted scope memory.problem request.down
  decision memory request := admission scope memory.problem request.down

theorem perform_project (scope : Scope) {formula : Cnf} (source : RichMemory formula) (request : Request) :
    perform (project scope source) request =
      (project scope (richPerform scope source request).1, (richPerform scope source request).2) := by
  cases request with
  | core request =>
      cases request with
      | advance => exact congrArg (fun memory => (memory, Event.core .advanced)) (advance_exact scope source)
      | sample inlet =>
          apply Prod.ext
          · rfl
          · exact congrArg Event.core
              ((congrArg Prod.snd (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform_exact
                (ReconfigurableMachine.LiveReduction.projectMemory scope source.core) (.sample inlet))).trans
                (ReconfigurableMachine.LiveReduction.event_project scope source.core (.sample inlet)))
      | pulse left right =>
          apply Prod.ext
          · apply memory_ext
            · exact ((congrArg Prod.fst
                (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform_exact
                  (ReconfigurableMachine.LiveReduction.projectMemory scope source.core) (.pulse left right))).trans
                (ReconfigurableMachine.LiveReduction.perform_project scope source.core (.pulse left right)))
            · rfl
          · exact congrArg Event.core
              ((congrArg Prod.snd (ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform_exact
                (ReconfigurableMachine.LiveReduction.projectMemory scope source.core) (.pulse left right))).trans
                (ReconfigurableMachine.LiveReduction.event_project scope source.core (.pulse left right)))
  | route slot bits => rfl
  | sampleProblem => rfl

def realization (scope : Scope) (formula : Cnf) :
    ExactRealization (richContract scope formula) (Memory scope formula) where
  reduced := contract scope formula
  project := project scope
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact source request := (congrArg Prod.fst (perform_project scope source request.down)).symm
  event_exact source request := (congrArg Prod.snd (perform_project scope source request.down)).symm
  read_exact source := by
    change (source.core.view, source.problem.frontier.length, source.problem.routed) =
      (ReconfigurableMachine.LiveReduction.readRuntime
        (ReconfigurableMachine.LiveReduction.projectMemory scope source.core),
        source.problem.frontier.length, source.problem.routed)
    rw [ReconfigurableMachine.LiveReduction.project_read]

def enabled {formula : Cnf} (scope : Scope) (problem : ProblemMemory formula)
    (request : Request) : Bool :=
  match admission scope problem request with
  | .inl _ => true
  | .inr _ => false

theorem enabled_exact {scope : Scope} {formula : Cnf} (memory : Memory scope formula)
    (request : ULift.{3} Request) :
    enabled scope memory.problem request.down = (contract scope formula).enabled memory request := by
  dsimp only [enabled, FutureContract.enabled, contract]
  cases admission scope memory.problem request.down <;> rfl

/-- One paired transition per request; no construction of specification callbacks. -/
def run {scope : Scope} {formula : Cnf} :
    Memory scope formula → List (ULift.{3} Request) → Outcome Event View
  | memory, [] => .stop (read memory)
  | memory, request :: rest =>
      let allowed := enabled scope memory.problem request.down
      let transition := perform memory request.down
      .step (read memory) allowed transition.2 (run transition.1 rest)

theorem run_exact {scope : Scope} {formula : Cnf} (memory : Memory scope formula)
    (requests : List (ULift.{3} Request)) : run memory requests = (contract scope formula).outcome memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih =>
      change Outcome.step _ _ _ (run _ rest) = _
      rw [ih, enabled_exact memory request]
      rfl

theorem all_futures_exact (scope : Scope) {formula : Cnf} (source : RichMemory formula)
    (requests : List (ULift.{3} Request)) :
    (richContract scope formula).outcome source requests = run (project scope source) requests :=
  ((realization scope formula).outcome_exact source requests).trans (run_exact _ requests).symm

theorem run_shared_transition {scope : Scope} {formula : Cnf} (memory : Memory scope formula)
    (request : ULift.{3} Request) (rest : List (ULift.{3} Request)) :
    run memory (request :: rest) =
      let transition := perform memory request.down
      .step (read memory) ((contract scope formula).enabled memory request) transition.2
        (run transition.1 rest) := by
  change Outcome.step _ _ _ _ = Outcome.step _ _ _ _
  rw [enabled_exact memory request]

end ConstitutiveSearch.MasterMachine
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.MasterMachine.perform
#print axioms ConstitutiveSearch.MasterMachine.richPerform
#print axioms ConstitutiveSearch.MasterMachine.perform_project
#print axioms ConstitutiveSearch.MasterMachine.realization
#print axioms ConstitutiveSearch.MasterMachine.enabled
#print axioms ConstitutiveSearch.MasterMachine.enabled_exact
#print axioms ConstitutiveSearch.MasterMachine.run
#print axioms ConstitutiveSearch.MasterMachine.run_exact
#print axioms ConstitutiveSearch.MasterMachine.all_futures_exact
#print axioms ConstitutiveSearch.MasterMachine.run_shared_transition
/- AXIOM_AUDIT_END -/
