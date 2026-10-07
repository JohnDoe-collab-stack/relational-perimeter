import RelationalPerimeter.Computation.Machine.ConstitutiveDiscovery
import RelationalPerimeter.Computation.Machine.ReducedLiveRunner
import RelationalPerimeter.Computation.Machine.ValidatedScheduleExecution

/-! R5 executable path. The older engine appears only in agreement proofs.
No new persistent data, callback or reader is added. Requests share one paired
production, including refusal followed by arbitrary remaining requests. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures
open EndogenousDecomposition.ValidatedScheduleExecution

private theorem enabledReduced_pulse_exact (scope : Scope) (left right : Signals) :
    enabledReduced scope ⟨.pulse left right⟩ = pulseFits scope left right := by
  unfold enabledReduced
  cases admission scope (.pulse left right) with
  | inl witness => exact witness.down.down.symm
  | inr impossible =>
      cases check : pulseFits scope left right with
      | false => rfl
      | true => exact False.elim (impossible ⟨⟨check⟩⟩)

def buildAction (front : Frontier) : LocalAction front :=
  let run := ConstitutiveDiscovery.discover front
  match found : run.outcome.discovered? with
  | none => False.elim (discovery_success front
      ((congrArg (fun result => result.outcome.discovered?)
        (ConstitutiveDiscovery.discovery_exact front)).symm.trans found))
  | some discovery =>
      let stored := run.outcome.produceStoredSchedule discovery found
      let validation := validateStoredSchedule stored
      let executed := (executeValidation validation).execution
      ⟨discovery,
        (congrArg (fun result => result.outcome.discovered?)
          (ConstitutiveDiscovery.discovery_exact front)).symm.trans found,
        validation.validated_exact ▸ executed⟩

private def actionFromRun (front : Frontier)
    (run : FeedbackDiscoveryFromDataRun front.depth front.generation.full front.provenance)
    (same : run = LiveReduction.discover front) : LocalAction front :=
  match found : run.outcome.discovered? with
  | none => False.elim (discovery_success front
      ((congrArg (fun result => result.outcome.discovered?) same).symm.trans found))
  | some discovery =>
      let stored := run.outcome.produceStoredSchedule discovery found
      let validation := validateStoredSchedule stored
      let executed := (executeValidation validation).execution
      ⟨discovery, (congrArg (fun result => result.outcome.discovered?) same).symm.trans found,
        validation.validated_exact ▸ executed⟩

private theorem actionFromRun_exact (front : Frontier)
    (run : FeedbackDiscoveryFromDataRun front.depth front.generation.full front.provenance)
    (same : run = LiveReduction.discover front) :
    actionFromRun front run same = LiveReduction.buildAction front := by
  cases same
  rfl

theorem buildAction_exact (front : Frontier) : buildAction front = LiveReduction.buildAction front :=
  actionFromRun_exact front _ (ConstitutiveDiscovery.discovery_exact front)

private def productionFromAction {scope : Scope} (live : Live scope)
    (action : LocalAction live.front) : Production live :=
  let connections := action.gates scope
  let output := fire connections live.values
  let decision : StructuralBranchDecision := ⟨action.selected, action.internalOutput⟩
  have length : output.length = scope.length :=
    (fired_length connections live.values
      ((scopeCode_length scope _ _).trans live.valuesLength.symm)).trans (scopeCode_length scope _ _)
  ⟨action, connections, rfl, output, rfl, decision, rfl,
    ⟨nextFront live.front action, output, length⟩, rfl, rfl⟩

def produce {scope : Scope} (live : Live scope) : Production live :=
  productionFromAction live (buildAction live.front)

theorem produce_exact {scope : Scope} (live : Live scope) : produce live = produceReduced live :=
  congrArg (productionFromAction live) (buildAction_exact live.front)

private def installProduction {scope : Scope} {live : Live scope}
    (production : Production live) : Runtime scope × Event :=
  let bank := route production.output production.output
  (⟨production.next, production.connections, bank, normal_route _ _⟩, .advanced)

/-- Consume a production already made by the authoritative live step. -/
def installProduced {scope : Scope} {live : Live scope}
    (production : Production live) : Runtime scope × Event := installProduction production

def advance {scope : Scope} (live : Live scope) : Runtime scope × Event :=
  installProduction (produce live)

theorem advance_exact {scope : Scope} (live : Live scope) : advance live = advanceReduced live := by
  exact congrArg installProduction (produce_exact live)

def perform {scope : Scope} (memory : Runtime scope) : Request → Runtime scope × Event
  | .advance => advance memory.live
  | .sample inlet => (memory, .sampled (memory.bank.read inlet))
  | .pulse left right => pulseReduced memory left right

theorem perform_exact {scope : Scope} (memory : Runtime scope) (request : Request) :
    perform memory request = performReduced memory request := by
  cases request with
  | advance => exact advance_exact memory.live
  | sample _ => rfl
  | pulse _ _ => rfl

def contract (scope : Scope) : FutureContract (Runtime scope) (ULift.{3} Request) Event View where
  next memory request := (perform memory request.down).1
  event memory request := (perform memory request.down).2
  read := readRuntime
  Allow _ request := Admitted scope request.down
  decision _ request := admission scope request.down

theorem enabled_exact {scope : Scope} (memory : Runtime scope) (request : ULift.{3} Request) :
    enabledReduced scope request = (contract scope).enabled memory request := by
  dsimp only [enabledReduced, FutureContract.enabled, contract]
  cases admission scope request.down <;> rfl

def realization (scope : Scope) : ExactRealization (runtimeContract scope) (Runtime scope) where
  reduced := contract scope
  project := projectMemory scope
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact memory request :=
    ((congrArg Prod.fst (perform_exact (projectMemory scope memory) request.down)).trans
      (perform_project scope memory request.down)).symm
  event_exact memory request :=
    ((congrArg Prod.snd (perform_exact (projectMemory scope memory) request.down)).trans
      (event_project scope memory request.down)).symm
  read_exact memory := (project_read scope memory).symm

def run {scope : Scope} : Runtime scope → List (ULift.{3} Request) → Outcome Event View
  | memory, [] => .stop (readRuntime memory)
  | memory, request :: rest =>
      let observation := readRuntime memory
      let allowed := enabledReduced scope request
      let transition := perform memory request.down
      .step observation allowed transition.2 (run transition.1 rest)

theorem run_exact {scope : Scope} (memory : Runtime scope) (requests : List (ULift.{3} Request)) :
    run memory requests = runReduced memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih =>
      change Outcome.step _ _ (perform memory request.down).2
        (run (perform memory request.down).1 rest) = _
      rw [perform_exact, ih]
      rfl

theorem run_contract_exact {scope : Scope} (memory : Runtime scope)
    (requests : List (ULift.{3} Request)) :
    run memory requests = (contract scope).outcome memory requests := by
  induction requests generalizing memory with
  | nil => rfl
  | cons request rest ih =>
      change Outcome.step _ _ _ (run _ rest) = Outcome.step _ _ _ _
      rw [ih, enabled_exact memory request]
      rfl

theorem all_sources_exact (scope : Scope) (memory : Memory)
    (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests = run (projectMemory scope memory) requests :=
  (executed_all_futures_exact scope memory requests).trans (run_exact _ requests).symm

theorem rich_sources_exact (scope : Scope) (frame : Frame)
    (requests : List (ULift.{3} Request)) :
    (sourceContract scope).outcome frame requests = run (projectMemory scope (project scope frame)) requests :=
  (executed_source_futures_exact scope frame requests).trans (run_exact _ requests).symm

theorem minimality (scope : Scope) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two) :
    projectMemory scope one = projectMemory scope two ↔
      ∀ requests, run (projectMemory scope one) requests = run (projectMemory scope two) requests := by
  constructor
  · intro same requests; exact congrArg (fun memory => run memory requests) same
  · intro same
    apply future_determines_projection scope first second
    intro requests
    exact (all_sources_exact scope one requests).trans
      ((same requests).trans (all_sources_exact scope two requests).symm)

theorem any_realization {scope : Scope} {Other : Type 3}
    (other : ExactRealization (runtimeContract scope) Other) {one two : Memory}
    (first : Coherent scope one) (second : Coherent scope two)
    (same : other.project one = other.project two) :
    projectMemory scope one = projectMemory scope two :=
  any_exact_realization_retains_projection scope other first second same

theorem refusal_continues {scope : Scope} (memory : Runtime scope) (left right : Signals)
    (wrong : pulseFits scope left right = false) (rest : List (ULift.{3} Request)) :
    run memory (⟨.pulse left right⟩ :: rest) =
      .step (readRuntime memory) false .refused (run memory rest) := by
  change Outcome.step _ _ (perform memory (.pulse left right)).2
    (run (perform memory (.pulse left right)).1 rest) = _
  rw [perform_exact, refusal_preserves_runtime memory left right wrong]
  have disabled : enabledReduced scope ⟨.pulse left right⟩ = false :=
    (enabledReduced_pulse_exact scope left right).trans wrong
  rw [disabled]

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.buildAction
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.buildAction_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.produce_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.advance
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.installProduced
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.advance_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.perform_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.contract
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.realization
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.run
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.run_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.run_contract_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.all_sources_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.rich_sources_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.minimality
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.any_realization
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.ConstitutiveExecution.refusal_continues
/- AXIOM_AUDIT_END -/
