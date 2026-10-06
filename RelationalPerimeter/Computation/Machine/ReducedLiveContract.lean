import RelationalPerimeter.Computation.Machine.ReducedLiveExecution

/-! Exact realization of the unchanged V2 contract, including incoherent input
memories. Minimality will be stated separately on coherent memories. -/
set_option genInjectivity false
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.ReconfigurableMachine.LiveReduction
open SAT EndogenousDecomposition ConnectedFabric ContinuationSignatures

structure Runtime (scope : Scope) : Type 3 where
  live : Live scope
  gates : List Gate
  bank : Bank
  normal : BankNormal bank

def projectMemory (scope : Scope) (memory : Memory) : Runtime scope :=
  ⟨projectLive scope memory.live, memory.gates, normalizeBank memory.bank, normal_route _ _⟩

def readRuntime {scope : Scope} (memory : Runtime scope) : View :=
  ((memory.live.front.depth, memory.live.front.provenance, memory.live.front.searchSeed),
    memory.bank.read .transformed, memory.bank.read .retained)

def advanceReduced {scope : Scope} (live : Live scope) : Runtime scope × Event :=
  let production := produceReduced live
  let bank := route production.output production.output
  (⟨production.next, production.connections, bank, normal_route _ _⟩, .advanced)

def pulseReduced {scope : Scope} (memory : Runtime scope) (left right : Signals) : Runtime scope × Event :=
  if pulseFits scope left right then
    let bank := drive memory.gates left right
    (⟨memory.live, memory.gates, bank, normal_route _ _⟩,
      .driven (bank.read .transformed) (bank.read .retained))
  else (memory, .refused)

def performReduced {scope : Scope} (memory : Runtime scope) : Request → Runtime scope × Event
  | .advance => advanceReduced memory.live
  | .sample inlet => (memory, .sampled (memory.bank.read inlet))
  | .pulse left right => pulseReduced memory left right

theorem runtime_ext {scope : Scope} (one two : Runtime scope)
    (live : one.live = two.live) (gates : one.gates = two.gates) (bank : one.bank = two.bank) : one = two := by
  cases one; cases two; cases live; cases gates; cases bank; rfl

theorem project_read (scope : Scope) (memory : Memory) :
    readRuntime (projectMemory scope memory) = memory.view := by
  change (_, (normalizeBank memory.bank).read .transformed,
    (normalizeBank memory.bank).read .retained) = _
  rw [normalized_reads, normalized_reads]
  rfl

theorem advanced_bank_exact (scope : Scope) (live : LiveContinuation.Memory) :
    (advanceReduced (projectLive scope live)).1.bank =
      normalizeBank (install scope (LiveContinuation.produce live)).bank := by
  let production := LiveContinuation.produce live
  change route (produceReduced (projectLive scope live)).output _ = normalizeBank (drive _ _ _)
  rw [produced_values_exact]
  have right : sense scope production.built.stage.next.assignment =
      sense scope production.decomposition.role.completedOutput.1 := by
    rw [production.built.stage.nextAssignmentExact]
    rfl
  rw [right]
  change route _ _ = normalizeBank (route (fire (compile scope production)
    (sense scope production.decomposition.role.executedInput.1)) _)
  rw [canonical_targets_converge, normal_route]

theorem advance_project (scope : Scope) (live : LiveContinuation.Memory) :
    (advanceReduced (projectLive scope live)).1 = projectMemory scope (advance scope live).1 := by
  apply runtime_ext
  · exact produced_next_exact scope live
  · exact produced_connections_exact scope live
  · exact advanced_bank_exact scope live

theorem perform_project (scope : Scope) (memory : Memory) (request : Request) :
    (performReduced (projectMemory scope memory) request).1 =
      projectMemory scope (perform scope memory request).1 := by
  cases request with
  | advance => exact advance_project scope memory.live
  | sample _ => rfl
  | pulse left right =>
      dsimp only [performReduced, perform, pulseReduced, pulse]
      split
      · apply runtime_ext
        · rfl
        · rfl
        · exact (normal_route _ _).symm
      · rfl

theorem event_project (scope : Scope) (memory : Memory) (request : Request) :
    (performReduced (projectMemory scope memory) request).2 = (perform scope memory request).2 := by
  cases request with
  | advance => rfl
  | sample inlet => exact congrArg Event.sampled (normalized_reads memory.bank inlet)
  | pulse left right =>
      dsimp only [performReduced, perform, pulseReduced, pulse]
      split <;> rfl

def contract (scope : Scope) : FutureContract (Runtime scope) (ULift.{3} Request) Event View where
  next memory request := (performReduced memory request.down).1
  event memory request := (performReduced memory request.down).2
  read := readRuntime
  Allow _ request := Admitted scope request.down
  decision _ request := admission scope request.down

def liveReduction (scope : Scope) : ExactRealization (runtimeContract scope) (Runtime scope) where
  reduced := contract scope
  project := projectMemory scope
  forward _ _ witness := witness
  backward _ _ witness := witness
  backward_forward _ _ _ := rfl
  forward_backward _ _ _ := rfl
  next_exact memory request := (perform_project scope memory request.down).symm
  event_exact memory request := (event_project scope memory request.down).symm
  read_exact memory := (project_read scope memory).symm

theorem all_futures_exact (scope : Scope) (memory : Memory) (requests : List (ULift.{3} Request)) :
    (runtimeContract scope).outcome memory requests =
      (contract scope).outcome (projectMemory scope memory) requests :=
  (liveReduction scope).outcome_exact memory requests

theorem source_futures_exact (scope : Scope) (frame : Frame) (requests : List (ULift.{3} Request)) :
    (sourceContract scope).outcome frame requests =
      (contract scope).outcome (projectMemory scope (project scope frame)) requests :=
  (ReconfigurableMachine.all_futures_exact scope frame requests).trans (all_futures_exact scope _ requests)

theorem pulse_preserves_live {scope : Scope} (memory : Runtime scope) (left right : Signals) :
    (performReduced memory (.pulse left right)).1.live = memory.live := by
  dsimp only [performReduced, pulseReduced]
  split <;> rfl

theorem refusal_preserves_runtime {scope : Scope} (memory : Runtime scope) (left right : Signals)
    (wrong : pulseFits scope left right = false) : performReduced memory (.pulse left right) = (memory, .refused) := by
  dsimp only [performReduced, pulseReduced]
  rw [wrong]
  rfl

/-- The accessible domain is the actual projection image, not every inhabitant
of the structural runtime type. It is closed under all admitted or refused requests. -/
def Accessible {scope : Scope} (memory : Runtime scope) : Prop :=
  ∃ source : Memory, projectMemory scope source = memory

theorem projection_accessible (scope : Scope) (source : Memory) :
    Accessible (projectMemory scope source) := ⟨source, rfl⟩

theorem accessible_next {scope : Scope} {memory : Runtime scope}
    (accessible : Accessible memory) (request : Request) :
    Accessible (performReduced memory request).1 := by
  rcases accessible with ⟨source, exactSource⟩
  cases exactSource
  exact ⟨(perform scope source request).1, (perform_project scope source request).symm⟩

end ConstitutiveSearch.ReconfigurableMachine.LiveReduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.projectMemory
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.advanceReduced
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.project_read
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.advanced_bank_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.advance_project
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.perform_project
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.event_project
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.liveReduction
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.all_futures_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.source_futures_exact
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.pulse_preserves_live
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.refusal_preserves_runtime
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.projection_accessible
#print axioms ConstitutiveSearch.ReconfigurableMachine.LiveReduction.accessible_next
/- AXIOM_AUDIT_END -/
