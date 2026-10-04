import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution
import RelationalPerimeter.Constitution.Grouping.ContinuationContract

/-!
# Live continuation of the actual discovery engine

The retained state contains the assignment, generation, seed and provenance
which discovery really reads. It contains neither a resource support nor an
operational-prefix archive. Removing those archives is not, on its own, an
irreversible-forgetting theorem: canonical states may still reconstruct them.

Future requests are numbers of actual engine steps, exactly as in the existing
executor. This is not a claim about an additional interactive input language.
Every step discovers, applies and decomposes before forming the next state.
-/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.EndogenousDecomposition.LiveContinuation
open MasterResources ConstitutiveSearch.Grouping

structure Memory : Type 3 where
  depth : Nat
  assignment : SequentialAssignment depth
  state : ThreadedConstitutiveState depth assignment
  fresh : ThreadedStateFreshForNext state

def project (cursor : Cursor) : Memory :=
  ⟨cursor.depth, cursor.assignment, cursor.state, cursor.freshness⟩

/-- Only material of this executed head, without its old prefix object. -/
structure Production (memory : Memory) : Type 3 where
  built : ConstructedThreadedStageRun memory.state
  decomposition : ExecutedStageDecomposition (causalStageOfThreadedStage built.run)

def produce (memory : Memory) : Production memory :=
  let discovery := runThreadedNextDiscovery memory.state
  let built := buildFromExecutedDiscovery memory.state memory.fresh discovery rfl
  ⟨built, executedStageDecomposition (causalStageOfThreadedStage built.run)⟩

/-- Read the production already made by the historical resource executor. -/
def sourceProduction (cursor : Cursor) : Production (project cursor) :=
  ⟨⟨cursor.head.stage, cursor.head.run⟩, cursor.head.production.decomposition⟩

theorem production_exact (cursor : Cursor) :
    sourceProduction cursor = produce (project cursor) := rfl

def Production.next {memory : Memory} (production : Production memory) : Memory :=
  ⟨memory.depth + 1, production.built.stage.next,
    production.built.run.nextRun.next,
    production.built.run.nextRun.fresh memory.fresh⟩

def next (memory : Memory) : Memory := (produce memory).next

theorem next_exact (cursor : Cursor) :
    project cursor.next = next (project cursor) := rfl

/-- The event retains this production, not the historical prefix which led to it. -/
abbrev Event : Type 3 := (memory : Memory) × Production memory

def event (memory : Memory) : Event := ⟨memory, produce memory⟩
def sourceEvent (cursor : Cursor) : Event := ⟨project cursor, sourceProduction cursor⟩

theorem event_exact (cursor : Cursor) : sourceEvent cursor = event (project cursor) := rfl

def run : Nat → Memory → Memory
  | 0, memory => memory
  | count + 1, memory => run count (next memory)

def sourceRun : Nat → Cursor → Cursor
  | 0, cursor => cursor
  | count + 1, cursor => sourceRun count cursor.next

theorem run_exact (count : Nat) (cursor : Cursor) :
    project (sourceRun count cursor) = run count (project cursor) := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact (ih cursor.next).trans (congrArg (run count) (next_exact cursor))

def events : Nat → Memory → List Event
  | 0, _ => []
  | count + 1, memory =>
      let production := produce memory
      ⟨memory, production⟩ :: events count production.next

/-- Runtime entry: each production is shared by the event and its successor.
The separate run/events functions are specifications, not two runtime passes. -/
def execute : Nat → Memory → Memory × List Event
  | 0, memory => (memory, [])
  | count + 1, memory =>
      let production := produce memory
      let rest := execute count production.next
      (rest.1, ⟨memory, production⟩ :: rest.2)

theorem execute_state (count : Nat) (memory : Memory) :
    (execute count memory).1 = run count memory := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih => exact ih (produce memory).next

theorem execute_events (count : Nat) (memory : Memory) :
    (execute count memory).2 = events count memory := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons ⟨memory, produce memory⟩) (ih (produce memory).next)

def sourceEvents : Nat → Cursor → List Event
  | 0, _ => []
  | count + 1, cursor => sourceEvent cursor :: sourceEvents count cursor.next

theorem events_exact (count : Nat) (cursor : Cursor) :
    sourceEvents count cursor = events count (project cursor) := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih =>
      change sourceEvent cursor :: sourceEvents count cursor.next = _
      rw [event_exact, ih, next_exact]
      rfl

theorem sourceRun_is_resource_execution (count : Nat) (cursor : Cursor) :
    sourceRun count cursor = (MasterResources.execute count cursor).2 := by
  induction count generalizing cursor with
  | zero => rfl
  | succ count ih => exact ih cursor.next

def read (memory : Memory) : Nat × List SAT.Var × Nat :=
  (memory.depth, memory.state.provenance, memory.state.searchSeed)

/-- All requests remain admissible: freshness is maintained by actual steps. -/
def contract : Continuation.Exact Cursor Memory Nat (List Event) (Nat × List SAT.Var × Nat) where
  project := project
  sourceNext := fun cursor count => sourceRun count cursor
  reducedNext := fun memory count => run count memory
  sourceAllow := fun _ _ => ULift.{3} Unit
  reducedAllow := fun _ _ => ULift.{3} Unit
  toReduced := fun _ _ witness => witness
  toSource := fun _ _ witness => witness
  sourceEvent := fun cursor count => sourceEvents count cursor
  reducedEvent := fun memory count => events count memory
  sourceRead := fun cursor => read (project cursor)
  reducedRead := read
  nextLaw := fun cursor count => run_exact count cursor
  eventLaw := fun cursor count => events_exact count cursor
  readLaw := fun _ => rfl

theorem all_future_requests (cursor : Cursor) (requests : List Nat) :
    project (Continuation.run contract.sourceNext cursor requests) =
      Continuation.run contract.reducedNext (project cursor) requests :=
  contract.run_exact cursor requests

theorem all_future_events (cursor : Cursor) (requests : List Nat) :
    Continuation.events contract.sourceNext contract.sourceEvent cursor requests =
      Continuation.events contract.reducedNext contract.reducedEvent (project cursor) requests :=
  contract.events_exact cursor requests

theorem all_future_reads (cursor : Cursor) (requests : List Nat) :
    Continuation.observations contract.sourceNext contract.sourceRead cursor requests =
      Continuation.observations contract.reducedNext contract.reducedRead (project cursor) requests :=
  contract.observations_exact cursor requests

end ConstitutiveSearch.EndogenousDecomposition.LiveContinuation
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.produce
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.production_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.next_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.run
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.run_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.events_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.execute
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.execute_state
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.execute_events
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.sourceRun_is_resource_execution
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.contract
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.all_future_requests
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.all_future_events
#print axioms ConstitutiveSearch.EndogenousDecomposition.LiveContinuation.all_future_reads
/- AXIOM_AUDIT_END -/
