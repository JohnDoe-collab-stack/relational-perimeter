import Tests.LocalAlignment.DocumentaryMaster

/-! Finite composition of the documentary master bridge. Received demands remain
independent of permissions and execution. Each actual master result supplies both
the successor cursor and the dossier memory for the next step. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Dossier
open Resources EndogenousDecomposition

structure Obligation (context : List SourceKey) where
  demand : Demand
  left : Location context
  right : Location context

def demands {context} (tasks : List (Obligation context)) : List Demand :=
  tasks.map Obligation.demand

def selectGoal {received items demand} (goal : Goal received items)
    (selected : Ref received demand) : Goal [demand] items :=
  match goal, selected with
  | .cons _ item located meets _, .here => .cons demand item located meets (.nil _)
  | .cons _ _ _ _ tail, .prior old => selectGoal tail old

theorem forbidden_list_incompatible {context sources contract received demand}
    (memory : @Memory context sources contract) (selected : Ref received demand)
    (position : Nat) (pinned : demand.origin = some position)
    (absent : resolvePermission contract.allowed position = none) :
    Goal received memory.items → False :=
  fun goal => forbidden_origin_incompatible demand position pinned absent memory (selectGoal goal selected)

/-- Admissibility supplies received references and their permissions. It supplies
neither a produced element nor an assignment or an execution certificate. -/
inductive PairAdmissible {context} (sources : Support SourceValue context)
    (contract : Contract) (task : Obligation context) where
  | left (permission : Ref contract.allowed task.left.2.position)
      (meets : Meets task.demand (sourceCitation sources task.left))
  | right (permission : Ref contract.allowed task.right.2.position)
      (meets : Meets task.demand (sourceCitation sources task.right))

inductive TaskAdmissible {context} (sources : Support SourceValue context)
    (contract : Contract) : List (Obligation context) → Type where
  | nil : TaskAdmissible sources contract []
  | cons {task rest} (head : PairAdmissible sources contract task)
      (tail : TaskAdmissible sources contract rest) :
      TaskAdmissible sources contract (task :: rest)

structure State {context} (sources : Support SourceValue context) (contract : Contract) where
  cursor : MasterResources.Cursor
  memory : Memory sources contract

abbrev Step {context sources contract} (state : @State context sources contract)
    (task : Obligation context) :=
  (stage : Master.Stage state.cursor sources contract task.demand task.left task.right) ×
    Master.Decision stage state.memory

def step {context sources contract} (state : @State context sources contract)
    (task : Obligation context) : Step state task :=
  Master.run state.cursor sources contract task.demand task.left task.right state.memory

def Step.next {context sources contract state task}
    (produced : @Step context sources contract state task) : State sources contract :=
  ⟨produced.1.next, produced.2.result.1⟩

def Step.added {context sources contract state task}
    (produced : @Step context sources contract state task) : Nat :=
  match produced.2 with
  | .complete _ => 1
  | .blocked _ _ => 0

theorem Step.depth {context sources contract state task}
    (produced : @Step context sources contract state task) :
    produced.next.cursor.depth = state.cursor.depth + 1 :=
  congrArg MasterResources.Boundary.depth produced.1.next_exact

theorem Step.items {context sources contract state task}
    (produced : @Step context sources contract state task) :
    produced.next.memory.items.length = state.memory.items.length + produced.added := by
  rcases produced with ⟨stage, decision⟩
  cases decision with
  | blocked _ _ => exact (Nat.add_zero _).symm
  | complete packet =>
      change packet.result.1.items.length = state.memory.items.length + 1
      rw [packet.items_exact]
      rfl

def incorporationReference {context sources contract}
    (memory : @Memory context sources contract) (output : Output sources contract)
    (result : Memory sources contract × Citation) (actual : result = incorporate memory output)
    {item} (old : Ref memory.items item) : Ref result.1.items item := by
  cases actual
  exact .prior old

theorem incorporationReference_position {context sources contract}
    (memory : @Memory context sources contract) (output : Output sources contract)
    (result : Memory sources contract × Citation) (actual : result = incorporate memory output)
    {item} (old : Ref memory.items item) :
    (incorporationReference memory output result actual old).position = 1 + old.position := by
  cases actual
  exact Nat.add_comm _ _

theorem incorporationReference_evidence {context sources contract}
    (memory : @Memory context sources contract) (output : Output sources contract)
    (result : Memory sources contract × Citation) (actual : result = incorporate memory output)
    {item} (old : Ref memory.items item) :
    result.1.valid (incorporationReference memory output result actual old) = memory.valid old := by
  cases actual
  rfl

/-- Old dossier references are transported through the actual incorporation.
Their indexed item is unchanged, even when another occurrence has equal value. -/
def Step.previous {context sources contract state task}
    (produced : @Step context sources contract state task) {item} :
    Ref state.memory.items item → Ref produced.next.memory.items item := by
  rcases produced with ⟨stage, decision⟩
  cases decision with
  | blocked _ _ => exact fun old => old
  | complete packet =>
      change Ref state.memory.items item → Ref packet.result.1.items item
      exact incorporationReference state.memory packet.output packet.result packet.resultExact

theorem Step.previous_position {context sources contract state task}
    (produced : @Step context sources contract state task) {item}
    (old : Ref state.memory.items item) :
    (produced.previous old).position = produced.added + old.position := by
  rcases produced with ⟨stage, decision⟩
  cases decision with
  | blocked _ _ => exact (Nat.zero_add _).symm
  | complete packet =>
      exact incorporationReference_position state.memory packet.output packet.result packet.resultExact old

theorem Step.previous_evidence {context sources contract state task}
    (produced : @Step context sources contract state task) {item}
    (old : Ref state.memory.items item) :
    produced.next.memory.valid (produced.previous old) = state.memory.valid old := by
  rcases produced with ⟨stage, decision⟩
  cases decision with
  | blocked _ _ => rfl
  | complete packet =>
      exact incorporationReference_evidence state.memory packet.output packet.result packet.resultExact old

/-- A trace retains the actual shared packets. Equality with the producer is
required at each step; the tail starts from that packet's own next state. -/
inductive Execution {context} {sources : Support SourceValue context} {contract : Contract} :
    State sources contract → List (Obligation context) → State sources contract → Type 3 where
  | nil {start} : Execution start [] start
  | cons {start task rest finish} (produced : Step start task)
      (actual : produced = step start task)
      (tail : Execution produced.next rest finish) :
      Execution start (task :: rest) finish

def execute {context sources contract} (start : @State context sources contract) :
    (tasks : List (Obligation context)) →
      (finish : State sources contract) × Execution start tasks finish
  | [] => ⟨start, .nil⟩
  | task :: rest =>
      let produced := step start task
      let tail := execute produced.next rest
      ⟨tail.1, .cons produced rfl tail.2⟩

theorem execute_append {context sources contract} (start : @State context sources contract)
    (before after : List (Obligation context)) :
    (execute start (before ++ after)).1 = (execute (execute start before).1 after).1 := by
  induction before generalizing start with
  | nil => rfl
  | cons task rest ih => exact ih (step start task).next

def Execution.added {context sources contract start tasks finish} :
    @Execution context sources contract start tasks finish → Nat
  | .nil => 0
  | .cons produced _ tail => produced.added + tail.added

def Execution.events {context sources contract start tasks finish} :
    @Execution context sources contract start tasks finish → List (Option Citation)
  | .nil => []
  | .cons produced _ tail => produced.2.result.2 :: tail.events

theorem Execution.events_length {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) :
    executed.events.length = tasks.length := by
  induction executed with
  | nil => rfl
  | cons produced actual tail ih => exact congrArg Nat.succ ih

theorem execute_append_events {context sources contract} (start : @State context sources contract)
    (before after : List (Obligation context)) :
    (execute start (before ++ after)).2.events =
      (execute start before).2.events ++ (execute (execute start before).1 after).2.events := by
  induction before generalizing start with
  | nil => rfl
  | cons task rest ih =>
      exact congrArg (List.cons (step start task).2.result.2) (ih (step start task).next)

def Execution.previous {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) {item} :
    Ref start.memory.items item → Ref finish.memory.items item :=
  match executed with
  | .nil => fun old => old
  | .cons produced _ tail => fun old => tail.previous (produced.previous old)

theorem Execution.previous_position {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) {item}
    (old : Ref start.memory.items item) :
    (executed.previous old).position = executed.added + old.position := by
  induction executed with
  | nil => exact (Nat.zero_add _).symm
  | cons produced actual tail ih =>
      change (tail.previous (produced.previous old)).position =
        (produced.added + tail.added) + old.position
      rw [ih, produced.previous_position]
      rw [Nat.add_comm produced.added tail.added, Nat.add_assoc]

theorem Execution.previous_evidence {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) {item}
    (old : Ref start.memory.items item) :
    finish.memory.valid (executed.previous old) = start.memory.valid old := by
  induction executed with
  | nil => rfl
  | cons produced actual tail ih =>
      exact (ih (produced.previous old)).trans (produced.previous_evidence old)

theorem Execution.depth {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) :
    finish.cursor.depth = start.cursor.depth + tasks.length := by
  induction executed with
  | nil => exact (Nat.add_zero _).symm
  | @cons start task rest finish produced actual tail ih =>
      rw [ih, produced.depth]
      change (start.cursor.depth + 1) + rest.length = start.cursor.depth + (rest.length + 1)
      rw [Nat.add_assoc, Nat.add_comm 1 rest.length]

theorem Execution.items {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) :
    finish.memory.items.length = start.memory.items.length + executed.added := by
  induction executed with
  | nil => exact (Nat.add_zero _).symm
  | cons produced actual tail ih =>
      rw [ih, produced.items]
      exact Nat.add_assoc _ _ _

def transportGoal {before after demands}
    (references : {item : Citation} → Ref before item → Ref after item) :
    Goal demands before → Goal demands after
  | .nil _ => .nil _
  | .cons demand item located meets tail =>
      .cons demand item (references located) meets (transportGoal references tail)

def Execution.old_goal {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish) {received} :
    Goal received start.memory.items → Goal received finish.memory.items :=
  transportGoal executed.previous

def prependGoal {demand rest items} (head : Goal [demand] items)
    (tail : Goal rest items) : Goal (demand :: rest) items := by
  cases head with
  | cons _ item located meets _ => exact .cons demand item located meets tail

/-- Constructive accomplishment of the whole received list. Its proof consumes
each actual completion, then transports the element through the actual tail. -/
def Execution.goal {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish)
    (admissible : TaskAdmissible sources contract tasks) : Goal (demands tasks) finish.memory.items :=
  match executed, admissible with
  | .nil, .nil => .nil _
  | .cons ⟨_stage, .blocked leftImpossible _⟩ _ _tail,
      .cons (.left permission meets) _ => False.elim (leftImpossible permission meets)
  | .cons ⟨_stage, .blocked _ rightImpossible⟩ _ _tail,
      .cons (.right permission meets) _ => False.elim (rightImpossible permission meets)
  | .cons ⟨_stage, .complete packet⟩ _ tail, .cons _ restAdmissible =>
      prependGoal (tail.old_goal packet.goal) (tail.goal restAdmissible)

theorem Execution.all_added {context sources contract start tasks finish}
    (executed : @Execution context sources contract start tasks finish)
    (admissible : TaskAdmissible sources contract tasks) : executed.added = tasks.length := by
  induction executed with
  | nil => rfl
  | @cons start task rest finish produced actual tail ih =>
      cases admissible with
      | cons head restAdmissible =>
          rcases produced with ⟨stage, decision⟩
          cases decision with
          | blocked leftImpossible rightImpossible =>
              cases head with
              | left permission meets => exact False.elim (leftImpossible permission meets)
              | right permission meets => exact False.elim (rightImpossible permission meets)
          | complete packet =>
              change 1 + tail.added = rest.length + 1
              rw [ih restAdmissible]
              exact Nat.add_comm _ _

def accomplishment {context sources contract} (start : @State context sources contract)
    (tasks : List (Obligation context)) (admissible : TaskAdmissible sources contract tasks) :
    Goal (demands tasks) (execute start tasks).1.memory.items :=
  (execute start tasks).2.goal admissible

theorem exact_step_count {context sources contract} (start : @State context sources contract)
    (tasks : List (Obligation context)) :
    (execute start tasks).1.cursor.depth = start.cursor.depth + tasks.length :=
  (execute start tasks).2.depth

theorem exact_item_count {context sources contract} (start : @State context sources contract)
    (tasks : List (Obligation context)) (admissible : TaskAdmissible sources contract tasks) :
    (execute start tasks).1.memory.items.length = start.memory.items.length + tasks.length := by
  rw [(execute start tasks).2.items, (execute start tasks).2.all_added admissible]

theorem completion_verdict {context sources contract} (start : @State context sources contract)
    (tasks : List (Obligation context)) (admissible : TaskAdmissible sources contract tasks) :
    goalSucceeded (demands tasks) (execute start tasks).1.memory.items = true := by
  unfold goalSucceeded
  cases evaluated : decideGoal (demands tasks) (execute start tasks).1.memory.items with
  | complete _ => rfl
  | incomplete absent => exact False.elim (absent (accomplishment start tasks admissible))

theorem execute_after_context_erasure {context sources contract}
    {Context : Type} (state : @State context sources contract × Context)
    (reset : Context → Context) (tasks : List (Obligation context)) :
    execute (state.1, reset state.2).1 tasks = execute state.1 tasks := rfl

end ConstitutiveSearch.Agent.Local.Documentary.Dossier
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Obligation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.demands
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.selectGoal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.forbidden_list_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.PairAdmissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.TaskAdmissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.State
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.next
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.added
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.depth
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.items
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.incorporationReference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.incorporationReference_position
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.incorporationReference_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.previous_position
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Step.previous_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.execute_append
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.added
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.events_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.execute_append_events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.previous_position
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.previous_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.depth
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.items
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.transportGoal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.old_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.prependGoal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.Execution.all_added
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.accomplishment
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.exact_step_count
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.exact_item_count
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.completion_verdict
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Dossier.execute_after_context_erasure
/- AXIOM_AUDIT_END -/
