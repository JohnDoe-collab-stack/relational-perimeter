import Tests.LocalAlignment.DocumentarySnapshot

/-! Documentary futures after projection. The fixed configuration retains the
received sources, permissions, rule operations and task constructors. Policies
receive only the current context and observation. Old interaction archives have
no read operation in this language. All actual resource formations are retained. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Memory
open Resources Program Adaptive Snapshot

inductive Request (Context : Type) where
  | progress (policy : Adaptive.Policy Context) (signal : Signal)
  | inspect (slot : Nat)
  | status
  | reset (policy : Adaptive.Policy Context)

structure Interaction where
  round : Nat
  signal : Signal
  proposal : Option Proposal
  summary : Summary

inductive Event where
  | produced (summary : Summary)
  | inspected (result : Option Readout)
  | observed (round depth available slots remaining : Nat) (succeeded : Bool)
  | reset
  | finished

structure Located {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) where
  spec : Specification
  slot : Ref data.slots spec
  occurrence : Occurrence data.session.frame.store
  actual : data.session.frame.bindings.read slot = some occurrence

def locateBinding {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) (index : Nat) : Option (Located data) :=
  match locate data.slots index with
  | none => none
  | some located => match h : data.session.frame.bindings.read located.2 with
    | none => none
    | some occurrence => some ⟨located.1, located.2, occurrence, h⟩

def Located.read {context sources contract rules Context final data}
    (found : @Located context sources contract rules Context final data) : Readout :=
  ⟨found.occurrence.2.position, data.session.frame.store.2.resources.read found.occurrence.2,
    found.occurrence.1.origins⟩

def read {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) (index : Nat) : Option Readout :=
  match locate data.slots index with
  | none => none
  | some located => (data.session.frame.bindings.read located.2).map (fun occurrence =>
      ⟨occurrence.2.position, data.session.frame.store.2.resources.read occurrence.2, occurrence.1.origins⟩)

theorem head_read {context sources contract rules Context final spec slots}
    (current : @SessionData context sources contract rules Context (spec :: slots))
    (queue : Script context rules (spec :: slots) final) (realized : Realized current.frame.restore (.here : Ref _ spec)) :
    read ⟨spec :: slots, current, queue⟩ 0 = some
      ⟨realized.occurrence.2.position, current.frame.store.2.resources.read realized.occurrence.2,
        realized.occurrence.1.origins⟩ := by
  unfold read
  dsimp only [locate]
  have actual : current.frame.bindings.read .here = some realized.occurrence := realized.actual
  rw [actual]
  rfl

def Admission {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) : Request Context → Type
  | .inspect index => {found : Located data // locateBinding data index = some found}
  | .progress _ _ | .reset _ | .status => PUnit

def accepted {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) : (request : Request Context) → Option (Admission data request)
  | .inspect index => match h : locateBinding data index with
    | none => none
    | some found => some ⟨found, h⟩
  | .progress _ _ | .reset _ | .status => some PUnit.unit

structure Transition {context sources contract rules Context final}
    (before : @PresentData context sources contract rules Context final) (request : Request Context) where
  private mk ::
  next : PresentData sources contract rules Context final
  event : Event
  interaction : Option Interaction
  progress : Accomplishable before → Accomplishable next
  nonincrease : next.remaining.length ≤ before.remaining.length
  extension : Support.Extension before.session.frame.store.2.resources next.session.frame.store.2.resources
  prior : ∀ {spec}, Ref before.slots spec → Ref next.slots spec
  previous : ∀ {spec} (old : Ref before.slots spec), next.session.frame.bindings.read (prior old) =
    (before.session.frame.bindings.read old).map (transport before.session.frame.store.2 next.session.frame.store.2 extension)

theorem identity_binding {context sources contract rules}
    (store : @Deduction.Store context sources contract rules) (binding : Option (Occurrence store)) :
    binding = binding.map (transport store.2 store.2 (.identity store.2.resources)) := by
  cases binding <;> rfl

def advance {context sources contract rules Context slots final}
    (current : @SessionData context sources contract rules Context slots)
    (queue : Script context rules slots final) (policy : Adaptive.Policy Context) (signal : Signal) :
    Transition ⟨slots, current, queue⟩ (.progress policy signal) :=
  match queue with
  | .done => ⟨⟨slots, current, .done⟩, .finished, none, id, Nat.le_refl _, .identity _, fun ref => ref, fun old => identity_binding current.frame.store (current.frame.bindings.read old)⟩
  | .cons instruction tail =>
      let actual := takeTurn policy current.restore signal instruction
      let next := PresentData.mk _ (Snapshot.session actual.next) tail
      ⟨next, .produced actual.effect.summary,
        some ⟨current.round, signal, actual.proposal, actual.effect.summary⟩,
        fun valid =>
          let tasks : Program.Admissible sources contract (.cons instruction tail) := valid.tasks
          match tasks with
          | .cons ready rest => ⟨complete_forward actual.next.frame (actual.complete ready valid.initial), rest⟩,
        Nat.le_succ _, actual.extension, fun ref => .prior ref,
        fun old => (binding_exact actual.next.frame (.prior old)).trans (actual.previous old)⟩

def step {context sources contract rules Context final}
    (before : @PresentData context sources contract rules Context final) (request : Request Context) : Transition before request :=
  match request with
  | .inspect index => ⟨before, .inspected (read before index), none, id, Nat.le_refl _, .identity _, fun ref => ref, fun old => identity_binding before.session.frame.store (before.session.frame.bindings.read old)⟩
  | .status => ⟨before, .observed before.session.round before.session.frame.dossier.cursor.depth
      before.session.frame.store.1.length before.slots.length before.remaining.length
      (Program.succeeded before.session.frame.restore), none, id, Nat.le_refl _, .identity _, fun ref => ref, fun old => identity_binding before.session.frame.store (before.session.frame.bindings.read old)⟩
  | .reset policy => ⟨before.reset policy, .reset, none,
      fun valid => ⟨valid.initial, valid.tasks⟩, Nat.le_refl _, .identity _, fun ref => ref,
      fun old => identity_binding before.session.frame.store (before.session.frame.bindings.read old)⟩
  | .progress policy signal => advance before.session before.remaining policy signal

theorem strict_progress {context sources contract rules Context final slots spec}
    (current : @SessionData context sources contract rules Context slots)
    (instruction : Instruction context rules slots spec) (tail : Script context rules (spec :: slots) final)
    (policy : Adaptive.Policy Context) (signal : Signal) :
    (step ⟨slots, current, .cons instruction tail⟩ (.progress policy signal)).next.remaining.length <
      (Script.cons instruction tail).length := Nat.lt_succ_self _

inductive Execution {context : List SourceKey} {sources : Support SourceValue context}
    {contract : Contract} {rules : Deduction.Policy} {Context : Type} {final : List Specification} :
    PresentData sources contract rules Context final → List (Request Context) →
      PresentData sources contract rules Context final → Type 3 where
  | done {before} : Execution before [] before
  | cons {before request rest finish} (actual : Transition before request)
      (executed : actual = step before request) (tail : Execution actual.next rest finish) :
      Execution before (request :: rest) finish

def run {context sources contract rules Context final}
    (before : @PresentData context sources contract rules Context final) (requests : List (Request Context)) :
    (finish : PresentData sources contract rules Context final) × Execution before requests finish :=
  match requests with
  | [] => ⟨before, .done⟩
  | request :: rest =>
      let actual := step before request
      let tail := run actual.next rest
      ⟨tail.1, .cons actual rfl tail.2⟩

def Execution.events {context sources contract rules Context final before requests finish}
    (trace : @Execution context sources contract rules Context final before requests finish) : List Event :=
  match trace with
  | .done => []
  | .cons actual _ tail => actual.event :: tail.events

def Execution.progress {context sources contract rules Context final before requests finish}
    (trace : @Execution context sources contract rules Context final before requests finish)
    (valid : Accomplishable before) : Accomplishable finish :=
  match trace with
  | .done => valid
  | .cons actual _ tail => tail.progress (actual.progress valid)

theorem Execution.nonincrease {context sources contract rules Context final before requests finish}
    (trace : @Execution context sources contract rules Context final before requests finish) :
    finish.remaining.length ≤ before.remaining.length := by
  induction trace with
  | done => exact Nat.le_refl _
  | cons actual executed tail ih => exact Nat.le_trans ih actual.nonincrease

def Execution.extension {context sources contract rules Context final before requests finish}
    (trace : @Execution context sources contract rules Context final before requests finish) :
    Support.Extension before.session.frame.store.2.resources finish.session.frame.store.2.resources :=
  match trace with
  | .done => .identity _
  | .cons actual _ tail => actual.extension.compose tail.extension

def Execution.references {context sources contract rules Context final before requests finish}
    (trace : @Execution context sources contract rules Context final before requests finish)
    {spec} (old : Ref before.slots spec) : Ref finish.slots spec :=
  match trace with
  | .done => old
  | .cons actual _ tail => tail.references (actual.prior old)

theorem Execution.bindings {context sources contract rules Context final before requests finish}
    (trace : @Execution context sources contract rules Context final before requests finish)
    {spec} (old : Ref before.slots spec) : finish.session.frame.bindings.read (trace.references old) =
    (before.session.frame.bindings.read old).map
      (transport before.session.frame.store.2 finish.session.frame.store.2 trace.extension) := by
  induction trace with
  | @done before =>
      exact identity_binding before.session.frame.store (before.session.frame.bindings.read old)
  | @cons before request rest finish actual executed tail ih =>
      rw [Execution.references, ih, actual.previous]
      cases before.session.frame.bindings.read old <;> rfl

structure Source {context} (sources : Support SourceValue context) (contract : Contract)
    (rules : Deduction.Policy) (Context : Type) (final : List Specification) where
  present : PresentData sources contract rules Context final
  archive : List Interaction

def project {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) := source.present

def sourceStep {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (request : Request Context) :
    Source sources contract rules Context final × Event :=
  let actual := step source.present request
  let archive := match actual.interaction with
    | none => source.archive
    | some item => item :: source.archive
  ⟨⟨actual.next, archive⟩, actual.event⟩

theorem projection_next {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (request : Request Context) :
    project (sourceStep source request).1 = (step (project source) request).next := rfl

theorem projection_event {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (request : Request Context) :
    (sourceStep source request).2 = (step (project source) request).event := rfl

def admission_forward {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (request : Request Context)
    (permit : Admission source.present request) : Admission (project source) request := permit

def admission_backward {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (request : Request Context)
    (permit : Admission (project source) request) : Admission source.present request := permit

theorem projection_admission {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (request : Request Context) :
    accepted source.present request = accepted (project source) request := rfl

theorem projection_read {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (index : Nat) :
    read source.present index = read (project source) index := rfl

def sourceRun {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) : List (Request Context) →
      Source sources contract rules Context final × List Event
  | [] => ⟨source, []⟩
  | request :: rest =>
      let actual := sourceStep source request
      let tail := sourceRun actual.1 rest
      ⟨tail.1, actual.2 :: tail.2⟩

theorem all_futures_projection {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context)) :
    project (sourceRun source requests).1 = (run (project source) requests).1 := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih => exact ih (sourceStep source request).1

theorem all_futures_events {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context)) :
    (sourceRun source requests).2 = (run (project source) requests).2.events := by
  induction requests generalizing source with
  | nil => rfl
  | cons request rest ih => exact congrArg (List.cons (sourceStep source request).2) (ih (sourceStep source request).1)

theorem all_futures_reads {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context)) (index : Nat) :
    read (project (sourceRun source requests).1) index = read (run (project source) requests).1 index :=
  congrArg (fun data => read data index) (all_futures_projection source requests)

def all_futures_progress {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context))
    (valid : Accomplishable (project source)) : Accomplishable (project (sourceRun source requests).1) :=
  (all_futures_projection source requests).symm ▸ (run (project source) requests).2.progress valid

def finish {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final)
    (policy : Adaptive.Policy Context) (feed : Nat → Signal) :=
  Adaptive.run policy feed data.session.restore data.remaining

def finish_complete {context sources contract rules Context final data policy feed}
    (actual : (result : Session sources contract rules Context final) ×
      Adaptive.Execution policy feed (@PresentData.session context sources contract rules Context final data).restore data.remaining result)
    (valid : Accomplishable data) : Complete actual.1.frame := actual.2.complete valid.tasks valid.initial

theorem finish_rounds {context sources contract rules Context final data policy feed}
    (actual : (result : Session sources contract rules Context final) ×
      Adaptive.Execution policy feed (@PresentData.session context sources contract rules Context final data).restore data.remaining result) :
    actual.1.round = data.session.round + data.remaining.length := actual.2.rounds

theorem finish_bound {context sources contract rules Context final data policy feed}
    (actual : (result : Session sources contract rules Context final) ×
      Adaptive.Execution policy feed (@PresentData.session context sources contract rules Context final data).restore data.remaining result) :
    actual.2.attempts ≤ data.remaining.length * 2 := actual.2.bound

theorem checkpoint_all_futures {context sources contract rules Context final}
    (data loaded : @PresentData context sources contract rules Context final)
    (loadedFrom : Snapshot.load (Snapshot.save data) = some loaded) (requests : List (Request Context)) :
    (run loaded requests).1 = (run data requests).1 ∧
      (run loaded requests).2.events = (run data requests).2.events := by
  have same : data = loaded := Option.some.inj loadedFrom
  cases same
  exact ⟨rfl, rfl⟩

def checkpoint_accomplishable {context sources contract rules Context final}
    (data loaded : @PresentData context sources contract rules Context final)
    (loadedFrom : Snapshot.load (Snapshot.save data) = some loaded)
    (valid : Accomplishable data) : Accomplishable loaded := (Option.some.inj loadedFrom) ▸ valid

def all_futures_admission {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context)) (next : Request Context) :
    (Admission (project (sourceRun source requests).1) next → Admission (run (project source) requests).1 next) ×
      (Admission (run (project source) requests).1 next → Admission (project (sourceRun source requests).1) next) :=
  ⟨fun permit => (all_futures_projection source requests) ▸ permit,
    fun permit => (all_futures_projection source requests).symm ▸ permit⟩

theorem all_futures_accepted {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context)) (next : Request Context) :
    (accepted (project (sourceRun source requests).1) next).isSome = (accepted (run (project source) requests).1 next).isSome :=
  congrArg (fun data => (accepted data next).isSome) (all_futures_projection source requests)

theorem all_futures_accomplishment {context sources contract rules Context final}
    (source : @Source context sources contract rules Context final) (requests : List (Request Context)) :
    Program.succeeded (project (sourceRun source requests).1).session.frame.restore =
      Program.succeeded (run (project source) requests).1.session.frame.restore :=
  congrArg (fun data => Program.succeeded data.session.frame.restore) (all_futures_projection source requests)

theorem indistinguishable_futures {context sources contract rules Context final}
    (left right : @Source context sources contract rules Context final) (same : project left = project right)
    (requests : List (Request Context)) :
    project (sourceRun left requests).1 = project (sourceRun right requests).1 ∧
      (sourceRun left requests).2 = (sourceRun right requests).2 := by
  constructor
  · exact (all_futures_projection left requests).trans
      ((congrArg (fun data => (run data requests).1) same).trans (all_futures_projection right requests).symm)
  · exact (all_futures_events left requests).trans
      ((congrArg (fun data => (run data requests).2.events) same).trans (all_futures_events right requests).symm)

end ConstitutiveSearch.Agent.Local.Documentary.Memory
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Request
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Interaction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Located
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.locateBinding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Located.read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.head_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Admission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.accepted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Transition
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.identity_binding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.advance
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.step
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.strict_progress
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution.events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution.progress
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution.nonincrease
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution.extension
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution.references
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Execution.bindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.Source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.project
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.sourceStep
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.projection_next
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.projection_event
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.admission_forward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.admission_backward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.projection_admission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.projection_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.sourceRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_projection
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_reads
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_progress
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.finish
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.finish_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.finish_rounds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.finish_bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.checkpoint_all_futures
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.checkpoint_accomplishable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_admission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_accepted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.all_futures_accomplishment
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory.indistinguishable_futures
/- AXIOM_AUDIT_END -/
