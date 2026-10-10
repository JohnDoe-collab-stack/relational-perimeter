import Tests.LocalAlignment.DocumentaryProgram

/-! Adaptive proposals over the received finite task queue. One bounded turn
consumes at most one proposal and then realizes the current obligation. Extra
incorporated occurrences retain their formation; they do not replace a task port.
The context may reset, while the actual frame, queue and round continue. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Adaptive
open Resources Program

def locate {Kind : Type} : (context : List Kind) → Nat → Option ((kind : Kind) × Ref context kind)
  | [], _ => none
  | kind :: _, 0 => some ⟨kind, .here⟩
  | _ :: rest, position + 1 => match locate rest position with
    | none => none
    | some prior => some ⟨prior.1, .prior prior.2⟩

inductive Proposal where
  | current
  | reverseSources
  | inspect (slot : Nat)
  | quote (left right : Nat)
  | deduce (rule left right : Nat)

structure Readout where
  position : Nat
  value : Int
  origins : List Nat

inductive Route where
  | matched
  | reversed
  | absent
  | invalid
  | inspected
  | diverted

structure Summary where
  route : Route
  events : List Program.Event
  inspection : Option Readout

structure Observation where
  round : Nat
  depth : Nat
  available : Nat
  slots : Nat
  goal : Specification
  last : Option Summary

structure Policy (Context : Type) where
  choose : Context → String → Observation → Context × Option Proposal
  reset : Context → Context

structure Signal where
  input : String
  forget : Bool

structure Session {context} (sources : Support SourceValue context) (contract : Contract)
    (rules : Deduction.Policy) (Context : Type) (slots : List Specification) where
  frame : Frame sources contract rules slots
  context : Context
  round : Nat
  last : Option Summary

def observe {context sources contract rules Context slots spec}
    (session : @Session context sources contract rules Context slots)
    (_instruction : Instruction context rules slots spec) : Observation :=
  ⟨session.round, session.frame.dossier.cursor.depth, session.frame.store.1.length,
    slots.length, spec, session.last⟩

def selection {context sources contract rules Context slots spec}
    (policy : Policy Context) (session : @Session context sources contract rules Context slots)
    (signal : Signal) (instruction : Instruction context rules slots spec) : Context × Option Proposal :=
  policy.choose (if signal.forget then policy.reset session.context else session.context)
    signal.input (observe session instruction)

def resetContext {context sources contract rules Context slots}
    (policy : Policy Context) (session : @Session context sources contract rules Context slots) :
    Session sources contract rules Context slots :=
  ⟨session.frame, policy.reset session.context, session.round, session.last⟩

def reverseTask {context} (task : Dossier.Obligation context) : Dossier.Obligation context :=
  ⟨task.demand, task.right, task.left⟩

def reverseReady {context sources contract task}
    (ready : @Dossier.PairAdmissible context sources contract task) :
    Dossier.PairAdmissible sources contract (reverseTask task) :=
  match ready with
  | .left permission correct => .right permission correct
  | .right permission correct => .left permission correct

def dropHead {context sources contract rules slots spec}
    (frame : @Frame context sources contract rules (spec :: slots)) : Frame sources contract rules slots :=
  ⟨frame.dossier, frame.store, fun old => frame.bindings (.prior old)⟩

def carry {context sources contract rules slots spec before instruction}
    (produced : @Program.Step context sources contract rules slots spec before instruction)
    (complete : Complete before) : Complete (dropHead produced.next) :=
  fun old =>
    let prior := complete old
    ⟨transport before.store.2 produced.next.store.2 produced.extension prior.occurrence,
      (produced.previous old).trans
        (congrArg (Option.map (transport before.store.2 produced.next.store.2 produced.extension)) prior.actual),
      (produced.extension.reads prior.occurrence.2).symm ▸ prior.meets⟩

structure Effect {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (instruction : Instruction context rules slots spec) where
  private mk ::
  next : Frame sources contract rules (spec :: slots)
  extension : Support.Extension before.store.2.resources next.store.2.resources
  previous : ∀ {oldSpec} (old : Ref slots oldSpec), next.bindings (.prior old) =
    (before.bindings old).map (transport before.store.2 next.store.2 extension)
  summary : Summary
  bound : summary.events.length ≤ 2
  progress : Ready sources contract instruction → Complete before → Complete next

def single {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (instruction chosen : Instruction context rules slots spec)
    (produced : Program.Step before chosen)
    (ready : Ready sources contract instruction → Ready sources contract chosen)
    (route : Route) (inspection : Option Readout) : Effect before instruction :=
  ⟨produced.next, produced.extension, produced.previous, ⟨route, [produced.event], inspection⟩,
    Nat.le_succ 1, fun original complete => produced.progress (ready original) complete⟩

def fallback {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (instruction : Instruction context rules slots spec)
    (route : Route) (inspection : Option Readout) : Effect before instruction :=
  let produced := Program.step before instruction
  single before instruction instruction produced id route inspection

def diverted {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (instruction proposed : Instruction context rules slots spec) : Effect before instruction :=
  let first := Program.step before proposed
  let retained := dropHead first.next
  let required := Program.step retained instruction
  let extension := first.extension.compose required.extension
  have previous : ∀ {oldSpec} (old : Ref slots oldSpec), required.next.bindings (.prior old) =
      (before.bindings old).map (transport before.store.2 required.next.store.2 extension) := by
    intro oldSpec old
    rw [required.previous]
    change (first.next.bindings (.prior old)).map _ = _
    rw [first.previous]
    cases before.bindings old <;> rfl
  ⟨required.next, extension, previous, ⟨.diverted, [first.event, required.event], none⟩,
    Nat.le_refl 2, fun ready complete => required.progress ready (carry first complete)⟩

def dispatch {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (instruction : Instruction context rules slots spec) : Option Proposal → Effect before instruction
  | none => fallback before instruction .absent none
  | some .current =>
      let produced := Program.step before instruction
      single before instruction instruction produced id .matched none
  | some .reverseSources => match instruction with
    | .quotation task =>
        let chosen := Instruction.quotation (reverseTask task)
        let produced := Program.step before chosen
        single before (.quotation task) chosen produced reverseReady .reversed none
    | .conclusion request leftRef rightRef demand =>
        fallback before (.conclusion request leftRef rightRef demand) .invalid none
  | some (.inspect index) => match locate slots index with
    | none => fallback before instruction .invalid none
    | some located => match before.bindings located.2 with
      | none => fallback before instruction .invalid none
      | some occurrence => fallback before instruction .inspected
          (some ⟨occurrence.2.position, before.store.2.resources.read occurrence.2, occurrence.1.origins⟩)
  | some (.quote left right) => match instruction with
    | .conclusion request leftRef rightRef demand =>
        fallback before (.conclusion request leftRef rightRef demand) .invalid none
    | .quotation task =>
        if left == task.left.2.position && right == task.right.2.position then
          let produced := Program.step before (.quotation task)
          single before (.quotation task) (.quotation task) produced id .matched none
        else if left == task.right.2.position && right == task.left.2.position then
          let chosen := Instruction.quotation (reverseTask task)
          let produced := Program.step before chosen
          single before (.quotation task) chosen produced reverseReady .reversed none
        else match locate context left with
          | none => fallback before (.quotation task) .invalid none
          | some leftOrigin => match locate context right with
            | none => fallback before (.quotation task) .invalid none
            | some rightOrigin => diverted before (.quotation task)
                (.quotation ⟨task.demand, leftOrigin, rightOrigin⟩)
  | some (.deduce rule left right) => match instruction with
    | .quotation task => fallback before (.quotation task) .invalid none
    | .conclusion request leftRef rightRef demand =>
        if rule == request.2.position && left == leftRef.position && right == rightRef.position then
          let produced := Program.step before (.conclusion request leftRef rightRef demand)
          single before (.conclusion request leftRef rightRef demand) (.conclusion request leftRef rightRef demand) produced id .matched none
        else match locate rules.rules rule with
          | none => fallback before (.conclusion request leftRef rightRef demand) .invalid none
          | some alternative => match locate slots left with
            | none => fallback before (.conclusion request leftRef rightRef demand) .invalid none
            | some leftSlot => match locate slots right with
              | none => fallback before (.conclusion request leftRef rightRef demand) .invalid none
              | some rightSlot => diverted before (.conclusion request leftRef rightRef demand)
                  (.conclusion alternative leftSlot.2 rightSlot.2 demand)

structure Turn {context sources contract rules Context slots spec}
    (before : @Session context sources contract rules Context slots)
    (instruction : Instruction context rules slots spec) where
  private mk ::
  next : Session sources contract rules Context (spec :: slots)
  proposal : Option Proposal
  effect : Effect before.frame instruction
  frameExact : next.frame = effect.next
  tick : next.round = before.round + 1

def takeTurn {context sources contract rules Context slots spec}
    (policy : Policy Context) (before : @Session context sources contract rules Context slots)
    (signal : Signal) (instruction : Instruction context rules slots spec) : Turn before instruction :=
  let chosen := selection policy before signal instruction
  let effect := dispatch before.frame instruction chosen.2
  let next := Session.mk effect.next chosen.1 (before.round + 1) (some effect.summary)
  ⟨next, chosen.2, effect, rfl, rfl⟩

def Turn.complete {context sources contract rules Context slots spec before instruction}
    (turn : @Turn context sources contract rules Context slots spec before instruction)
    (ready : Ready sources contract instruction) (complete : Complete before.frame) : Complete turn.next.frame :=
  turn.frameExact.symm ▸ turn.effect.progress ready complete

def Turn.extension {context sources contract rules Context slots spec before instruction}
    (turn : @Turn context sources contract rules Context slots spec before instruction) :
    Support.Extension before.frame.store.2.resources turn.next.frame.store.2.resources :=
  turn.frameExact.symm ▸ turn.effect.extension

theorem Turn.previous {context sources contract rules Context slots spec before instruction}
    (turn : @Turn context sources contract rules Context slots spec before instruction)
    {oldSpec} (old : Ref slots oldSpec) : turn.next.frame.bindings (.prior old) =
      (before.frame.bindings old).map (transport before.frame.store.2 turn.next.frame.store.2 turn.extension) := by
  rcases turn with ⟨⟨frame, modelContext, round, last⟩, proposal, effect, frameExact, tick⟩
  cases frameExact
  exact effect.previous old

inductive Execution {context sources contract rules Context}
    (policy : Policy Context) (feed : Nat → Signal) : {before after : List Specification} →
      Session sources contract rules Context before → Script context rules before after →
        Session sources contract rules Context after → Type 3 where
  | done {before start} : @Execution context sources contract rules Context policy feed before before start .done start
  | cons {before spec after start instruction tail finish}
      (turn : @Turn context sources contract rules Context before spec start instruction)
      (actual : turn = takeTurn policy start (feed start.round) instruction)
      (rest : @Execution context sources contract rules Context policy feed (spec :: before) after turn.next tail finish) :
      Execution policy feed start (.cons instruction tail) finish

def run {context sources contract rules Context before after}
    (policy : Policy Context) (feed : Nat → Signal)
    (start : @Session context sources contract rules Context before) (script : Script context rules before after) :
    (finish : Session sources contract rules Context after) × Execution policy feed start script finish :=
  match script with
  | .done => ⟨start, .done⟩
  | .cons instruction tail =>
      let turn := takeTurn policy start (feed start.round) instruction
      let rest := run policy feed turn.next tail
      ⟨rest.1, .cons turn rfl rest.2⟩

def Execution.complete {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish)
    (admissible : Program.Admissible sources contract script) (initial : Complete start.frame) : Complete finish.frame :=
  match trace, admissible with
  | .done, .done => initial
  | .cons turn _ rest, .cons ready remaining => rest.complete remaining (turn.complete ready initial)

theorem all_policies_accomplish {context sources contract rules Context before after}
    (policy : Policy Context) (feed : Nat → Signal)
    (start : @Session context sources contract rules Context before) (script : Script context rules before after)
    (admissible : Program.Admissible sources contract script) (initial : Complete start.frame) :
    Nonempty (Complete (run policy feed start script).1.frame) :=
  ⟨(run policy feed start script).2.complete admissible initial⟩

def Execution.extension {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish) :
    Support.Extension start.frame.store.2.resources finish.frame.store.2.resources :=
  match trace with
  | .done => .identity start.frame.store.2.resources
  | .cons turn _ rest => turn.extension.compose rest.extension

def Execution.summaries {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish) : List Summary :=
  match trace with
  | .done => []
  | .cons turn _ rest => turn.effect.summary :: rest.summaries

def Execution.attempts {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish) : Nat :=
  match trace with
  | .done => 0
  | .cons turn _ rest => turn.effect.summary.events.length + rest.attempts

theorem Execution.rounds {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish) :
    finish.round = start.round + script.length := by
  induction trace with
  | done => exact (Nat.add_zero _).symm
  | cons turn actual rest tail =>
      rw [tail, turn.tick]
      exact (Nat.add_assoc _ _ _).trans (congrArg (Nat.add _) (Nat.add_comm 1 _))

theorem Execution.bound {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish) :
    trace.attempts ≤ script.length * 2 := by
  induction trace with
  | done => exact Nat.le_refl 0
  | cons turn actual rest tail =>
      change turn.effect.summary.events.length + rest.attempts ≤ Nat.succ (Script.length _) * 2
      rw [Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add turn.effect.bound tail) (Nat.le_of_eq (Nat.add_comm _ _))

theorem remaining_strictly_decreases {context rules before spec after}
    (instruction : Instruction context rules before spec) (tail : Script context rules (spec :: before) after) :
    tail.length < (Script.cons instruction tail).length := Nat.lt_succ_self _

theorem one_turn_accomplishes {context sources contract rules Context slots spec}
    (policy : Policy Context) (start : @Session context sources contract rules Context slots)
    (signal : Signal) (instruction : Instruction context rules slots spec)
    (ready : Ready sources contract instruction) (initial : Complete start.frame) :
    Nonempty (Realized (takeTurn policy start signal instruction).next.frame (.here : Ref (spec :: slots) spec)) :=
  ⟨(takeTurn policy start signal instruction).complete ready initial .here⟩

theorem Execution.bindings {context sources contract rules Context policy feed before after start script finish}
    (trace : @Execution context sources contract rules Context policy feed before after start script finish)
    {spec} (old : Ref before spec) : finish.frame.bindings (script.previous old) =
      (start.frame.bindings old).map (transport start.frame.store.2 finish.frame.store.2 trace.extension) := by
  induction trace with
  | @done before start =>
      change start.frame.bindings old = (start.frame.bindings old).map _
      cases start.frame.bindings old <;> rfl
  | @cons before spec after start instruction tailScript finish turn actual rest tail =>
      rw [Script.previous, tail, turn.previous]
      cases start.frame.bindings old <;> rfl

/-- The retained present includes the received task queue, separately from the
resettable proposal context. It contains no counter in that context. -/
structure Present {context} (sources : Support SourceValue context) (contract : Contract)
    (rules : Deduction.Policy) (Context : Type) (final : List Specification) where
  slots : List Specification
  session : Session sources contract rules Context slots
  remaining : Script context rules slots final

def Present.finish {context sources contract rules Context final}
    (present : @Present context sources contract rules Context final)
    (policy : Policy Context) (feed : Nat → Signal) := run policy feed present.session present.remaining

def Present.reset {context sources contract rules Context final}
    (present : @Present context sources contract rules Context final) (policy : Policy Context) :
    Present sources contract rules Context final :=
  ⟨present.slots, resetContext policy present.session, present.remaining⟩

theorem Present.reset_keeps_remaining {context sources contract rules Context final}
    (present : @Present context sources contract rules Context final) (policy : Policy Context) :
    (present.reset policy).remaining.length = present.remaining.length := rfl

theorem reset_keeps_round {context sources contract rules Context slots}
    (policy : Policy Context) (start : @Session context sources contract rules Context slots) :
    (resetContext policy start).round = start.round := rfl

theorem reset_keeps_frame {context sources contract rules Context slots}
    (policy : Policy Context) (start : @Session context sources contract rules Context slots) :
    (resetContext policy start).frame = start.frame := rfl

theorem all_policies_after_reset {context sources contract rules Context before after}
    (policy : Policy Context) (feed : Nat → Signal)
    (start : @Session context sources contract rules Context before) (script : Script context rules before after)
    (admissible : Program.Admissible sources contract script) (initial : Complete start.frame) :
    Nonempty (Complete (run policy feed (resetContext policy start) script).1.frame) :=
  all_policies_accomplish policy feed (resetContext policy start) script admissible initial

theorem run_append {context sources contract rules Context before middle after}
    (policy : Policy Context) (feed : Nat → Signal) (start : @Session context sources contract rules Context before)
    (first : Script context rules before middle) (last : Script context rules middle after) :
    (run policy feed start (first.append last)).1 = (run policy feed (run policy feed start first).1 last).1 := by
  induction first with
  | done => rfl
  | cons instruction tail ih => exact ih (start := (takeTurn policy start (feed start.round) instruction).next) last

end ConstitutiveSearch.Agent.Local.Documentary.Adaptive
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.locate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Proposal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Readout
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Route
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Summary
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Observation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Policy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Signal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Session
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.observe
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.selection
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.resetContext
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.reverseTask
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.reverseReady
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.dropHead
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.carry
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Effect
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.single
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.fallback
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.diverted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.dispatch
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Turn
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.takeTurn
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Turn.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Turn.extension
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Turn.previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.all_policies_accomplish
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.extension
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.summaries
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.attempts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.rounds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.remaining_strictly_decreases
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.one_turn_accomplishes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Execution.bindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Present.finish
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Present.reset
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.Present.reset_keeps_remaining
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.reset_keeps_round
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.reset_keeps_frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.all_policies_after_reset
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Adaptive.run_append
/- AXIOM_AUDIT_END -/
