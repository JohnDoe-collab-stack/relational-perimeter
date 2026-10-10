import Tests.LocalAlignment.DocumentaryPortableControl

/-! Executable recovery data for the existing documentary machine. The common
preparation reads its retained queue and calls the existing transition once.
Primitive validity is used by proofs, never by the selection algorithm.
The count below concerns semantic operations; instrumented internal cost and
physical commit are separate obligations. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.RecoveryData
open Resources Program Adaptive Snapshot

variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {Context : Type}
  {final : List Specification}

abbrev Data (before : @PresentData context sources contract rules Context final) :=
  Script context rules before.slots final

def capture (before : @PresentData context sources contract rules Context final) : Data before :=
  before.remaining

abbrev Valid (before : @PresentData context sources contract rules Context final) :=
  Snapshot.Accomplishable before

def rank (before : @PresentData context sources contract rules Context final) : Nat :=
  before.remaining.length

def silent (Context : Type) : Adaptive.Policy Context :=
  ⟨fun modelContext _ _ => ⟨modelContext, none⟩, fun modelContext => modelContext⟩

def signal : Adaptive.Signal := ⟨"", false⟩

def request (Context : Type) : Memory.Request Context := .progress (silent Context) signal

structure Packet (before : @PresentData context sources contract rules Context final) where
  private mk ::
  transition : Memory.Transition before (request Context)
  actual : transition = Memory.step before (request Context)

def prepare (before : @PresentData context sources contract rules Context final) : Packet before :=
  let actual := Memory.step before (request Context)
  ⟨actual, rfl⟩

def preserves {before : @PresentData context sources contract rules Context final}
    (packet : Packet before) (valid : Valid before) : Valid packet.transition.next :=
  packet.transition.progress valid

theorem decreases {before : @PresentData context sources contract rules Context final}
    (packet : Packet before) (positive : 0 < rank before) :
    rank packet.transition.next < rank before := by
  rw [packet.actual]
  cases before with
  | mk slots current remaining =>
      cases remaining with
      | done => exact False.elim (Nat.not_lt_zero _ positive)
      | cons instruction tail =>
          exact Memory.strict_progress current instruction tail (silent Context) signal

theorem previous {before : @PresentData context sources contract rules Context final}
    (packet : Packet before) {spec} (old : Ref before.slots spec) :
    packet.transition.next.session.frame.bindings.read (packet.transition.prior old) =
      (before.session.frame.bindings.read old).map
        (Program.transport before.session.frame.store.2 packet.transition.next.session.frame.store.2
          packet.transition.extension) := packet.transition.previous old

structure Goal (before : @PresentData context sources contract rules Context final) where
  slotsExact : before.slots = final
  complete : Program.Complete before.session.frame.restore

def zero_goal (before : @PresentData context sources contract rules Context final)
    (valid : Valid before) (zero : rank before = 0) : Goal before := by
  cases before with
  | mk slots current remaining =>
      cases remaining with
      | done => exact ⟨rfl, valid.initial⟩
      | cons instruction tail => exact False.elim (Nat.noConfusion zero)

theorem silent_events {slots spec}
    (before : @Adaptive.Session context sources contract rules Context slots)
    (instruction : Instruction context rules slots spec) (received : Signal) :
    (Adaptive.takeTurn (silent Context) before received instruction).effect.summary.events.length = 1 := rfl

theorem execution_attempts {before after}
    {feed : Nat → Signal} {start : @Adaptive.Session context sources contract rules Context before}
    {script : Script context rules before after} {finish}
    (trace : Adaptive.Execution (silent Context) feed start script finish) :
    trace.attempts = script.length := by
  induction trace with
  | done => rfl
  | cons turn actual rest ih =>
      change turn.effect.summary.events.length + rest.attempts = _
      have one : turn.effect.summary.events.length = 1 :=
        (congrArg (fun produced => produced.effect.summary.events.length) actual).trans
          (silent_events _ _ _)
      rw [one, ih]
      exact Nat.add_comm 1 _

abbrev Result (before : @PresentData context sources contract rules Context final) :=
  (finish : Adaptive.Session sources contract rules Context final) ×
    Adaptive.Execution (silent Context) (fun _ => signal) before.session.restore before.remaining finish

def recover (before : @PresentData context sources contract rules Context final) : Result before :=
  Memory.finish before (silent Context) (fun _ => signal)

def recover_complete (before : @PresentData context sources contract rules Context final)
    (actual : Result before) (valid : Valid before) : Program.Complete actual.1.frame :=
  Memory.finish_complete (data := before) actual valid

theorem recover_rounds (before : @PresentData context sources contract rules Context final) :
    (recover before).1.round = before.session.round + rank before :=
  Memory.finish_rounds (data := before) (recover before)

theorem recover_attempts (before : @PresentData context sources contract rules Context final) :
    (recover before).2.attempts = rank before := execution_attempts (recover before).2

theorem reset_commutes (before : @PresentData context sources contract rules Context final)
    (policy : Adaptive.Policy Context) :
    (prepare (before.reset policy)).transition.next = (prepare before).transition.next.reset policy := by
  cases before with
  | mk slots current remaining => cases remaining <;> rfl

theorem projection_packet (source : @Memory.Source context sources contract rules Context final) :
    (prepare (Memory.project source)).transition.next =
      Memory.project (Memory.sourceStep source (request Context)).1 := rfl

theorem projection_recover (source : @Memory.Source context sources contract rules Context final) :
    recover (Memory.project source) = recover source.present := rfl

theorem loaded_packet (codec : ControlCodec.Codec Context)
    (before after : @PresentData context sources contract rules Context final)
    (loaded : PortableControl.loadPresent codec before.session.frame.dossier before.session.frame.store final
      (PortableControl.save codec (PortableControl.capture before)) = some after) :
    HEq (prepare after) (prepare before) := by
  have same := Option.some.inj ((PortableControl.present_byte_roundtrip codec before).symm.trans loaded)
  cases same
  rfl

theorem loaded_recover (codec : ControlCodec.Codec Context)
    (before after : @PresentData context sources contract rules Context final)
    (loaded : PortableControl.loadPresent codec before.session.frame.dossier before.session.frame.store final
      (PortableControl.save codec (PortableControl.capture before)) = some after) :
    HEq (recover after) (recover before) := by
  have same := Option.some.inj ((PortableControl.present_byte_roundtrip codec before).symm.trans loaded)
  cases same
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.RecoveryData

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.Data
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.Valid
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.rank
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.silent
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.signal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.request
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.prepare
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.preserves
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.decreases
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.previous
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.Goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.zero_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.silent_events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.execution_attempts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.Result
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.recover
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.recover_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.recover_rounds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.recover_attempts
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.reset_commutes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.projection_packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.projection_recover
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.loaded_packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RecoveryData.loaded_recover
/- AXIOM_AUDIT_END -/
