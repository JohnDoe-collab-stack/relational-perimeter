import Tests.LocalAlignment.DocumentaryAdaptive

/-! Finite binding tables and typed present snapshots. Actual stores, formation,
source identities and master resources are retained. Binding closures and past
interaction archives are not fields of the payload. No past producer is replayed. -/
set_option genInjectivity false
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Snapshot
open Resources Program Adaptive

inductive Bindings {context sources contract rules}
    (store : @Deduction.Store context sources contract rules) : List Specification → Type where
  | nil : Bindings store []
  | cons {spec rest} (head : Option (Occurrence store))
      (tail : Bindings store rest) : Bindings store (spec :: rest)

def Bindings.read {context sources contract rules store slots spec}
    (table : @Bindings context sources contract rules store slots) (slot : Ref slots spec) : Option (Occurrence store) :=
  match table, slot with
  | .cons head _, .here => head
  | .cons _ tail, .prior old => tail.read old

def Bindings.capture {context sources contract rules store} : (slots : List Specification) →
    ({spec : Specification} → Ref slots spec → Option (Occurrence store)) → @Bindings context sources contract rules store slots
  | [], _ => .nil
  | _ :: rest, bindings => .cons (bindings .here) (capture rest (fun old => bindings (.prior old)))

theorem Bindings.capture_read {context sources contract rules store slots spec}
    (bindings : {spec : Specification} → Ref slots spec → Option (Occurrence store)) (slot : Ref slots spec) :
    (@Bindings.capture context sources contract rules store slots bindings).read slot = bindings slot := by
  induction slot with
  | here => rfl
  | prior old ih => exact ih (fun prior => bindings (.prior prior))

theorem Bindings.read_capture {context sources contract rules store slots}
    (table : @Bindings context sources contract rules store slots) :
    Bindings.capture slots table.read = table := by
  induction table with
  | nil => rfl
  | cons head tail ih => exact congrArg (Bindings.cons head) ih

structure FrameData {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (slots : List Specification) where
  dossier : Dossier.State sources contract
  store : Deduction.Store sources contract rules
  bindings : Bindings store slots

def frame {context sources contract rules slots}
    (before : @Frame context sources contract rules slots) : FrameData sources contract rules slots :=
  ⟨before.dossier, before.store, Bindings.capture slots before.bindings⟩

def FrameData.restore {context sources contract rules slots}
    (data : @FrameData context sources contract rules slots) : Frame sources contract rules slots :=
  ⟨data.dossier, data.store, data.bindings.read⟩

theorem binding_exact {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots) (slot : Ref slots spec) :
    (frame before).restore.bindings slot = before.bindings slot := Bindings.capture_read before.bindings slot

theorem frame_roundtrip {context sources contract rules slots}
    (data : @FrameData context sources contract rules slots) : frame data.restore = data := by
  cases data with
  | mk dossier store bindings =>
      change FrameData.mk dossier store (Bindings.capture slots bindings.read) = _
      rw [Bindings.read_capture]

def complete_forward {context sources contract rules slots}
    (before : @Frame context sources contract rules slots) (complete : Complete before) : Complete (frame before).restore :=
  fun slot => let old := complete slot
    ⟨old.occurrence, (binding_exact before slot).trans old.actual, old.meets⟩

def complete_backward {context sources contract rules slots}
    (before : @Frame context sources contract rules slots) (complete : Complete (frame before).restore) : Complete before :=
  fun slot => let retained := complete slot
    ⟨retained.occurrence, (binding_exact before slot).symm.trans retained.actual, retained.meets⟩

structure SessionData {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (Context : Type) (slots : List Specification) where
  frame : FrameData sources contract rules slots
  context : Context
  round : Nat
  last : Option Summary

def session {context sources contract rules Context slots}
    (before : @Session context sources contract rules Context slots) : SessionData sources contract rules Context slots :=
  ⟨frame before.frame, before.context, before.round, before.last⟩

def SessionData.restore {context sources contract rules Context slots}
    (data : @SessionData context sources contract rules Context slots) : Session sources contract rules Context slots :=
  ⟨data.frame.restore, data.context, data.round, data.last⟩

theorem session_roundtrip {context sources contract rules Context slots}
    (data : @SessionData context sources contract rules Context slots) : session data.restore = data := by
  cases data with
  | mk frame context round last =>
      change SessionData.mk (Snapshot.frame frame.restore) context round last = _
      rw [frame_roundtrip]

structure PresentData {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (Context : Type) (final : List Specification) where
  slots : List Specification
  session : SessionData sources contract rules Context slots
  remaining : Script context rules slots final

def present {context sources contract rules Context final}
    (before : @Present context sources contract rules Context final) : PresentData sources contract rules Context final :=
  ⟨before.slots, session before.session, before.remaining⟩

def PresentData.restore {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) : Present sources contract rules Context final :=
  ⟨data.slots, data.session.restore, data.remaining⟩

theorem present_roundtrip {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) : present data.restore = data := by
  cases data with
  | mk slots session remaining =>
      change PresentData.mk slots (Snapshot.session session.restore) remaining = _
      rw [session_roundtrip]

structure Accomplishable {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) where
  initial : Complete data.session.frame.restore
  tasks : Program.Admissible sources contract data.remaining

def PresentData.reset {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) (policy : Adaptive.Policy Context) :
    PresentData sources contract rules Context final :=
  ⟨data.slots, ⟨data.session.frame, policy.reset data.session.context, data.session.round, data.session.last⟩,
    data.remaining⟩

theorem reset_keeps_work {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) (policy : Adaptive.Policy Context) :
    (data.reset policy).remaining.length = data.remaining.length ∧
      (data.reset policy).session.round = data.session.round := ⟨rfl, rfl⟩

/-- This payload keeps actual resource objects under the received configuration.
It is a typed checkpoint model; a byte codec and process/file effects belong to
the separate realization layer. The payload contains no interaction archive. -/
structure Checkpoint {context} (sources : Support SourceValue context)
    (contract : Contract) (rules : Deduction.Policy) (Context : Type) (final : List Specification) where
  version : Nat
  payload : PresentData sources contract rules Context final

def save {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) :
    Checkpoint sources contract rules Context final := ⟨1, data⟩

def load {context sources contract rules Context final}
    (checkpoint : @Checkpoint context sources contract rules Context final) :
    Option (PresentData sources contract rules Context final) :=
  if checkpoint.version == 1 then some checkpoint.payload else none

theorem checkpoint_roundtrip {context sources contract rules Context final}
    (data : @PresentData context sources contract rules Context final) : load (save data) = some data := rfl

theorem checkpoint_bad_version {context sources contract rules Context final}
    (checkpoint : @Checkpoint context sources contract rules Context final)
    (wrong : (checkpoint.version == 1) = false) : load checkpoint = none := by
  unfold load
  rw [wrong]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.Snapshot
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Bindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Bindings.read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Bindings.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Bindings.capture_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Bindings.read_capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.FrameData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.frame
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.FrameData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.binding_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.frame_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.complete_forward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.complete_backward
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.SessionData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.session
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.SessionData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.session_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.PresentData
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.PresentData.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.present_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Accomplishable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.PresentData.reset
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.reset_keeps_work
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.Checkpoint
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.checkpoint_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Snapshot.checkpoint_bad_version
/- AXIOM_AUDIT_END -/
