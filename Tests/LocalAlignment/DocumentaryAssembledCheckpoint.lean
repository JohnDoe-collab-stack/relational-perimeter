import Tests.LocalAlignment.DocumentaryStateCapture
import Tests.LocalAlignment.DocumentaryMasterPayload
import Tests.LocalAlignment.DocumentaryPortableStore
import Tests.LocalAlignment.DocumentaryPortableMemory
import Tests.LocalAlignment.DocumentaryPortableControl

/-! A concrete assembled checkpoint with a typed master-formation payload and
one byte envelope for its decoded current source, store, documentary memory
and complete control. Loading supplies no old cursor/store/memory/session.
The remaining master values and producer environments are still typed data:
this assembled checkpoint is not a complete-master byte codec. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint
open Resources EndogenousDecomposition Program ControlCodec

universe u v

def putValues {Kind : Type u} {Value : Kind → Type v} {kinds kind}
    (port : Ref kinds kind) (values : Values Value kinds) (value : Value kind) :
    Values Value kinds :=
  match port with
  | .here => (value, values.2)
  | .prior port => (values.1, putValues port values.2 value)

theorem put_values_exact {Kind : Type u} {Value : Kind → Type v} {kinds kind}
    (port : Ref kinds kind) (values : Values Value kinds) (value : Value kind)
    (same : value = Resources.read values port) : putValues port values value = values := by
  induction port with
  | here => cases values; cases same; rfl
  | prior port ih => exact congrArg (Prod.mk values.1) (ih values.2 value same)

def putSupport {Kind : Type u} {Value : Kind → Type v} {kinds kind}
    (support : Support Value kinds) (port : Ref kinds kind) (value : Value kind)
    (same : value = support.read port) : Support Value kinds :=
  let changed := putValues port support.values value
  ⟨changed, Eq.rec (motive := fun values _ => Formation Value values)
    support.formation (put_values_exact port support.values value same).symm⟩

theorem support_fields_exact {Kind : Type u} {Value : Kind → Type v} {kinds}
    (old changed : Values Value kinds) (same : old = changed) (formation : Formation Value old) :
    (⟨changed, same ▸ formation⟩ : Support Value kinds) = ⟨old, formation⟩ := by
  cases same
  rfl

theorem put_support_exact {Kind : Type u} {Value : Kind → Type v} {kinds kind}
    (support : Support Value kinds) (port : Ref kinds kind) (value : Value kind)
    (same : value = support.read port) : putSupport support port value same = support := by
  exact support_fields_exact support.values (putValues port support.values value)
    (put_values_exact port support.values value same).symm support.formation

/-- This projection incorporates the decoded fields; its old-state argument is
used only to state the dependent equality certificate. -/
def decodedState {depth assignment} (expected : ThreadedConstitutiveState depth assignment)
    (loaded : StatePortable.Loaded) (same : loaded = ⟨depth, assignment, expected⟩) :
    ThreadedConstitutiveState depth assignment :=
  Eq.rec (motive := fun value _ => ThreadedConstitutiveState value.1 value.2.1) loaded.2.2 same

theorem decoded_state_exact {depth assignment} (expected : ThreadedConstitutiveState depth assignment)
    (loaded : StatePortable.Loaded) (same : loaded = ⟨depth, assignment, expected⟩) :
    decodedState expected loaded same = expected := by
  cases same
  rfl

def cursorFields (before : MasterResources.Cursor) (support : Support MasterResources.Value before.kinds)
    (supportExact : support = before.support) :
    MasterResources.Cursor :=
  have stateExact : (support.read before.source).down = before.state := by rw [supportExact]; rfl
  { depth := before.depth
    assignment := before.assignment
    kinds := before.kinds
    support := support
    source := before.source
    past := stateExact.symm ▸ before.past
    fresh := stateExact.symm ▸ before.fresh }

theorem cursor_fields_exact (before : MasterResources.Cursor)
    (support : Support MasterResources.Value before.kinds) (same : support = before.support) :
    cursorFields before support same = before := by
  cases before
  cases same
  rfl

def putSource (before : MasterResources.Cursor)
    (state : ThreadedConstitutiveState before.depth before.assignment) (same : state = before.state) :
    MasterResources.Cursor :=
  cursorFields before (putSupport before.support before.source (ULift.up state) (congrArg ULift.up same))
    (put_support_exact _ _ _ _)

theorem put_source_exact (before : MasterResources.Cursor)
    (state : ThreadedConstitutiveState before.depth before.assignment) (same : state = before.state) :
    putSource before state same = before := by
  exact cursor_fields_exact _ _ _

structure Sections where
  source : List UInt8
  store : List UInt8
  memory : List UInt8
  control : List UInt8

def octet : Codec UInt8 :=
  natural.via UInt8.toNat
    (fun value => if bounded : value < 256 then some (UInt8.ofNatLT value bounded) else none)
    (fun value => by
      cases value with
      | ofBitVec vector =>
          cases vector with
          | ofFin number =>
              cases number with
              | mk value bounded =>
                  change (if proof : value < 256 then some (UInt8.ofNatLT value proof) else none) = _
                  rw [dif_pos bounded]
                  rfl)

def sectionsCodec : Codec Sections :=
  (octet.list.product (octet.list.product (octet.list.product octet.list))).via
    (fun value => (value.source, value.store, value.memory, value.control))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (fun value => by cases value; rfl)

def envelope : Codec Sections :=
  (natural.product (natural.product sectionsCodec)).via
    (fun value => (94, 1, value))
    (fun data => match data.1 with
      | 94 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none) (fun _ => rfl)

def saveSections (value : Sections) : List UInt8 := bytes (envelope.words value)

def loadSections (input : List UInt8) : Option Sections := do
  let words ← fromBytes input
  let (value, tail) ← envelope.read words
  match tail with | [] => some value | _ :: _ => none

theorem sections_byte_roundtrip (value : Sections) : loadSections (saveSections value) = some value := by
  unfold loadSections saveSections
  rw [bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact value []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

structure Packet : Type 3 where
  master : MasterPayload.CursorData
  reader : SequentialPortable.Formed master.restore.assignment
  wire : List UInt8
  sourceExact : ∀ sections, loadSections wire = some sections →
    sections.source = StatePortable.save master.restore.state reader

def restoreMaster (packet : Packet) (sections : Sections)
    (actual : loadSections packet.wire = some sections) : Option MasterResources.Cursor :=
  match loaded : StatePortable.restore sections.source with
  | none => none
  | some value =>
      have valueExact : value =
          (⟨packet.master.restore.depth, packet.master.restore.assignment, packet.master.restore.state⟩ :
            StatePortable.Loaded) := by
        have exact := StatePortable.restored_exact packet.master.restore.state packet.reader
        rw [← packet.sourceExact sections actual] at exact
        exact Option.some.inj (loaded.symm.trans exact)
      let source := decodedState packet.master.restore.state value valueExact
      some (putSource packet.master.restore source (decoded_state_exact _ _ _))

theorem restore_master_exact (packet : Packet) (sections : Sections)
    (actual : loadSections packet.wire = some sections) :
    restoreMaster packet sections actual = some packet.master.restore := by
  unfold restoreMaster
  have exact := StatePortable.restored_exact packet.master.restore.state packet.reader
  rw [← packet.sourceExact sections actual] at exact
  split
  · rename_i missing
    rw [missing] at exact
    cases exact
  · dsimp only
    rw [put_source_exact]

def restore {context} (sources : Support SourceValue context) (contract : Contract)
    (rules : Deduction.Policy) {Context : Type} (codec : Codec Context) (final : List Specification)
    (packet : Packet) : Option (Snapshot.PresentData sources contract rules Context final) :=
  match actual : loadSections packet.wire with
  | none => none
  | some sections =>
      match restoreMaster packet sections actual with
      | none => none
      | some master =>
          match PortableStore.load sources contract rules sections.store with
          | .error _ => none
          | .ok store =>
              match PortableMemory.load sources contract sections.memory with
              | .error _ => none
              | .ok memory =>
                  match PortableControl.load codec store final sections.control with
                  | none => none
                  | some control => some (control.present ⟨master, memory⟩)

def sections {context sources contract rules Context final} (codec : Codec Context)
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor) : Sections :=
  ⟨StateCapture.save before.session.frame.dossier.cursor ready,
    PortableStore.save before.session.frame.store, PortableMemory.save before.session.frame.dossier.memory,
    PortableControl.save codec (PortableControl.capture before)⟩

def capture {context sources contract rules Context final} (codec : Codec Context)
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor) : Packet :=
  let master := MasterPayload.cursor before.session.frame.dossier.cursor
  have masterExact : master.restore = before.session.frame.dossier.cursor := MasterPayload.cursor_exact _
  let reader : SequentialPortable.Formed master.restore.assignment :=
    { code := AssignmentCapture.cursor before.session.frame.dossier.cursor
      safe := by rw [masterExact]; exact ready.2
      exact := by rw [masterExact]; exact ready.1 }
  { master := master
    reader := reader
    wire := saveSections (sections codec before ready)
    sourceExact := by
      intro loaded actual
      have same := Option.some.inj ((sections_byte_roundtrip (sections codec before ready)).symm.trans actual)
      cases same
      change StateCapture.save before.session.frame.dossier.cursor ready =
        StatePortable.save master.restore.state reader
      unfold StateCapture.save StatePortable.save StatePortable.capture SequentialCapture.formed
      dsimp only [reader]
      rw [masterExact] }

theorem restored_exact {context sources contract rules Context final} (codec : Codec Context)
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor)
    (store : CanonicalRestoration.Formed sources contract rules before.session.frame.store)
    (memory : PortableMemory.Formed sources contract before.session.frame.dossier.memory) :
    restore sources contract rules codec final (capture codec before ready) = some before := by
  unfold restore
  have loaded := sections_byte_roundtrip (sections codec before ready)
  change loadSections (capture codec before ready).wire = some (sections codec before ready) at loaded
  split
  · rename_i missing
    rw [missing] at loaded
    cases loaded
  · rename_i loadedSections actual
    have same := Option.some.inj (actual.symm.trans loaded)
    cases same
    rw [restore_master_exact]
    change (match PortableStore.load sources contract rules (PortableStore.save before.session.frame.store) with
      | .error _ => none
      | .ok decodedStore =>
          match PortableMemory.load sources contract (PortableMemory.save before.session.frame.dossier.memory) with
          | .error _ => none
          | .ok decodedMemory =>
              match PortableControl.load codec decodedStore final
                (PortableControl.save codec (PortableControl.capture before)) with
              | none => none
              | some control => some (control.present
                  ⟨(MasterPayload.cursor before.session.frame.dossier.cursor).restore, decodedMemory⟩)) = _
    rw [PortableStore.byte_roundtrip store, PortableMemory.byte_roundtrip memory]
    dsimp only
    rw [PortableControl.byte_roundtrip]
    dsimp only
    rw [MasterPayload.cursor_exact]
    exact congrArg some (PortableControl.capture_exact before)

theorem all_futures {context sources contract rules Context final} (codec : Codec Context)
    (before after : @Snapshot.PresentData context sources contract rules Context final)
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor)
    (store : CanonicalRestoration.Formed sources contract rules before.session.frame.store)
    (memory : PortableMemory.Formed sources contract before.session.frame.dossier.memory)
    (loaded : restore sources contract rules codec final (capture codec before ready) = some after)
    (requests : List (Memory.Request Context)) :
    HEq (Memory.run after requests) (Memory.run before requests) := by
  have same := Option.some.inj ((restored_exact codec before ready store memory).symm.trans loaded)
  cases same
  rfl

def accomplishment {context sources contract rules Context final} (codec : Codec Context)
    (before after : @Snapshot.PresentData context sources contract rules Context final)
    (ready : SequentialCapture.Ready before.session.frame.dossier.cursor)
    (store : CanonicalRestoration.Formed sources contract rules before.session.frame.store)
    (memory : PortableMemory.Formed sources contract before.session.frame.dossier.memory)
    (loaded : restore sources contract rules codec final (capture codec before ready) = some after)
    (possible : Snapshot.Accomplishable before) : Snapshot.Accomplishable after :=
  (Option.some.inj ((restored_exact codec before ready store memory).symm.trans loaded)) ▸ possible

end ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.putValues
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.put_values_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.putSupport
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.support_fields_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.put_support_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.decodedState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.decoded_state_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.cursorFields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.cursor_fields_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.putSource
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.put_source_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.Sections
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.octet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.sectionsCodec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.saveSections
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.loadSections
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.sections_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.restoreMaster
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.restore_master_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.sections
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.all_futures
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssembledCheckpoint.accomplishment
/- AXIOM_AUDIT_END -/
