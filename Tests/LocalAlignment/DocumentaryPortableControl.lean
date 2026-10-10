import Tests.LocalAlignment.DocumentaryControlCodec
import Tests.LocalAlignment.DocumentaryCanonicalRestoration

/-! Portable control of an actual retained present. Loading resolves exact ports,
including absent bindings and permitted outputs that miss their goals. Reference
reconstruction calls no task, master head, extraction or deduction. Context
decoding is delegated to the received codec. The documentary store and
dossier/master are supplied components, not hidden byte payloads. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableControl
open Resources Program Adaptive ControlCodec

def binding {context sources contract rules store}
    (value : Option (@Occurrence context sources contract rules store)) : Option Nat :=
  value.map (fun found => found.2.position)

def loadBinding {context sources contract rules}
    (store : @Deduction.Store context sources contract rules) : Option Nat → Option (Option (Occurrence store))
  | none => some none
  | some position => (Adaptive.locate store.1 position).map some

theorem binding_exact {context sources contract rules store}
    (value : Option (@Occurrence context sources contract rules store)) :
    loadBinding store (binding value) = some value := by
  cases value with
  | none => rfl
  | some value =>
      change (Adaptive.locate store.1 value.2.position).map some = _
      rw [CanonicalRestoration.locate_reference]
      rfl

def bindings {context sources contract rules store slots}
    (table : @Snapshot.Bindings context sources contract rules store slots) : List (Option Nat) :=
  match table with
  | .nil => []
  | .cons head tail => binding head :: bindings tail

def loadBindings {context sources contract rules}
    (store : @Deduction.Store context sources contract rules) :
    (slots : List Specification) → List (Option Nat) → Option (Snapshot.Bindings store slots)
  | [], [] => some .nil
  | [], _ :: _ => none
  | _ :: _, [] => none
  | _ :: rest, position :: positions => do
      let head ← loadBinding store position
      let tail ← loadBindings store rest positions
      return .cons head tail

theorem bindings_exact {context sources contract rules store slots}
    (table : @Snapshot.Bindings context sources contract rules store slots) :
    loadBindings store slots (bindings table) = some table := by
  induction table with
  | nil => rfl
  | cons head tail ih =>
      change (do let head ← loadBinding store (binding head)
                 let tail ← loadBindings store _ (bindings tail)
                 pure (Snapshot.Bindings.cons head tail)) = _
      rw [binding_exact]
      change (do let tail ← loadBindings store _ (bindings tail)
                 pure (Snapshot.Bindings.cons head tail)) = _
      rw [ih]
      rfl

def instruction {context rules slots spec}
    (value : Instruction context rules slots spec) : Command :=
  match value with
  | .quotation task => .quotation task.demand task.left.2.position task.right.2.position
  | .conclusion request left right demand => .conclusion request.2.position left.position right.position demand

def loadInstruction (context : List SourceKey) (rules : Deduction.Policy) (slots : List Specification) :
    Command → Option ((spec : Specification) × Instruction context rules slots spec)
  | .quotation demand left right => do
      let leftRef ← Adaptive.locate context left
      let rightRef ← Adaptive.locate context right
      return ⟨.quotation demand, .quotation ⟨demand, leftRef, rightRef⟩⟩
  | .conclusion rule left right demand => do
      let request ← Adaptive.locate rules.rules rule
      let leftRef ← Adaptive.locate slots left
      let rightRef ← Adaptive.locate slots right
      return ⟨.conclusion demand, .conclusion request leftRef.2 rightRef.2 demand⟩

theorem instruction_exact {context rules slots spec}
    (value : Instruction context rules slots spec) :
    loadInstruction context rules slots (instruction value) = some ⟨spec, value⟩ := by
  cases value with
  | quotation task =>
      change (do let left ← Adaptive.locate context task.left.2.position
                 let right ← Adaptive.locate context task.right.2.position
                 pure (Sigma.mk (Specification.quotation task.demand) (Instruction.quotation ⟨task.demand, left, right⟩))) = _
      rw [CanonicalRestoration.locate_reference]
      change (do let right ← Adaptive.locate context task.right.2.position
                 pure (Sigma.mk (Specification.quotation task.demand) (Instruction.quotation ⟨task.demand, task.left, right⟩))) = _
      rw [CanonicalRestoration.locate_reference]
      cases task
      rfl
  | conclusion request left right demand =>
      change (do let rule ← Adaptive.locate rules.rules request.2.position
                 let leftRef ← Adaptive.locate slots left.position
                 let rightRef ← Adaptive.locate slots right.position
                 pure (Sigma.mk (Specification.conclusion demand) (Instruction.conclusion rule leftRef.2 rightRef.2 demand))) = _
      rw [CanonicalRestoration.locate_reference]
      change (do let leftRef ← Adaptive.locate slots left.position
                 let rightRef ← Adaptive.locate slots right.position
                 pure (Sigma.mk (Specification.conclusion demand) (Instruction.conclusion request leftRef.2 rightRef.2 demand))) = _
      rw [CanonicalRestoration.locate_reference]
      change (do let rightRef ← Adaptive.locate slots right.position
                 pure (Sigma.mk (Specification.conclusion demand) (Instruction.conclusion request left rightRef.2 demand))) = _
      rw [CanonicalRestoration.locate_reference]
      rfl

def script {context rules before after} (value : Script context rules before after) : List Command :=
  match value with | .done => [] | .cons head tail => instruction head :: script tail

def loadScript (context : List SourceKey) (rules : Deduction.Policy) :
    (before : List Specification) → List Command →
      Option ((after : List Specification) × Script context rules before after)
  | before, [] => some ⟨before, .done⟩
  | before, head :: tail => do
      let first ← loadInstruction context rules before head
      let rest ← loadScript context rules (first.1 :: before) tail
      return ⟨rest.1, .cons first.2 rest.2⟩

theorem script_exact {context rules before after} (value : Script context rules before after) :
    loadScript context rules before (script value) = some ⟨after, value⟩ := by
  induction value with
  | done => rfl
  | cons head tail ih =>
      change (do let first ← loadInstruction context rules _ (instruction head)
                 let rest ← loadScript context rules _ (script tail)
                 pure (Sigma.mk rest.1 (Script.cons first.2 rest.2))) = _
      rw [instruction_exact]
      change (do let rest ← loadScript context rules _ (script tail)
                 pure (Sigma.mk rest.1 (Script.cons head rest.2))) = _
      rw [ih]
      rfl

structure Data {context sources contract rules}
    (store : @Deduction.Store context sources contract rules) (Context : Type) (final : List Specification) where
  slots : List Specification
  bindings : Snapshot.Bindings store slots
  remaining : Script context rules slots final
  context : Context
  round : Nat
  last : Option Summary

def record {context sources contract rules store Context final}
    (value : @Data context sources contract rules store Context final) : Raw Context :=
  ⟨value.slots, bindings value.bindings, script value.remaining, value.context, value.round, value.last⟩

def restore {context sources contract rules Context}
    (store : @Deduction.Store context sources contract rules) (final : List Specification) (value : Raw Context) :
    Option (Data store Context final) := do
  let table ← loadBindings store value.slots value.bindings
  let tasks ← loadScript context rules value.slots value.remaining
  letI : DecidableEq (List Specification) := specification.list.equality
  if same : tasks.1 = final then
    return ⟨value.slots, table, same ▸ tasks.2, value.context, value.round, value.last⟩
  else none

theorem record_exact {context sources contract rules store Context final}
    (value : @Data context sources contract rules store Context final) :
    restore store final (record value) = some value := by
  letI : DecidableEq (List Specification) := specification.list.equality
  cases value with
  | mk slots table remaining ctx round last =>
      unfold restore record
      rw [bindings_exact]
      change (do let tasks ← loadScript context rules slots (script remaining)
                 if same : tasks.1 = final then
                   pure (Data.mk slots table (same ▸ tasks.2) ctx round last)
                 else none) = _
      rw [script_exact]
      change (if same : final = final then
                some (Data.mk slots table (same ▸ remaining) ctx round last)
              else none) = _
      rw [dif_pos rfl]

def save {context sources contract rules store Context final} (codec : Codec Context)
    (value : @Data context sources contract rules store Context final) : List UInt8 :=
  ControlCodec.save codec (record value)

def load {context sources contract rules Context} (codec : Codec Context)
    (store : @Deduction.Store context sources contract rules) (final : List Specification) (bytes : List UInt8) :
    Option (Data store Context final) := do
  let value ← ControlCodec.load codec bytes
  restore store final value

theorem byte_roundtrip {context sources contract rules store Context final} (codec : Codec Context)
    (value : @Data context sources contract rules store Context final) :
    load codec store final (save codec value) = some value := by
  unfold load save
  rw [ControlCodec.byte_roundtrip]
  exact record_exact value

def capture {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final) :
    Data before.session.frame.store Context final :=
  ⟨before.slots, before.session.frame.bindings, before.remaining,
    before.session.context, before.session.round, before.session.last⟩

def Data.present {context sources contract rules store Context final}
    (value : @Data context sources contract rules store Context final) (dossier : Dossier.State sources contract) :
    Snapshot.PresentData sources contract rules Context final :=
  ⟨value.slots, ⟨⟨dossier, store, value.bindings⟩, value.context, value.round, value.last⟩, value.remaining⟩

theorem capture_exact {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final) :
    (capture before).present before.session.frame.dossier = before := by
  cases before with
  | mk slots session remaining =>
      cases session with
      | mk frame ctx round last => cases frame; rfl

/-- This joins loaded control with the supplied actual dossier and store. It is
a control-component realization, not a complete-present byte loader. -/
def loadPresent {context sources contract rules Context} (codec : Codec Context)
    (dossier : @Dossier.State context sources contract)
    (store : Deduction.Store sources contract rules) (final : List Specification) (bytes : List UInt8) :
    Option (Snapshot.PresentData sources contract rules Context final) :=
  (load codec store final bytes).map (fun value => value.present dossier)

theorem present_byte_roundtrip {context sources contract rules Context final} (codec : Codec Context)
    (before : @Snapshot.PresentData context sources contract rules Context final) :
    loadPresent codec before.session.frame.dossier before.session.frame.store final (save codec (capture before)) =
      some before := by
  unfold loadPresent
  rw [byte_roundtrip]
  exact congrArg some (capture_exact before)

theorem loaded_all_futures {context sources contract rules Context final} (codec : Codec Context)
    (before after : @Snapshot.PresentData context sources contract rules Context final)
    (loaded : loadPresent codec before.session.frame.dossier before.session.frame.store final
      (save codec (capture before)) = some after) (requests : List (Memory.Request Context)) :
    HEq (Memory.run after requests) (Memory.run before requests) := by
  have same := Option.some.inj ((present_byte_roundtrip codec before).symm.trans loaded)
  cases same
  rfl

def loaded_accomplishable {context sources contract rules Context final} (codec : Codec Context)
    (before after : @Snapshot.PresentData context sources contract rules Context final)
    (loaded : loadPresent codec before.session.frame.dossier before.session.frame.store final
      (save codec (capture before)) = some after) (possible : Snapshot.Accomplishable before) :
    Snapshot.Accomplishable after :=
  (Option.some.inj ((present_byte_roundtrip codec before).symm.trans loaded)) ▸ possible

end ConstitutiveSearch.Agent.Local.Documentary.PortableControl

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.binding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loadBinding
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.binding_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.bindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loadBindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.bindings_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.instruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loadInstruction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.instruction_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.script
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loadScript
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.script_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.Data
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.record_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.Data.present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.capture_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loadPresent
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.present_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loaded_all_futures
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableControl.loaded_accomplishable
/- AXIOM_AUDIT_END -/
