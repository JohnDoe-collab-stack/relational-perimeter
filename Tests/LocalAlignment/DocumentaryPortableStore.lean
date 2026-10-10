import Tests.LocalAlignment.DocumentaryCanonicalRestoration
import Tests.LocalAlignment.DocumentaryPortableCheckpoint

/-! Byte serialization of the canonical documentary store, with a distinct
schema. Configuration is received unchanged by the loader. This envelope does
not encode an adaptive session, queue, dossier memory or master cursor. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableStore
open Resources Portable CanonicalRestoration

inductive Error where
  | bytes | version | schema | header | store (reason : Portable.Error)

def envelope {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) : PortableCheckpoint.Saved :=
  ⟨1, 2, 0, 0, record store, [], 0⟩

def save {context sources contract policy}
    (store : @Deduction.Store context sources contract policy) : List UInt8 :=
  PortableCheckpoint.toBytes (PortableCheckpoint.encode (envelope store))

def load {context} (sources : Support SourceValue context) (contract : Contract)
    (policy : Deduction.Policy) (bytes : List UInt8) :
    Except Error (Deduction.Store sources contract policy) := do
  let saved ← match PortableCheckpoint.decode (PortableCheckpoint.fromBytes bytes) with
    | none => .error .bytes
    | some saved => .ok saved
  if saved.version != 1 then throw .version
  if saved.schema != 2 then throw .schema
  if saved.round != 0 || saved.depth != 0 || saved.task != 0 then throw .header
  match saved.bindings with
  | _ :: _ => throw .header
  | [] => (loadStore sources contract policy saved.nodes).mapError Error.store

/-- Equality includes the occurrence kinds, resource values, formation tree and
its producers, and the justification readers. It holds for every finite formed
store in this language under the same received configuration. -/
theorem byte_roundtrip {context sources contract policy store}
    (formed : @Formed context sources contract policy store) :
    load sources contract policy (save store) = .ok store := by
  unfold load save
  rw [PortableCheckpoint.physical_byte_codec_roundtrip]
  dsimp only [envelope, Bind.bind, Except.bind]
  change (loadStore sources contract policy (record store)).mapError Error.store = _
  rw [store_roundtrip formed]
  rfl

theorem execution_byte_roundtrip {context sources contract policy before after start script finish}
    (trace : @Program.Execution context sources contract policy before after start script finish)
    (initial : Formed sources contract policy start.store) :
    load sources contract policy (save finish.store) = .ok finish.store := by
  rcases execution_formed trace initial with ⟨formed⟩
  exact byte_roundtrip formed

/-- Any continuation that consumes this store alone receives exactly the same
store after the byte roundtrip. Full-present futures require the remaining
components to be restored as well. -/
theorem store_continuations {context sources contract policy store} {Result : Type}
    (formed : @Formed context sources contract policy store)
    (future : Deduction.Store sources contract policy → Result) :
    (load sources contract policy (save store)).map future = .ok (future store) := by
  rw [byte_roundtrip formed]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.PortableStore
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.Error
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.execution_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStore.store_continuations
/- AXIOM_AUDIT_END -/
