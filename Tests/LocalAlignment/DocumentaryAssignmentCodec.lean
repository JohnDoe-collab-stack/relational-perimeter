import Tests.LocalAlignment.DocumentaryPortableAssignment

/-! Exact versioned bytes for a first-order assignment/reader recipe. Loading
only reconstructs the bundle's latent functions. This is a component codec,
not a SequentialAssignment validity checker or a complete master checkpoint. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec
open PortableAssignment

def fields : Command → Nat × Option Nat
  | .visit => (0, none)
  | .flip selected => (1, some selected)

def readCommand (data : Nat × Option Nat) : Option Command :=
  match data.1 with
  | 0 => match data.2 with | none => some .visit | some _ => none
  | 1 => match data.2 with | none => none | some selected => some (.flip selected)
  | _ => none

theorem command_exact (value : Command) : readCommand (fields value) = some value := by
  cases value <;> rfl

def command : ControlCodec.Codec Command :=
  (ControlCodec.natural.product ControlCodec.natural.optional).via fields readCommand command_exact

def codes : ControlCodec.Codec Code := command.list

def envelope : ControlCodec.Codec Code :=
  (ControlCodec.natural.product (ControlCodec.natural.product codes)).via
    (fun code => (88, 1, code))
    (fun data => match data.1 with
      | 88 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none)
    (fun _ => rfl)

def save (code : Code) : List UInt8 := ControlCodec.bytes (envelope.words code)

def load (bytes : List UInt8) : Option Code := do
  let words ← ControlCodec.fromBytes bytes
  let (code, tail) ← envelope.read words
  match tail with | [] => some code | _ :: _ => none

theorem byte_roundtrip (code : Code) : load (save code) = some code := by
  unfold load save
  rw [ControlCodec.bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact code []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

def restore (bytes : List UInt8) : Option Bundle := (load bytes).map interpret

theorem formed_roundtrip {value} (formed : Formed value) :
    restore (save (capture formed)) = some value := by
  unfold restore
  rw [byte_roundtrip]
  change some (interpret (capture formed)) = some value
  rw [capture_exact]

theorem all_loaded_consumers {value} (formed : Formed value) {Result : Type u}
    (future : Bundle → Result) :
    (restore (save (capture formed))).map future = some (future value) := by
  rw [formed_roundtrip]
  rfl

theorem all_loaded_queries {value} (formed : Formed value) (queries : List SAT.Var) :
    (restore (save (capture formed))).map (fun data => readQueries data queries) =
      some (readQueries value queries) :=
  all_loaded_consumers formed (fun data => readQueries data queries)

end ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.fields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.readCommand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.command_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.command
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.codes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.formed_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.all_loaded_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.AssignmentCodec.all_loaded_queries
/- AXIOM_AUDIT_END -/
