import Tests.LocalAlignment.DocumentaryCanonicalAdaptiveRestoration

/-! Restoration of the documentary dossier component. The received sources and
contract are unchanged. The decoder constructs the justification reader directly;
it does not execute extraction, incorporation, search or a historical master head.
This component does not encode a master cursor or an adaptive present. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableMemory
open Resources Program CanonicalRestoration

inductive Error where
  | bytes | version | schema | header | source | permission

def prepend {context sources contract} (memory : @Documentary.Memory context sources contract)
    (output : Output sources contract) : Documentary.Memory sources contract :=
  ⟨output.item :: memory.items, fun ref => match ref with
    | .here => output.evidence
    | .prior old => memory.valid old⟩

def record {context sources contract} (memory : @Documentary.Memory context sources contract) : List Nat :=
  memory.items.map Citation.position

def loadPositions {context} (sources : Support SourceValue context) (contract : Contract) :
    List Nat → Except Error (Documentary.Memory sources contract)
  | [] => .ok (Documentary.empty sources contract)
  | position :: rest => do
      let prior ← loadPositions sources contract rest
      let origin ← match Adaptive.locate context position with
        | none => .error .source
        | some origin => .ok origin
      let permission ← match resolvePermission contract.allowed origin.2.position with
        | none => .error .permission
        | some permission => .ok permission
      return prepend prior (canonicalOutput sources contract origin permission)

/-- Positive formation evidence for the actual dossier. Its reader retains the
source reference and the permission actually returned by the resolver. -/
inductive Formed {context} (sources : Support SourceValue context) (contract : Contract) :
    Documentary.Memory sources contract → Type where
  | empty : Formed sources contract (Documentary.empty sources contract)
  | cons {prior} (previous : Formed sources contract prior) (origin : Location context)
      (permission : Ref contract.allowed origin.2.position)
      (resolved : resolvePermission contract.allowed origin.2.position = some permission) :
      Formed sources contract (prepend prior (canonicalOutput sources contract origin permission))

theorem positions_roundtrip {context sources contract memory}
    (formed : @Formed context sources contract memory) :
    loadPositions sources contract (record memory) = .ok memory := by
  induction formed with
  | empty => rfl
  | @cons prior previous origin permission resolved ih =>
      change (do
        let restored ← loadPositions sources contract (record prior)
        let found ← match Adaptive.locate context origin.2.position with
          | none => .error .source
          | some found => .ok found
        let allowed ← match resolvePermission contract.allowed found.2.position with
          | none => .error .permission
          | some allowed => .ok allowed
        return prepend restored (canonicalOutput sources contract found allowed)) = _
      rw [ih, locate_reference origin.2]
      dsimp only [Bind.bind, Except.bind]
      rw [resolved]
      rfl

def packet_formed {context cursor sources contract demand left right stage memory}
    (previous : @Formed context sources contract memory)
    (packet : @Master.Completion context cursor sources contract demand left right stage memory) :
    Formed sources contract packet.result.1 := by
  rw [packet.resultExact, packet_output packet]
  exact .cons previous packet.candidate.origin packet.candidate.permission (packet_permission packet)

def dossier_step_formed {context sources contract state task}
    (previous : @Formed context sources contract state.memory)
    (produced : @Dossier.Step context sources contract state task) :
    Formed sources contract produced.next.memory :=
  match produced with
  | ⟨_, .complete packet⟩ => packet_formed previous packet
  | ⟨_, .blocked _ _⟩ => previous

def quotation_step_formed {context sources contract rules slots}
    (before : @Frame context sources contract rules slots)
    (previous : Formed sources contract before.dossier.memory) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) :
    Formed sources contract (Program.quotationStep before task produced).next.dossier.memory :=
  match produced with
  | ⟨_, .complete packet⟩ => packet_formed previous packet
  | ⟨_, .blocked _ _⟩ => previous

theorem program_step_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (previous : Formed sources contract before.dossier.memory)
    (instruction : Instruction context rules slots spec)
    (produced : Program.Step before instruction) (actual : produced = Program.step before instruction) :
    Nonempty (Formed sources contract produced.next.dossier.memory) := by
  cases actual
  cases instruction with
  | quotation task => exact ⟨quotation_step_formed before previous task (Dossier.step before.dossier task)⟩
  | conclusion request leftRef rightRef demand =>
      dsimp only [Program.step]
      split
      · exact ⟨previous⟩
      · rename_i leftOccurrence leftActual
        split
        · exact ⟨previous⟩
        · rename_i rightOccurrence rightActual
          cases Deduction.execute before.store.2 request leftOccurrence.2 rightOccurrence.2
          all_goals exact ⟨previous⟩

theorem program_execution_formed {context sources contract rules before after start script finish}
    (trace : @Program.Execution context sources contract rules before after start script finish)
    (initial : Formed sources contract start.dossier.memory) :
    Nonempty (Formed sources contract finish.dossier.memory) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons produced actual rest ih =>
      rcases program_step_formed _ initial _ produced actual with ⟨next⟩
      exact ih next

theorem fallback_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (previous : Formed sources contract before.dossier.memory)
    (instruction : Instruction context rules slots spec)
    (route : Adaptive.Route) (inspection : Option Adaptive.Readout) :
    Nonempty (Formed sources contract (Adaptive.fallback before instruction route inspection).next.dossier.memory) :=
  program_step_formed before previous instruction _ rfl

theorem diverted_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (previous : Formed sources contract before.dossier.memory)
    (instruction proposed : Instruction context rules slots spec) :
    Nonempty (Formed sources contract (Adaptive.diverted before instruction proposed).next.dossier.memory) := by
  rcases program_step_formed before previous proposed _ rfl with ⟨first⟩
  exact program_step_formed (Adaptive.dropHead (Program.step before proposed).next) first instruction _ rfl

theorem dispatch_formed {context sources contract rules slots spec}
    (before : @Frame context sources contract rules slots)
    (previous : Formed sources contract before.dossier.memory)
    (instruction : Instruction context rules slots spec) (proposal : Option Adaptive.Proposal) :
    Nonempty (Formed sources contract (Adaptive.dispatch before instruction proposal).next.dossier.memory) := by
  cases proposal with
  | none => exact fallback_formed before previous instruction _ _
  | some proposal =>
      cases proposal <;> cases instruction
      all_goals dsimp only [Adaptive.dispatch]
      all_goals repeat first
        | exact program_step_formed _ previous _ _ rfl
        | exact fallback_formed _ previous _ _ _
        | exact diverted_formed _ previous _ _
        | split

theorem turn_formed {context sources contract rules Context slots spec}
    (policy : Adaptive.Policy Context) (before : @Adaptive.Session context sources contract rules Context slots)
    (previous : Formed sources contract before.frame.dossier.memory)
    (signal : Adaptive.Signal) (instruction : Instruction context rules slots spec)
    (turn : Adaptive.Turn before instruction) (actual : turn = Adaptive.takeTurn policy before signal instruction) :
    Nonempty (Formed sources contract turn.next.frame.dossier.memory) := by
  cases actual
  exact dispatch_formed before.frame previous instruction (Adaptive.selection policy before signal instruction).2

theorem adaptive_execution_formed {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Formed sources contract start.frame.dossier.memory) :
    Nonempty (Formed sources contract finish.frame.dossier.memory) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons turn actual rest ih =>
      rcases turn_formed _ _ initial _ _ turn actual with ⟨next⟩
      exact ih next

theorem memory_step_formed {context sources contract rules Context final}
    (before : @Snapshot.PresentData context sources contract rules Context final)
    (previous : Formed sources contract before.session.frame.dossier.memory)
    (request : Memory.Request Context) (transition : Memory.Transition before request)
    (actual : transition = Memory.step before request) :
    Nonempty (Formed sources contract transition.next.session.frame.dossier.memory) := by
  cases actual
  cases request with
  | inspect index => exact ⟨previous⟩
  | status => exact ⟨previous⟩
  | reset policy => exact ⟨previous⟩
  | progress policy signal =>
      rcases before with ⟨slots, session, queue⟩
      cases queue with
      | done => exact ⟨previous⟩
      | cons instruction tail => exact turn_formed policy session.restore previous signal instruction _ rfl

theorem memory_execution_formed {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Formed sources contract before.session.frame.dossier.memory) :
    Nonempty (Formed sources contract finish.session.frame.dossier.memory) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons transition actual rest ih =>
      rcases memory_step_formed _ initial _ transition actual with ⟨next⟩
      exact ih next

def envelope {context sources contract}
    (memory : @Documentary.Memory context sources contract) : PortableCheckpoint.Saved :=
  ⟨1, 3, 0, 0, [], record memory, 0⟩

def save {context sources contract} (memory : @Documentary.Memory context sources contract) : List UInt8 :=
  PortableCheckpoint.toBytes (PortableCheckpoint.encode (envelope memory))

def load {context} (sources : Support SourceValue context) (contract : Contract) (bytes : List UInt8) :
    Except Error (Documentary.Memory sources contract) := do
  let saved ← match PortableCheckpoint.decode (PortableCheckpoint.fromBytes bytes) with
    | none => .error .bytes
    | some saved => .ok saved
  if saved.version != 1 then throw .version
  if saved.schema != 3 then throw .schema
  if saved.round != 0 || saved.depth != 0 || saved.task != 0 then throw .header
  match saved.nodes with
  | _ :: _ => throw .header
  | [] => loadPositions sources contract saved.bindings

theorem byte_roundtrip {context sources contract memory} (formed : @Formed context sources contract memory) :
    load sources contract (save memory) = .ok memory := by
  unfold load save
  rw [PortableCheckpoint.physical_byte_codec_roundtrip]
  dsimp only [envelope, Bind.bind, Except.bind]
  exact positions_roundtrip formed

theorem adaptive_execution_byte_roundtrip {context sources contract rules Context policy feed before after start script finish}
    (trace : @Adaptive.Execution context sources contract rules Context policy feed before after start script finish)
    (initial : Formed sources contract start.frame.dossier.memory) :
    load sources contract (save finish.frame.dossier.memory) = .ok finish.frame.dossier.memory := by
  rcases adaptive_execution_formed trace initial with ⟨formed⟩
  exact byte_roundtrip formed

theorem memory_execution_byte_roundtrip {context sources contract rules Context final before requests finish}
    (trace : @Memory.Execution context sources contract rules Context final before requests finish)
    (initial : Formed sources contract before.session.frame.dossier.memory) :
    load sources contract (save finish.session.frame.dossier.memory) = .ok finish.session.frame.dossier.memory := by
  rcases memory_execution_formed trace initial with ⟨formed⟩
  exact byte_roundtrip formed

theorem component_futures {context sources contract memory} {Result : Type u}
    (formed : @Formed context sources contract memory)
    (future : Documentary.Memory sources contract → Result) :
    (load sources contract (save memory)).map future = .ok (future memory) := by
  rw [byte_roundtrip formed]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.PortableMemory
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.Error
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.prepend
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.loadPositions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.positions_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.packet_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.dossier_step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.quotation_step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.program_step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.program_execution_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.fallback_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.diverted_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.dispatch_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.turn_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.adaptive_execution_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.memory_step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.memory_execution_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.adaptive_execution_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.memory_execution_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableMemory.component_futures
/- AXIOM_AUDIT_END -/
