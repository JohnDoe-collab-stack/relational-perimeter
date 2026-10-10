import Tests.LocalAlignment.DocumentaryGenerationPortable
import Tests.LocalAlignment.DocumentarySequentialPortable

/-! Complete threaded-state bytes: dependent assignment and measured reader,
generation, search seed, ordered decisions and provenance. The loader receives
no retained state. Decision validation is a finite calculation on code and
stored Boolean decisions; it does not query the latent measured reader. -/
set_option genInjectivity false
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.StatePortable
open Resources EndogenousDecomposition PortableAssignment ControlCodec SAT

def bit : Code → Var → Bool
  | [], query => alternatingAssignmentBit query
  | .visit :: prior, query => bit prior query
  | .flip selected :: prior, query =>
      if query = selected then !(bit prior query) else bit prior query

theorem bit_exact (code : Code) (query : Var) :
    bit code query = (interpret code).assignment query := by
  induction code with
  | nil => rfl
  | cons command prior ih =>
      cases command with
      | visit => exact ih
      | flip selected =>
          change (if query = selected then !(bit prior query) else bit prior query) =
            Assignment.flipAt selected (interpret prior).assignment query
          unfold Assignment.flipAt
          rw [ih]

def Holds (code : Code) : List StructuralBranchDecision → Prop
  | [] => True
  | decision :: rest => bit code decision.var = decision.value ∧ Holds code rest

instance holdsDecidable (code : Code) (decisions : List StructuralBranchDecision) :
    Decidable (Holds code decisions) :=
  match decisions with
  | [] => .isTrue True.intro
  | decision :: rest =>
      let prior : Decidable (Holds code rest) := holdsDecidable code rest
      @instDecidableAnd _ _ (inferInstance : Decidable (bit code decision.var = decision.value)) prior

theorem holds_exact (code : Code) (decisions : List StructuralBranchDecision)
    (actual : Holds code decisions) :
    StructuralDecisionsHold (interpret code).assignment decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest ih => exact ⟨(bit_exact code decision.var).symm.trans actual.1, ih actual.2⟩

theorem holds_of_exact (code : Code) (decisions : List StructuralBranchDecision)
    (actual : StructuralDecisionsHold (interpret code).assignment decisions) :
    Holds code decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest ih => exact ⟨(bit_exact code decision.var).trans actual.1, ih actual.2⟩

structure Record where
  depth : Nat
  assignment : Code
  generation : GenerationPortable.Record
  searchSeed : Nat
  decisions : List StructuralBranchDecision
  provenance : List Var

def capture {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) : Record :=
  ⟨depth, formed.code, GenerationPortable.capture state.generation, state.searchSeed,
    state.decisions, state.provenance⟩

abbrev Loaded := (depth : Nat) × (assignment : SequentialAssignment depth) ×
  ThreadedConstitutiveState depth assignment

def fields (depth : Nat) (code : Code) (safe : SequentialPortable.Safe depth code)
    (generation : CanonicalStageGeneration depth) (seed : Nat)
    (seedExact : seed = generatedSearchSeed generation)
    (decisions : List StructuralBranchDecision) (provenance : List Var)
    (provenanceExact : provenance = decisions.map (fun decision => decision.var))
    (holds : Holds code decisions) : ThreadedConstitutiveState depth (SequentialPortable.assemble depth code safe) :=
  { threadedAssignment := SequentialPortable.assemble depth code safe
    threadedAssignmentExact := rfl
    generation := generation
    searchSeed := seed
    searchSeedExact := seedExact
    decisions := decisions
    provenance := provenance
    provenanceExact := provenanceExact
    decisionsHold := holds_exact code decisions holds }

def validate (record : Record) : Option Loaded :=
  if safe : SequentialPortable.Safe record.depth record.assignment then do
    let generation ← GenerationPortable.restoreRecord record.depth record.generation
    if seedExact : record.searchSeed = generatedSearchSeed generation then
      if provenanceExact : record.provenance = record.decisions.map (fun decision => decision.var) then
        if holds : Holds record.assignment record.decisions then
          return ⟨record.depth, SequentialPortable.assemble record.depth record.assignment safe,
            fields record.depth record.assignment safe generation record.searchSeed seedExact
              record.decisions record.provenance provenanceExact holds⟩
        else none
      else none
    else none
  else none

theorem coupled_equal {depth left right}
    (decoded : ThreadedConstitutiveState depth left) (before : ThreadedConstitutiveState depth right)
    (assignment : left = right) (generation : decoded.generation = before.generation)
    (seed : decoded.searchSeed = before.searchSeed) (decisions : decoded.decisions = before.decisions)
    (provenance : decoded.provenance = before.provenance) :
    (⟨depth, left, decoded⟩ : Loaded) = ⟨depth, right, before⟩ := by
  cases assignment
  cases decoded with
  | mk da de dg ds dse dd dp dpe dh =>
      cases before with
      | mk ba be bg bs bse bd bp bpe bh =>
          cases de
          cases be
          cases generation
          cases seed
          cases decisions
          cases provenance
          rfl

theorem fields_exact {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment)
    (holds : Holds formed.code state.decisions) :
    (⟨depth, SequentialPortable.assemble depth formed.code formed.safe,
      fields depth formed.code formed.safe state.generation state.searchSeed state.searchSeedExact
        state.decisions state.provenance state.provenanceExact holds⟩ : Loaded) =
      ⟨depth, assignment, state⟩ := by
  exact coupled_equal _ state (SequentialPortable.assembled_exact formed) rfl rfl rfl rfl

theorem record_exact {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) :
    validate (capture state formed) = some (⟨depth, assignment, state⟩ : Loaded) := by
  have holds : Holds formed.code state.decisions := by
    apply holds_of_exact
    rw [formed.exact]
    exact state.decisionsHold
  unfold validate capture
  rw [dif_pos formed.safe]
  rw [GenerationPortable.record_exact]
  change (if seedExact : state.searchSeed = generatedSearchSeed state.generation then
    if provenanceExact : state.provenance = state.decisions.map (fun decision => decision.var) then
      if actual : Holds formed.code state.decisions then
        some (⟨depth, SequentialPortable.assemble depth formed.code formed.safe,
          fields depth formed.code formed.safe state.generation state.searchSeed seedExact
            state.decisions state.provenance provenanceExact actual⟩ : Loaded)
      else none
    else none
    else none) = _
  rw [dif_pos state.searchSeedExact, dif_pos state.provenanceExact, dif_pos holds, fields_exact]

def boolean : Codec Bool :=
  natural.via (fun value => match value with | false => 0 | true => 1)
    (fun value => match value with | 0 => some false | 1 => some true | _ + 2 => none)
    (fun value => by cases value <;> rfl)

def decision : Codec StructuralBranchDecision :=
  (natural.product boolean).via
    (fun value => (value.var, value.value))
    (fun value => some ⟨value.1, value.2⟩) (fun value => by cases value; rfl)

def recordCodec : Codec Record :=
  (natural.product (AssignmentCodec.codes.product (GenerationPortable.recordCodec.product
    (natural.product (decision.list.product natural.list))))).via
    (fun value => (value.depth, value.assignment, value.generation, value.searchSeed,
      value.decisions, value.provenance))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2⟩) (fun value => by cases value; rfl)

def envelope : Codec Record :=
  (natural.product (natural.product recordCodec)).via
    (fun value => (93, 1, value))
    (fun data => match data.1 with
      | 93 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none) (fun _ => rfl)

def save {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) : List UInt8 :=
  bytes (envelope.words (capture state formed))

def load (input : List UInt8) : Option Record := do
  let words ← fromBytes input
  let (record, tail) ← envelope.read words
  match tail with | [] => some record | _ :: _ => none

def restore (input : List UInt8) : Option Loaded := (load input).bind validate

theorem record_byte_roundtrip (record : Record) :
    load (bytes (envelope.words record)) = some record := by
  unfold load
  rw [bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact record []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

theorem byte_roundtrip {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) :
    load (save state formed) = some (capture state formed) := by
  unfold load save
  rw [bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact (capture state formed) []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

theorem restored_exact {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) :
    restore (save state formed) = some (⟨depth, assignment, state⟩ : Loaded) := by
  unfold restore
  rw [byte_roundtrip]
  exact record_exact state formed

theorem all_consumers {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) {Result : Type u} (future : Loaded → Result) :
    (restore (save state formed)).map future = some (future ⟨depth, assignment, state⟩) := by
  rw [restored_exact]
  rfl

/-- Freshness remains a separate admission test for executing a next stage. -/
def Fresh (depth : Nat) : List StructuralBranchDecision → Prop
  | [] => True
  | decision :: rest => decision.var < SequentialPortable.limit depth ∧ Fresh depth rest

instance freshDecidable (depth : Nat) (decisions : List StructuralBranchDecision) :
    Decidable (Fresh depth decisions) :=
  match decisions with
  | [] => .isTrue True.intro
  | decision :: rest =>
      @instDecidableAnd _ _ (inferInstance : Decidable (decision.var < SequentialPortable.limit depth))
        (freshDecidable depth rest)

theorem fresh_member (depth : Nat) (decisions : List StructuralBranchDecision) (fresh : Fresh depth decisions)
    (decision : StructuralBranchDecision) (member : decision ∈ decisions) :
    decision.var < SequentialPortable.limit depth := by
  induction decisions with
  | nil => cases member
  | cons head rest ih =>
      cases member with
      | head => exact fresh.1
      | tail _ member => exact ih fresh.2 member

theorem fresh_state {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (fresh : Fresh depth state.decisions) : ThreadedStateFreshForNext state := by
  intro decision member
  rw [← SequentialPortable.limit_exact]
  exact fresh_member depth state.decisions fresh decision member

abbrev LoadedForNext := (depth : Nat) × (assignment : SequentialAssignment depth) ×
  {state : ThreadedConstitutiveState depth assignment // ThreadedStateFreshForNext state}

def restoreForNext (input : List UInt8) : Option LoadedForNext := do
  let ⟨depth, assignment, state⟩ ← restore input
  if fresh : Fresh depth state.decisions then
    some ⟨depth, assignment, ⟨state, fresh_state state fresh⟩⟩
  else none

theorem for_next_roundtrip {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) (fresh : Fresh depth state.decisions) :
    restoreForNext (save state formed) =
      some (⟨depth, assignment, ⟨state, fresh_state state fresh⟩⟩ : LoadedForNext) := by
  unfold restoreForNext
  rw [restored_exact]
  dsimp only [Bind.bind, Option.bind]
  rw [dif_pos fresh]

theorem all_next_consumers {depth assignment} (state : ThreadedConstitutiveState depth assignment)
    (formed : SequentialPortable.Formed assignment) (fresh : Fresh depth state.decisions)
    {Result : Type u} (future : LoadedForNext → Result) :
    (restoreForNext (save state formed)).map future =
      some (future ⟨depth, assignment, ⟨state, fresh_state state fresh⟩⟩) := by
  rw [for_next_roundtrip state formed fresh]
  rfl


end ConstitutiveSearch.Agent.Local.Documentary.StatePortable

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.record_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.for_next_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.all_next_consumers
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.Fresh
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.freshDecidable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.fresh_member
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.fresh_state
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.LoadedForNext
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.restoreForNext
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.bit
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.bit_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.Holds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.holdsDecidable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.holds_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.holds_of_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.Record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.Loaded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.fields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.validate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.coupled_equal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.fields_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.record_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.boolean
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.decision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.recordCodec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.StatePortable.all_consumers
/- AXIOM_AUDIT_END -/
