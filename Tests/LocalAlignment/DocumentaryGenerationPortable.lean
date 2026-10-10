import Tests.LocalAlignment.DocumentaryHistoryPortable
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveOperationalStage

/-! Exact serialization of all CanonicalStageGeneration fields. The complete
target formation is decoded from its constructor code; its integrated source
is validated at the dependent index. Counts are retained verbatim. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable
open StrongPerimetralTurning StrongPerimetralTurning.Example
open ConstitutiveGeneration EndogenousDecomposition FoundationPortable ControlCodec

structure Record where
  target : Tree
  generateCalls : Nat
  generatedSteps : Nat
  provenanceUnits : Nat
  certificatesProduced : Nat

def capture {depth} (value : CanonicalStageGeneration depth) : Record :=
  ⟨FoundationPortable.capture value.target, value.generateCalls, value.generatedSteps,
    value.provenanceUnits, value.certificatesProduced⟩

/-- The level is a validation readout of the received full constructor tree. -/
theorem source_index_exact (depth : Nat) (tree : Tree) (indexed : tree.level = depth + 3) :
    materialize examplePresentation tree = (constructStage depth).history.endpoint := by
  have expected : (FoundationPortable.capture (constructStage depth).history.endpoint).level =
      depth + 3 :=
    (capture_level _).trans (constitutedOperationalIndex_exact depth)
  have same : tree = FoundationPortable.capture (constructStage depth).history.endpoint :=
    level_injective _ _ (indexed.trans expected.symm)
  rw [same, FoundationPortable.capture_exact]

def fields (depth : Nat) (source : Tree) (indexed : source.level = depth + 3)
    (counts : Nat × Nat × Nat × Nat) : CanonicalStageGeneration depth :=
  let original := materialize examplePresentation source
  let target := extendFields original
  have originalExact : original = (constructStage depth).history.endpoint :=
    source_index_exact depth source indexed
  { target := target
    targetExact := by
      unfold target
      rw [originalExact]
      rfl
    generated := Eq.rec
      (motive := fun original _ => GeneratedStep original target)
      (HistoryPortable.stepFields original) originalExact
    generateCalls := counts.1
    generatedSteps := counts.2.1
    provenanceUnits := counts.2.2.1
    certificatesProduced := counts.2.2.2 }

def restoreRecord (depth : Nat) (record : Record) : Option (CanonicalStageGeneration depth) :=
  match record.target with
  | .root => none
  | .formed source =>
      if indexed : source.level = depth + 3 then
        some (fields depth source indexed
          (record.generateCalls, record.generatedSteps, record.provenanceUnits, record.certificatesProduced))
      else none

theorem generation_equal {depth} (left right : CanonicalStageGeneration depth)
    (target : left.target = right.target)
    (calls : left.generateCalls = right.generateCalls)
    (steps : left.generatedSteps = right.generatedSteps)
    (provenance : left.provenanceUnits = right.provenanceUnits)
    (certificates : left.certificatesProduced = right.certificatesProduced) : left = right := by
  cases left with
  | mk lt le lg lc ls lp lf =>
      cases right with
      | mk rt re rg rc rs rp rf =>
          cases target
          cases calls
          cases steps
          cases provenance
          cases certificates
          have generated := HistoryPortable.generatedStep_unique lg rg
          cases generated
          rfl

theorem record_exact {depth} (value : CanonicalStageGeneration depth) :
    restoreRecord depth (capture value) = some value := by
  have targetCode : FoundationPortable.capture value.target =
      Tree.formed (FoundationPortable.capture (constructStage depth).history.endpoint) := by
    rw [value.targetExact]
    rfl
  have indexed : (FoundationPortable.capture (constructStage depth).history.endpoint).level =
      depth + 3 :=
    (capture_level _).trans (constitutedOperationalIndex_exact depth)
  unfold capture restoreRecord
  rw [targetCode]
  change (if indexed : (FoundationPortable.capture (constructStage depth).history.endpoint).level = depth + 3
    then some (fields depth (FoundationPortable.capture (constructStage depth).history.endpoint) indexed
      (value.generateCalls, value.generatedSteps, value.provenanceUnits, value.certificatesProduced))
    else none) = _
  rw [dif_pos indexed]
  apply congrArg some
  apply generation_equal
  · change extendFields (materialize examplePresentation
        (FoundationPortable.capture (constructStage depth).history.endpoint)) = value.target
    rw [FoundationPortable.capture_exact, value.targetExact]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

def recordCodec : Codec Record :=
  (treeCodec.product (natural.product (natural.product (natural.product natural)))).via
    (fun value => (value.target, value.generateCalls, value.generatedSteps,
      value.provenanceUnits, value.certificatesProduced))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2⟩)
    (fun value => by cases value; rfl)

def envelope : Codec (Nat × Record) :=
  (natural.product (natural.product (natural.product recordCodec))).via
    (fun value => (92, 1, value))
    (fun data => match data.1 with
      | 92 => match data.2.1 with | 1 => some data.2.2 | _ => none
      | _ => none) (fun _ => rfl)

def save {depth} (value : CanonicalStageGeneration depth) : List UInt8 :=
  bytes (envelope.words (depth, capture value))

def load (input : List UInt8) : Option (Nat × Record) := do
  let words ← fromBytes input
  let (value, tail) ← envelope.read words
  match tail with | [] => some value | _ :: _ => none

abbrev Loaded := (depth : Nat) × CanonicalStageGeneration depth

def restore (input : List UInt8) : Option Loaded := do
  let (depth, record) ← load input
  let generation ← restoreRecord depth record
  return ⟨depth, generation⟩

theorem byte_roundtrip {depth} (value : CanonicalStageGeneration depth) :
    load (save value) = some (depth, capture value) := by
  unfold load save
  rw [bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have actual := envelope.exact (depth, capture value) []
  rw [PortableCheckpoint.append_empty] at actual
  rw [actual]

theorem restored_exact {depth} (value : CanonicalStageGeneration depth) :
    restore (save value) = some (⟨depth, value⟩ : Loaded) := by
  unfold restore
  rw [byte_roundtrip]
  change (do let generation ← restoreRecord depth (capture value); pure (⟨depth, generation⟩ : Loaded)) = _
  rw [record_exact]
  rfl

theorem all_consumers {depth} (value : CanonicalStageGeneration depth)
    {Result : Type u} (future : Loaded → Result) :
    (restore (save value)).map future = some (future ⟨depth, value⟩) := by
  rw [restored_exact]
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.Record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.capture
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.source_index_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.fields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.restoreRecord
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.generation_equal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.record_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.recordCodec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.envelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.save
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.load
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.Loaded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.restore
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.restored_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GenerationPortable.all_consumers
/- AXIOM_AUDIT_END -/
