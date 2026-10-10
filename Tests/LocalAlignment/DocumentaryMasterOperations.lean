import Tests.LocalAlignment.DocumentaryControlCodec
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MasterResourceExecution

/-! Explicit recipes for the seven existing master producers. A recipe stores
typed ports and their dependent environment, not a Producer function field.
Only the first-order opcode/position record has a byte codec here: the master
values and dependent environment still require their own portable realization. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterOperations
open Resources EndogenousDecomposition

inductive Record where
  | discover (source : Nat)
  | applyStage (discovery fresh : Nat)
  | decompose (past application : Nat)
  | assemble (production : Nat)
  | nextPrefix (head : Nat)
  | nextSource (head : Nat)
  | nextFresh (head fresh : Nat)

def Record.fields : Record → Nat × List Nat
  | .discover source => (0, [source])
  | .applyStage discovery fresh => (1, [discovery, fresh])
  | .decompose past application => (2, [past, application])
  | .assemble production => (3, [production])
  | .nextPrefix head => (4, [head])
  | .nextSource head => (5, [head])
  | .nextFresh head fresh => (6, [head, fresh])

def readSingle (build : Nat → Record) : List Nat → Option Record
  | [] => none
  | head :: tail => match tail with
    | [] => some (build head)
    | _ :: _ => none

def readDouble (build : Nat → Nat → Record) : List Nat → Option Record
  | [] => none
  | first :: tail => match tail with
    | [] => none
    | second :: rest => match rest with
      | [] => some (build first second)
      | _ :: _ => none

def readRecord (fields : Nat × List Nat) : Option Record :=
  match fields.1 with
  | 0 => readSingle Record.discover fields.2
  | 1 => readDouble Record.applyStage fields.2
  | 2 => readDouble Record.decompose fields.2
  | 3 => readSingle Record.assemble fields.2
  | 4 => readSingle Record.nextPrefix fields.2
  | 5 => readSingle Record.nextSource fields.2
  | 6 => readDouble Record.nextFresh fields.2
  | _ => none

theorem record_exact (record : Record) : readRecord record.fields = some record := by
  cases record <;> rfl

def recordCodec : ControlCodec.Codec Record :=
  ControlCodec.Codec.via
    (ControlCodec.Codec.product ControlCodec.natural
      (ControlCodec.Codec.list ControlCodec.natural))
    Record.fields readRecord record_exact

def saveRecord (record : Record) : List UInt8 :=
  ControlCodec.bytes (recordCodec.words record)

def loadRecord (bytes : List UInt8) : Option Record := do
  let words ← ControlCodec.fromBytes bytes
  let (record, tail) ← recordCodec.read words
  match tail with
  | [] => some record
  | _ :: _ => none

theorem record_byte_roundtrip (record : Record) :
    loadRecord (saveRecord record) = some record := by
  unfold loadRecord saveRecord
  rw [ControlCodec.bytes_exact]
  dsimp only [Bind.bind, Option.bind]
  have exact := recordCodec.exact record []
  rw [PortableCheckpoint.append_empty] at exact
  rw [exact]

/-- The environment is indexed by the actual retained resource kinds. It is
still dependent typed data, not a first-order byte representation of those
kinds or of their higher-order state values. -/
inductive Operation (kinds : List MasterResources.Kind) : Type 3 where
  | discover {depth assignment}
      (source : Ref kinds (.source depth assignment))
  | applyStage {depth assignment} {state : ThreadedConstitutiveState depth assignment}
      (discovery : Ref kinds (.discovery state)) (fresh : Ref kinds (.fresh state))
  | decompose {depth assignment} {state : ThreadedConstitutiveState depth assignment}
      (past : Ref kinds (.prefix state)) (application : Ref kinds (.application state))
  | assemble {depth assignment} {state : ThreadedConstitutiveState depth assignment}
      {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
      {built : ConstructedThreadedStageRun state}
      (production : Ref kinds (.decomposition state past built))
  | nextPrefix {depth assignment} {state : ThreadedConstitutiveState depth assignment}
      {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
      (head : Ref kinds (.head state past))
  | nextSource {depth assignment} {state : ThreadedConstitutiveState depth assignment}
      {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
      (head : Ref kinds (.head state past))
  | nextFresh {depth assignment} {state : ThreadedConstitutiveState depth assignment}
      {past : ConstitutedOperationalPrefix (causalStateOfThreadedState state)}
      (head : Ref kinds (.head state past)) (fresh : Ref kinds (.fresh state))

/-- Construct the existing producer closure; do not apply its operation. -/
def Operation.producer {kinds} : Operation kinds → Producer MasterResources.Value kinds
  | .discover source => MasterResources.discover source
  | .applyStage discovery fresh => MasterResources.applyStage discovery fresh
  | .decompose past application => MasterResources.decompose past application
  | .assemble production => MasterResources.assemble production
  | .nextPrefix head => MasterResources.headNextPrefix head
  | .nextSource head => MasterResources.headNextSource head
  | .nextFresh head fresh => MasterResources.headNextFresh head fresh

def Operation.record {kinds} : Operation kinds → Record
  | .discover source => .discover source.position
  | .applyStage discovery fresh => .applyStage discovery.position fresh.position
  | .decompose past application => .decompose past.position application.position
  | .assemble production => .assemble production.position
  | .nextPrefix head => .nextPrefix head.position
  | .nextSource head => .nextSource head.position
  | .nextFresh head fresh => .nextFresh head.position fresh.position

def portPositions {Kind : Type u} {context : List Kind} :
    {input : List Kind} → Ports context input → List Nat
  | _, .nil => []
  | _, .cons ref rest => ref.position :: portPositions rest

/-- Exact ordered source ports, including repeated or distinct equal-value
occurrences. Numeric positions are readings of these typed ports. -/
theorem producer_ports {kinds} (operation : Operation kinds) :
    portPositions operation.producer.inputs = operation.record.fields.2 := by
  cases operation <;> rfl

theorem every_operation_record_bytes {kinds} (operation : Operation kinds) :
    loadRecord (saveRecord operation.record) = some operation.record :=
  record_byte_roundtrip operation.record

end ConstitutiveSearch.Agent.Local.Documentary.MasterOperations
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.Record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.Record.fields
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.readSingle
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.readDouble
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.readRecord
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.record_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.recordCodec
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.saveRecord
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.loadRecord
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.record_byte_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.Operation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.Operation.producer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.Operation.record
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.portPositions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.producer_ports
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterOperations.every_operation_record_bytes
/- AXIOM_AUDIT_END -/
