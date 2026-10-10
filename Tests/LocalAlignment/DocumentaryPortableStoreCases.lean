import Tests.LocalAlignment.DocumentaryCanonicalAdaptiveRestoration
import Tests.LocalAlignment.DocumentaryMemoryCases

/-! General-theorem instances and boundary cases for store-only bytes.
The former fixed checkpoint protocol and its evidence remain unchanged. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases
open Resources CanonicalRestoration

theorem actual_program_recovered :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy (PortableStore.save ProgramCases.actual.1.store) =
      .ok ProgramCases.actual.1.store :=
  PortableStore.execution_byte_roundtrip ProgramCases.actual.2 .empty

theorem unsuitable_outputs_recovered :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy (PortableStore.save ProgramCases.wrongActual.1.store) =
      .ok ProgramCases.wrongActual.1.store :=
  PortableStore.execution_byte_roundtrip ProgramCases.wrongActual.2 .empty

theorem refused_and_missing_recovered :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy (PortableStore.save ProgramCases.blockedActual.1.store) =
      .ok ProgramCases.blockedActual.1.store :=
  PortableStore.execution_byte_roundtrip ProgramCases.blockedActual.2 .empty

theorem forbidden_source_recovered :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy (PortableStore.save ProgramCases.sourceBlockedActual.1.store) =
      .ok ProgramCases.sourceBlockedActual.1.store :=
  PortableStore.execution_byte_roundtrip ProgramCases.sourceBlockedActual.2 .empty

theorem every_adaptive_policy_recovered (policy : Adaptive.Policy Nat) (feed : Nat → Adaptive.Signal) :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy
      (PortableStore.save (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).1.frame.store) =
      .ok (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).1.frame.store :=
  CanonicalAdaptiveRestoration.execution_byte_roundtrip
    (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).2 .empty

theorem every_memory_sequence_recovered (requests : List (Memory.Request Nat)) :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy
      (PortableStore.save (Memory.run MemoryCases.boot requests).1.session.frame.store) =
      .ok (Memory.run MemoryCases.boot requests).1.session.frame.store :=
  CanonicalAdaptiveRestoration.memory_execution_byte_roundtrip (Memory.run MemoryCases.boot requests).2 .empty

def wire (saved : PortableCheckpoint.Saved) : List UInt8 :=
  PortableCheckpoint.toBytes (PortableCheckpoint.encode saved)

def emptyEnvelope := PortableStore.envelope ProgramCases.start.store

theorem empty_recovered :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy (PortableStore.save ProgramCases.start.store) =
      .ok ProgramCases.start.store := PortableStore.byte_roundtrip .empty

theorem bad_version : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with version := 2 }) = .error .version := rfl

theorem bad_schema : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with schema := 1 }) = .error .schema := rfl

theorem bad_header : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with depth := 1 }) = .error .header := rfl

theorem bad_bindings : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with bindings := [0] }) = .error .header := rfl

theorem empty_bytes : PortableStore.load Cases.sources Cases.contract DeductionCases.policy [] = .error .bytes := rfl

theorem forbidden_source : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with nodes := [.quotation 0 42] }) = .error (.store .sourceForbidden) := rfl

theorem changed_value : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with nodes := [.quotation 1 43] }) = .error (.store .valueChanged) := rfl

theorem forbidden_duplicate_rule : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with nodes := [.derived 2 0 0 0, .quotation 1 42] }) = .error (.store .ruleForbidden) := rfl

theorem missing_premise : PortableStore.load Cases.sources Cases.contract DeductionCases.policy
    (wire { emptyEnvelope with nodes := [.derived 0 0 1 0, .quotation 1 42] }) = .error (.store .premiseMissing) := rfl

def output := canonicalOutput Cases.sources Cases.contract Cases.publicOrigin .here
def once : Deduction.Store Cases.sources Cases.contract DeductionCases.policy :=
  ⟨_, Deduction.quote ProgramCases.start.store.2 output⟩
def twice : Deduction.Store Cases.sources Cases.contract DeductionCases.policy := ⟨_, Deduction.quote once.2 output⟩
def twiceFormed : Formed Cases.sources Cases.contract DeductionCases.policy twice :=
  .quotation (.quotation .empty Cases.publicOrigin .here rfl) Cases.publicOrigin .here rfl

theorem equal_values_distinct_occurrences :
    twice.2.resources.read .here = twice.2.resources.read (.prior .here) ∧
      (Ref.here : Ref twice.1 (.quotation output.item)).position = 0 ∧
      (Ref.prior .here : Ref twice.1 (.quotation output.item)).position = 1 := ⟨rfl, rfl, rfl⟩

theorem repeated_formation_recovered :
    PortableStore.load Cases.sources Cases.contract DeductionCases.policy (PortableStore.save twice) = .ok twice :=
  PortableStore.byte_roundtrip twiceFormed

/-- A coherent noncanonical producer reads the earlier occurrence rather than
depositing the packet again. Equal records do not encode that different action. -/
def copiedProducer : Producer Deduction.Value once.1 where
  inputKinds := [.quotation output.item]
  inputs := .cons .here .nil
  outputKind := fun _ => .quotation output.item
  operation := fun arguments => arguments.1

def copied : Deduction.Store Cases.sources Cases.contract DeductionCases.policy :=
  ⟨_, ⟨once.2.resources.extend copiedProducer, fun ref => match ref with
    | .here => .quotation output.item output.evidence
    | .prior old => once.2.valid old⟩⟩

def formationArity {Kind : Type} {Value : Kind → Type} {kinds : List Kind}
    {values : Values Value kinds} (formation : Formation Value values) : Nat := by
  cases formation with
  | given _ => exact 0
  | produced _ producer => exact producer.inputKinds.length

def lastArity {context sources contract policy} (store : @Deduction.Store context sources contract policy) : Nat :=
  formationArity store.2.resources.formation

theorem equal_records_different_formations : Portable.record copied = Portable.record twice ∧ copied ≠ twice := by
  constructor
  · rfl
  · intro same
    have impossible : 1 = 0 := congrArg lastArity same
    exact Nat.noConfusion impossible

end ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.actual_program_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.unsuitable_outputs_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.refused_and_missing_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.forbidden_source_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.every_adaptive_policy_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.every_memory_sequence_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.wire
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.emptyEnvelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.empty_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.bad_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.bad_schema
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.bad_header
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.bad_bindings
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.empty_bytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.forbidden_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.changed_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.forbidden_duplicate_rule
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.missing_premise
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.once
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.twice
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.twiceFormed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.equal_values_distinct_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.repeated_formation_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.copiedProducer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.copied
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.formationArity
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.lastArity
#print axioms ConstitutiveSearch.Agent.Local.Documentary.PortableStoreCases.equal_records_different_formations
/- AXIOM_AUDIT_END -/
