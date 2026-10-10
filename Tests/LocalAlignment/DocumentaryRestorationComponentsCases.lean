import Tests.LocalAlignment.DocumentaryMaterializedPresent
import Tests.LocalAlignment.DocumentaryPortableStoreCases

/-! Concrete instances of dossier bytes and materialized master/present laws.
Whole-present statements below consume typed payloads, not physical bytes. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases
open Resources

theorem every_program_dossier_recovered :
    PortableMemory.load Cases.sources Cases.contract (PortableMemory.save ProgramCases.actual.1.dossier.memory) =
      .ok ProgramCases.actual.1.dossier.memory := by
  rcases PortableMemory.program_execution_formed ProgramCases.actual.2 .empty with ⟨formed⟩
  exact PortableMemory.byte_roundtrip formed

theorem unsuitable_dossier_recovered :
    PortableMemory.load Cases.sources Cases.contract (PortableMemory.save ProgramCases.wrongActual.1.dossier.memory) =
      .ok ProgramCases.wrongActual.1.dossier.memory := by
  rcases PortableMemory.program_execution_formed ProgramCases.wrongActual.2 .empty with ⟨formed⟩
  exact PortableMemory.byte_roundtrip formed

theorem blocked_dossier_recovered :
    PortableMemory.load Cases.sources Cases.contract (PortableMemory.save ProgramCases.sourceBlockedActual.1.dossier.memory) =
      .ok ProgramCases.sourceBlockedActual.1.dossier.memory := by
  rcases PortableMemory.program_execution_formed ProgramCases.sourceBlockedActual.2 .empty with ⟨formed⟩
  exact PortableMemory.byte_roundtrip formed

theorem every_adaptive_dossier_recovered (policy : Adaptive.Policy Nat) (feed : Nat → Adaptive.Signal) :
    PortableMemory.load Cases.sources Cases.contract
      (PortableMemory.save (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).1.frame.dossier.memory) =
      .ok (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).1.frame.dossier.memory :=
  PortableMemory.adaptive_execution_byte_roundtrip
    (Adaptive.run policy feed AdaptiveCases.start ProgramCases.script).2 .empty

theorem every_memory_dossier_recovered (requests : List (Memory.Request Nat)) :
    PortableMemory.load Cases.sources Cases.contract
      (PortableMemory.save (Memory.run MemoryCases.boot requests).1.session.frame.dossier.memory) =
      .ok (Memory.run MemoryCases.boot requests).1.session.frame.dossier.memory :=
  PortableMemory.memory_execution_byte_roundtrip (Memory.run MemoryCases.boot requests).2 .empty

def output := CanonicalRestoration.canonicalOutput Cases.sources Cases.contract Cases.publicOrigin .here
def once := PortableMemory.prepend (Documentary.empty Cases.sources Cases.contract) output
def twice := PortableMemory.prepend once output
def twiceFormed : PortableMemory.Formed Cases.sources Cases.contract twice :=
  .cons (.cons .empty Cases.publicOrigin .here rfl) Cases.publicOrigin .here rfl

theorem repeated_citations_recovered :
    PortableMemory.load Cases.sources Cases.contract (PortableMemory.save twice) = .ok twice :=
  PortableMemory.byte_roundtrip twiceFormed

theorem equal_items_separate_occurrences :
    twice.items = [output.item, output.item] ∧
      (Ref.here : Ref twice.items output.item).position = 0 ∧
      (Ref.prior .here : Ref twice.items output.item).position = 1 ∧
      PortableMemory.record twice = [1, 1] := ⟨rfl, rfl, rfl, rfl⟩

def emptyEnvelope := PortableMemory.envelope (Documentary.empty Cases.sources Cases.contract)
def wire (saved : PortableCheckpoint.Saved) := PortableCheckpoint.toBytes (PortableCheckpoint.encode saved)

theorem bad_version : PortableMemory.load Cases.sources Cases.contract
    (wire { emptyEnvelope with version := 2 }) = .error .version := rfl
theorem wrong_component : PortableMemory.load Cases.sources Cases.contract
    (wire { emptyEnvelope with schema := 2 }) = .error .schema := rfl
theorem bad_header : PortableMemory.load Cases.sources Cases.contract
    (wire { emptyEnvelope with round := 1 }) = .error .header := rfl
theorem unexpected_nodes : PortableMemory.load Cases.sources Cases.contract
    (wire { emptyEnvelope with nodes := [.quotation 1 42] }) = .error .header := rfl
theorem absent_source : PortableMemory.load Cases.sources Cases.contract
    (wire { emptyEnvelope with bindings := [99] }) = .error .source := rfl
theorem forbidden_equal_content_source : PortableMemory.load Cases.sources Cases.contract
    (wire { emptyEnvelope with bindings := [0] }) = .error .permission := rfl
theorem missing_permission : PortableMemory.load Cases.sources (⟨[]⟩ : Contract)
    (PortableMemory.save twice) = .error .permission := rfl
theorem invalid_bytes : PortableMemory.load Cases.sources Cases.contract [] = .error .bytes := rfl

theorem every_master_cursor_materialized (count : Nat) :
    (MasterPayload.cursor
      (EndogenousDecomposition.MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish).restore =
      (EndogenousDecomposition.MasterResources.executeWithReferences count ProgramCases.start.dossier.cursor).finish :=
  MasterPayload.cursor_exact _

/-- The typed materialization also handles the noncanonical copy producer which
the narrower store byte schema cannot reconstruct from equal numeric records. -/
theorem noncanonical_formation_materialized :
    (MasterPayload.resources PortableStoreCases.copied.2.resources).restore =
      PortableStoreCases.copied.2.resources := MasterPayload.resources_exact _

theorem actual_prefix_materialized :
    (MaterializedPresent.present MemoryCases.retainedPrefix).restore = MemoryCases.retainedPrefix :=
  MaterializedPresent.present_exact _

theorem every_declared_future_materialized (requests : List (Memory.Request Nat)) :
    HEq (Memory.run (MaterializedPresent.present MemoryCases.retainedPrefix).restore requests)
      (Memory.run MemoryCases.retainedPrefix requests) := MaterializedPresent.all_futures _ requests

theorem quotation_and_sum_after_materialization :
    (Memory.run (MaterializedPresent.present MemoryCases.retainedPrefix).restore MemoryCases.futures).1.remaining.length = 0 := by
  rw [MaterializedPresent.present_exact]
  exact MemoryCases.continued_done

end ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.every_program_dossier_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.unsuitable_dossier_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.blocked_dossier_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.every_adaptive_dossier_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.every_memory_dossier_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.once
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.twice
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.twiceFormed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.repeated_citations_recovered
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.equal_items_separate_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.emptyEnvelope
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.wire
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.bad_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.wrong_component
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.bad_header
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.unexpected_nodes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.absent_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.forbidden_equal_content_source
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.missing_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.invalid_bytes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.every_master_cursor_materialized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.noncanonical_formation_materialized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.actual_prefix_materialized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.every_declared_future_materialized
#print axioms ConstitutiveSearch.Agent.Local.Documentary.RestorationComponentsCases.quotation_and_sum_after_materialization
/- AXIOM_AUDIT_END -/
