import Tests.LocalAlignment.DocumentaryMaster
import Tests.LocalAlignment.DocumentaryCases
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.VariableMasterInstance

/-! Development cases for the semantic bridge, with the existing public origin.
Source-derived problems change the actual normalization and documentary output.
This module does not run a model or claim a reduced-memory checkpoint. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.MasterCases
open Resources SAT EndogenousDecomposition
open Cases

def factRun := Master.run VariableMaster.Example.origin sources contract factDemand
  privateOrigin publicOrigin initial

def pinnedRun := Master.run VariableMaster.Example.origin sources contract pinnedDemand
  privateOrigin publicOrigin initial

def bothContract : Contract := ⟨[0, 1, 2]⟩
def bothRun := Master.run VariableMaster.Example.origin sources bothContract factDemand
  privateOrigin publicOrigin (empty sources bothContract)

def revisedDemand : Demand := ⟨7, 43, none⟩
def revisedRun := Master.run VariableMaster.Example.origin sources contract revisedDemand
  publicOrigin updatedOrigin initial

def contextErasedRun :=
  let erased := eraseContext (initial, "Employer obligatoirement la source privee") (fun _ => "")
  Master.run VariableMaster.Example.origin sources contract factDemand
    privateOrigin publicOrigin erased.1

def pinnedContextErasedRun :=
  let erased := eraseContext (initial, "La source privee est indispensable") (fun _ => "")
  Master.run VariableMaster.Example.origin sources contract pinnedDemand
    privateOrigin publicOrigin erased.1

def continuedRun :=
  Master.run factRun.1.next sources contract factDemand privateOrigin publicOrigin factRun.2.result.1

def actualDocument : List UInt8 :=
  match factRun.2.result.2 with
  | none => utf8 "Aucun element incorpore.\n"
  | some citation => renderCitation citation

theorem same_received_value_different_permission :
    factRun.1.leftCheck.flag = false ∧ factRun.1.rightCheck.flag = true := ⟨rfl, rfl⟩

theorem pair_encoding_changes_with_contract :
    factRun.1.formula = [[.positive 10]] ∧ bothRun.1.formula = [] := by
  constructor
  · change [[Literal.positive (VariableMaster.selected (VariableMaster.masterHead VariableMaster.Example.origin))]] = _
    rw [VariableMaster.Example.selected_exact]
  · rfl

theorem actual_grouped_width : bothRun.1.reduction.retained.length = 1 := rfl
theorem actual_distinct_width : factRun.1.reduction.retained.length = 2 := rfl

theorem permitted_route_finishes : goalSucceeded [factDemand] factRun.2.result.1.items = true := rfl
theorem permitted_route_is_public :
    (factRun.2.result.2.map Citation.position) = some 1 := rfl
theorem grouped_route_is_public :
    (bothRun.2.result.2.map Citation.position) = some 1 := rfl
theorem grouped_sources_stay_distinct : privateOrigin.2.position ≠ publicOrigin.2.position := by decide

theorem incompatible_goal_stays_incomplete :
    goalSucceeded [pinnedDemand] pinnedRun.2.result.1.items = false := rfl
theorem incompatible_goal_no_output : pinnedRun.2.result.2 = none := rfl

theorem changed_fact_selects_its_actual_version :
    revisedRun.2.result.2.map (fun item => (item.position, item.passage.value)) = some (2, 43) := rfl
theorem changed_fact_finishes :
    goalSucceeded [revisedDemand] revisedRun.2.result.1.items = true := rfl

theorem context_erasure_same_run : contextErasedRun = factRun := rfl
theorem pinned_context_erasure_same_run : pinnedContextErasedRun = pinnedRun := rfl
theorem actual_successor_used :
    continuedRun.1.head.next.depth = factRun.1.head.next.depth + 1 := rfl
theorem continuation_keeps_goal :
    goalSucceeded [factDemand] continuedRun.2.result.1.items = true := rfl
theorem continuation_keeps_first_element :
    continuedRun.2.result.1.items.tail = factRun.2.result.1.items := rfl

theorem actual_document_exact :
    actualDocument = utf8 "> La mesure certifiee est 42.\n\nSource 1, version 1, extrait 0, occurrence recue 1.\nFait 7 = 42.\n" := rfl

end ConstitutiveSearch.Agent.Local.Documentary.MasterCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.factRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.pinnedRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.bothContract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.bothRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.revisedDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.revisedRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.contextErasedRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.pinnedContextErasedRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.continuedRun
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.actualDocument
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.same_received_value_different_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.pair_encoding_changes_with_contract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.actual_grouped_width
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.actual_distinct_width
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.permitted_route_finishes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.permitted_route_is_public
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.grouped_route_is_public
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.grouped_sources_stay_distinct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.incompatible_goal_stays_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.incompatible_goal_no_output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.changed_fact_selects_its_actual_version
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.changed_fact_finishes
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.context_erasure_same_run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.pinned_context_erasure_same_run
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.actual_successor_used
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.continuation_keeps_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.continuation_keeps_first_element
#print axioms ConstitutiveSearch.Agent.Local.Documentary.MasterCases.actual_document_exact
/- AXIOM_AUDIT_END -/
