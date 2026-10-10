import Tests.LocalAlignment.DocumentaryDossier
import Tests.LocalAlignment.DocumentaryMasterCases

/-! Development cases for a finite sourced dossier. The received permissions,
fact criteria and versions are unchanged from the binary bridge fixtures. -/
set_option genInjectivity false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
namespace ConstitutiveSearch.Agent.Local.Documentary.DossierCases
open Resources EndogenousDecomposition Cases MasterCases Dossier

def first : Obligation context := ⟨factDemand, privateOrigin, publicOrigin⟩
def revision : Obligation context := ⟨revisedDemand, publicOrigin, updatedOrigin⟩
def pinned : Obligation context := ⟨pinnedDemand, privateOrigin, publicOrigin⟩
def unavailable : Obligation context := ⟨⟨7, 44, none⟩, publicOrigin, updatedOrigin⟩
def tasks : List (Obligation context) := [first, revision]
def start : State sources contract := ⟨VariableMaster.Example.origin, initial⟩

def admissible : TaskAdmissible sources contract tasks :=
  .cons (.right .here ⟨rfl, rfl, True.intro⟩)
    (.cons (.right (.prior .here) ⟨rfl, rfl, True.intro⟩) .nil)

def produced := Dossier.execute start tasks
def completed : Goal (demands tasks) produced.1.memory.items :=
  accomplishment start tasks admissible

def withRefusal := Dossier.execute start [first, pinned, revision]
def withUnavailable := Dossier.execute start [unavailable, revision]
def repeated := Dossier.execute start [first, first]
def noTasks := Dossier.execute start []

def firstPart := Dossier.execute start [first]
def resumed := Dossier.execute firstPart.1 [revision]
def erased :=
  let state := (firstPart.1, "Employer la source privee, meme si elle est interdite")
  Dossier.execute (state.1, (fun _ => "") state.2).1 [revision]
def existing := Dossier.execute produced.1 [first]

def render : List Citation → List UInt8
  | [] => []
  | item :: rest => renderCitation item ++ render rest

def actualDocument : List UInt8 := render produced.1.memory.items.reverse

theorem all_demands_completed : goalSucceeded (demands tasks) produced.1.memory.items = true :=
  completion_verdict start tasks admissible
theorem actual_two_steps : produced.1.cursor.depth = start.cursor.depth + 2 :=
  exact_step_count start tasks
theorem actual_two_elements : produced.1.memory.items.length = 2 :=
  exact_item_count start tasks admissible

theorem exact_source_versions :
    produced.1.memory.items.map (fun item => (item.position, item.source.version, item.passage.value)) =
      [(2, 2, 43), (1, 1, 42)] := rfl

theorem exact_events :
    produced.2.events.map (fun event => event.map Citation.position) = [some 1, some 2] := rfl

theorem refusal_does_not_stop_continuation :
    withRefusal.2.events.map (fun event => event.map Citation.position) = [some 1, none, some 2] := rfl
theorem refusal_has_no_documentary_effect :
    withRefusal.1.memory.items.length = 2 := rfl
theorem refusal_remains_incomplete :
    goalSucceeded (demands [first, pinned, revision]) withRefusal.1.memory.items = false := rfl
theorem successful_parts_remain_complete :
    goalSucceeded [factDemand, revisedDemand] withRefusal.1.memory.items = true := rfl
theorem unavailable_fact_not_fabricated :
    withUnavailable.2.events.map (fun event => event.map Citation.position) = [none, some 2] := rfl
theorem unavailable_dossier_incomplete :
    goalSucceeded (demands [unavailable, revision]) withUnavailable.1.memory.items = false := rfl

theorem forbidden_whole_task_impossible (memory : Memory sources contract) :
    Goal (demands [first, pinned, revision]) memory.items → False :=
  forbidden_list_incompatible memory (.prior .here) 0 rfl private_permission_absent

theorem equal_values_keep_two_dossier_occurrences :
    repeated.1.memory.items.length = 2 := rfl
theorem empty_task_keeps_present : noTasks.1 = start := rfl
theorem erasure_keeps_actual_resume : erased = resumed := rfl
theorem resume_agrees_with_uninterrupted : produced.1 = resumed.1 :=
  execute_append start [first] [revision]
theorem resume_keeps_prefix : resumed.1.memory.items.tail = firstPart.1.memory.items := rfl
theorem resume_uses_produced_cursor : resumed.1.cursor.depth = firstPart.1.cursor.depth + 1 :=
  exact_step_count firstPart.1 [revision]
theorem continued_dossier_keeps_completed_demands :
    goalSucceeded (demands tasks) existing.1.memory.items = true := rfl

def firstReference : Ref firstPart.1.memory.items (extract sources publicOrigin).citation := .here
def keptReference : Ref resumed.1.memory.items (extract sources publicOrigin).citation :=
  resumed.2.previous firstReference
theorem previous_occurrence_shift : keptReference.position = 1 :=
  resumed.2.previous_position firstReference
theorem previous_evidence_exact :
    resumed.1.memory.valid keptReference = firstPart.1.memory.valid firstReference :=
  resumed.2.previous_evidence firstReference

theorem actual_document_exact :
    actualDocument = utf8 "> La mesure certifiee est 42.\n\nSource 1, version 1, extrait 0, occurrence recue 1.\nFait 7 = 42.\n> La mesure revisee est 43.\n\nSource 1, version 2, extrait 0, occurrence recue 2.\nFait 7 = 43.\n" := rfl

end ConstitutiveSearch.Agent.Local.Documentary.DossierCases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.first
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.revision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.pinned
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.unavailable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.tasks
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.start
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.admissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.completed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.withRefusal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.withUnavailable
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.repeated
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.noTasks
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.firstPart
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.resumed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.erased
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.existing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.render
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.actualDocument
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.all_demands_completed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.actual_two_steps
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.actual_two_elements
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.exact_source_versions
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.exact_events
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.refusal_does_not_stop_continuation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.refusal_has_no_documentary_effect
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.refusal_remains_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.successful_parts_remain_complete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.unavailable_fact_not_fabricated
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.unavailable_dossier_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.forbidden_whole_task_impossible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.equal_values_keep_two_dossier_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.empty_task_keeps_present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.erasure_keeps_actual_resume
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.resume_agrees_with_uninterrupted
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.resume_keeps_prefix
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.resume_uses_produced_cursor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.continued_dossier_keeps_completed_demands
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.firstReference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.keptReference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.previous_occurrence_shift
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.previous_evidence_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.DossierCases.actual_document_exact
/- AXIOM_AUDIT_END -/
