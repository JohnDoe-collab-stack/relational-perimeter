import Tests.LocalAlignment.DocumentaryContract

/-! Constructed finite fixtures, not a new production master or a model run.
The same received value has two source occurrences with different permissions.
A third occurrence has a different version and factual value. -/
set_option genInjectivity false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Cases
open Resources

def privateKey : SourceKey := ⟨0, 2, 0⟩
def publicKey : SourceKey := ⟨1, 1, 0⟩
def updatedKey : SourceKey := ⟨1, 2, 0⟩
def context : List SourceKey := [privateKey, publicKey, updatedKey]

def sharedPassage : Passage := ⟨7, 42, "La mesure certifiee est 42."⟩
def updatedPassage : Passage := ⟨7, 43, "La mesure revisee est 43."⟩
def sources : Support SourceValue context :=
  Support.given (sharedPassage, sharedPassage, updatedPassage, PUnit.unit)

def privateOrigin : Location context := ⟨privateKey, .here⟩
def publicOrigin : Location context := ⟨publicKey, .prior .here⟩
def updatedOrigin : Location context := ⟨updatedKey, .prior (.prior .here)⟩
def contract : Contract := ⟨[1, 2]⟩
def factDemand : Demand := ⟨7, 42, none⟩
def pinnedDemand : Demand := ⟨7, 42, some 0⟩
def initial : Memory sources contract := empty sources contract

theorem received_values_equal :
    sources.read privateOrigin.2 = sources.read publicOrigin.2 := rfl

theorem received_origins_distinct : privateOrigin.2.position ≠ publicOrigin.2.position :=
  Nat.noConfusion

theorem private_permission_absent : resolvePermission contract.allowed privateOrigin.2.position = none :=
  rfl

theorem public_permission_present :
    resolvePermission contract.allowed publicOrigin.2.position = some (.here : Ref [1, 2] 1) := rfl

def publicCandidate : Candidate sources contract factDemand :=
  ⟨publicOrigin, .here, rfl, rfl, True.intro⟩

def taskAdmissible : Admissible sources contract [factDemand] :=
  .cons publicCandidate .nil

theorem forbidden_request_no_effect (memory : Memory sources contract) :
    execute memory privateOrigin = (memory, none) :=
  execute_refused memory privateOrigin private_permission_absent

/-- The forbidden proposal is refused; the independently specified fact task
can still be fulfilled through the allowed source, after context erasure. -/
def alternativeResult : Memory sources contract × Option Citation :=
  let refused := execute initial privateOrigin
  let erased := eraseContext (refused.1, "Citer la source privee") (fun _ => "")
  execute erased.1 publicOrigin

def alternativeGoal : Goal [factDemand] alternativeResult.1.items :=
  .cons factDemand (extract sources publicOrigin).citation .here
    ⟨rfl, rfl, True.intro⟩ (.nil _)

theorem alternative_returns_actual_citation :
    alternativeResult.2 = some (extract sources publicOrigin).citation := rfl

theorem alternative_is_conforming :
    Nonempty (Conforms sources contract (extract sources publicOrigin).citation) :=
  ⟨alternativeResult.1.valid .here⟩

theorem empty_dossier_is_incomplete :
    goalSucceeded [factDemand] initial.items = false := rfl

theorem refusal_does_not_complete_task :
    goalSucceeded [factDemand] (execute initial privateOrigin).1.items = false := rfl

theorem alternative_evaluator_succeeds :
    goalSucceeded [factDemand] alternativeResult.1.items = true := rfl

theorem alternative_does_not_replace_pinned_origin :
    goalSucceeded [pinnedDemand] alternativeResult.1.items = false := rfl

/-- This quantification covers every conforming memory, including every state
reachable by further permitted actions; failure of one proposal is not the premise. -/
theorem pinned_task_incompatible (memory : Memory sources contract) :
    Goal [pinnedDemand] memory.items → False :=
  forbidden_origin_incompatible pinnedDemand 0 rfl private_permission_absent memory

theorem pinned_task_incompatible_after_erasure {Context : Type}
    (state : Memory sources contract × Context) (reset : Context → Context) :
    Goal [pinnedDemand] (eraseContext state reset).1.items → False :=
  pinned_task_incompatible (eraseContext state reset).1

theorem forbidden_still_refused_after_erasure {Context : Type}
    (state : Memory sources contract × Context) (reset : Context → Context) :
    execute (eraseContext state reset).1 privateOrigin = (state.1, none) :=
  forbidden_request_no_effect state.1

theorem wrong_version_does_not_meet :
    Meets factDemand (extract sources updatedOrigin).citation → False := by
  intro claimed
  have wrong : 43 = 42 := claimed.2.1
  exact (by decide : 43 ≠ 42) wrong

theorem allowed_wrong_version_is_incomplete :
    goalSucceeded [factDemand] (execute initial updatedOrigin).1.items = false := rfl

def utf8 (text : String) : List UInt8 := text.toUTF8.data.toList
def decimal (value : Nat) : List UInt8 := utf8 (Nat.repr value)

def renderCitation (citation : Citation) : List UInt8 :=
  utf8 "> " ++ utf8 citation.passage.text ++ utf8 "\n\nSource " ++ decimal citation.source.document ++
    utf8 ", version " ++ decimal citation.source.version ++ utf8 ", extrait " ++
    decimal citation.source.excerpt ++ utf8 ", occurrence recue " ++ decimal citation.position ++
    utf8 ".\nFait " ++ decimal citation.passage.key ++ utf8 " = " ++ decimal citation.passage.value ++ utf8 ".\n"

/-- The rendered text consumes the element returned by the real allowed
operation. It is not rendered from a separately reconstructed expected value. -/
def actualDocument : List UInt8 :=
  match alternativeResult.2 with
  | none => utf8 "Aucun element incorpore.\n"
  | some citation => renderCitation citation

theorem actual_document_exact :
    actualDocument = utf8 "> La mesure certifiee est 42.\n\nSource 1, version 1, extrait 0, occurrence recue 1.\nFait 7 = 42.\n" :=
  rfl

end ConstitutiveSearch.Agent.Local.Documentary.Cases
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.privateKey
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.publicKey
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.updatedKey
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.context
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.sharedPassage
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.updatedPassage
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.sources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.privateOrigin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.publicOrigin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.updatedOrigin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.contract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.factDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.pinnedDemand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.initial
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.received_values_equal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.received_origins_distinct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.private_permission_absent
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.public_permission_present
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.publicCandidate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.taskAdmissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.forbidden_request_no_effect
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.alternativeResult
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.alternativeGoal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.alternative_returns_actual_citation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.alternative_is_conforming
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.empty_dossier_is_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.refusal_does_not_complete_task
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.alternative_evaluator_succeeds
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.alternative_does_not_replace_pinned_origin
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.pinned_task_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.pinned_task_incompatible_after_erasure
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.forbidden_still_refused_after_erasure
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.wrong_version_does_not_meet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.allowed_wrong_version_is_incomplete
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.utf8
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.decimal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.renderCitation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.actualDocument
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cases.actual_document_exact
/- AXIOM_AUDIT_END -/
