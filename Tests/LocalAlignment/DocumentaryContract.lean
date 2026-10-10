import RelationalPerimeter.Agents.Constitutive.Requirement

/-! First documentary semantic layer, using the existing typed resource producers.
This layer closes received-source extraction and admission. It does not yet
interpret a documentary action in the single master discovery engine.
The goal never depends on permissions; an impossible goal remains impossible. -/
set_option genInjectivity false
namespace ConstitutiveSearch.Agent.Local.Documentary
open Resources

structure SourceKey where
  document : Nat
  version : Nat
  excerpt : Nat

structure Passage where
  key : Nat
  value : Nat
  text : String

def SourceValue (_key : SourceKey) : Type := Passage

abbrev Location (context : List SourceKey) := (key : SourceKey) × Ref context key

structure Citation where
  source : SourceKey
  position : Nat
  passage : Passage

structure Contract where
  allowed : List Nat

structure Demand where
  key : Nat
  value : Nat
  origin : Option Nat

/-- Independent of the producer and of the permissions. A pinned origin cannot
be replaced by another occurrence with equal contents. -/
def Meets (demand : Demand) (citation : Citation) : Prop :=
  citation.passage.key = demand.key ∧ citation.passage.value = demand.value ∧
    match demand.origin with
    | none => True
    | some position => citation.position = position

inductive Goal : List Demand → List Citation → Type where
  | nil (items : List Citation) : Goal [] items
  | cons {rest items} (demand : Demand) (item : Citation)
      (located : Ref items item) (meets : Meets demand item) (tail : Goal rest items) :
      Goal (demand :: rest) items

def meetsDecision (demand : Demand) (item : Citation) : Decidable (Meets demand item) := by
  unfold Meets
  cases demand.origin <;> infer_instance

inductive Meeting (demand : Demand) (items : List Citation) where
  | found (item : Citation) (located : Ref items item) (meets : Meets demand item)
  | missing (absent : {item : Citation} → Ref items item → Meets demand item → False)

/-- Searches actual dossier occurrences, preserving their references. -/
def findMeeting (demand : Demand) : (items : List Citation) → Meeting demand items
  | [] => .missing (fun ref => nomatch ref)
  | head :: rest =>
      match meetsDecision demand head with
      | .isTrue meets => .found head .here meets
      | .isFalse wrong =>
          match findMeeting demand rest with
          | .found item located meets => .found item (.prior located) meets
          | .missing absent => .missing (fun ref meets => match ref with
              | .here => wrong meets
              | .prior old => absent old meets)

inductive GoalDecision (demands : List Demand) (items : List Citation) where
  | complete (witness : Goal demands items)
  | incomplete (missing : Goal demands items → False)

/-- Independent common evaluator of task completion. Incompleteness here
concerns this dossier; it is distinct from impossibility of every future dossier. -/
def decideGoal : (demands : List Demand) → (items : List Citation) → GoalDecision demands items
  | [], items => .complete (.nil items)
  | demand :: rest, items =>
      match findMeeting demand items with
      | .missing absent => .incomplete (fun goal => match goal with
          | .cons _ _ located meets _ => absent located meets)
      | .found item located meets =>
          match decideGoal rest items with
          | .complete tail => .complete (.cons demand item located meets tail)
          | .incomplete missing => .incomplete (fun goal => match goal with
              | .cons _ _ _ _ tail => missing tail)

def goalSucceeded (demands : List Demand) (items : List Citation) : Bool :=
  match decideGoal demands items with
  | .complete _ => true
  | .incomplete _ => false

theorem goalSucceeded_correct (demands : List Demand) (items : List Citation)
    (passed : goalSucceeded demands items = true) : Nonempty (Goal demands items) := by
  unfold goalSucceeded at passed
  cases evaluated : decideGoal demands items with
  | complete witness => exact ⟨witness⟩
  | incomplete missing =>
      rw [evaluated] at passed
      cases passed

theorem goalSucceeded_missing (demands : List Demand) (items : List Citation)
    (failed : goalSucceeded demands items = false) : Goal demands items → False := by
  unfold goalSucceeded at failed
  cases evaluated : decideGoal demands items with
  | complete witness =>
      rw [evaluated] at failed
      cases failed
  | incomplete missing => exact missing

def sourceCitation {context} (sources : Support SourceValue context)
    (origin : Location context) : Citation :=
  ⟨origin.1, origin.2.position, sources.read origin.2⟩

/-- A resource occurrence produced by actually reading the selected input port.
Its formation is total and does not assume publication permission. -/
def extractionProducer {context : List SourceKey} {key}
    (origin : Ref context key) : Producer SourceValue context where
  inputKinds := [key]
  inputs := .cons origin .nil
  outputKind := fun _ => key
  operation := fun arguments => arguments.1

structure Extraction {context} (sources : Support SourceValue context)
    (origin : Location context) where
  private mk ::
  resources : Support SourceValue (origin.1 :: context)
  exact : resources = sources.extend (extractionProducer origin.2)

def extract {context} (sources : Support SourceValue context) (origin : Location context) :
    Extraction sources origin :=
  let produced := sources.extend (extractionProducer origin.2)
  ⟨produced, rfl⟩

def Extraction.citation {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : Citation :=
  ⟨origin.1, origin.2.position, action.resources.read .here⟩

theorem Extraction.citation_exact {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : action.citation = sourceCitation sources origin := by
  rcases action with ⟨resources, exact⟩
  cases exact
  rfl

def Extraction.transport {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : Support.Extension sources action.resources := by
  rcases action with ⟨resources, exact⟩
  cases exact
  exact Support.Extension.produced sources (extractionProducer origin.2)

theorem Extraction.old_read {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) {key} (ref : Ref context key) :
    action.resources.read (action.transport.references ref) = sources.read ref :=
  action.transport.reads ref

theorem Extraction.fresh_distinct {context} {sources : Support SourceValue context} {origin}
    (_action : Extraction sources origin) (old : Ref context origin.1) :
    (Ref.here : Ref (origin.1 :: context) origin.1).position ≠
      (Ref.prior old : Ref (origin.1 :: context) origin.1).position :=
  fresh_position_distinct old

structure Cited {context} (sources : Support SourceValue context) (item : Citation) where
  origin : Location context
  sourceExact : item.source = origin.1
  positionExact : item.position = origin.2.position
  contentExact : item.passage = sources.read origin.2

def Extraction.cited {context} {sources : Support SourceValue context} {origin}
    (action : Extraction sources origin) : Cited sources action.citation := by
  have exact := action.citation_exact
  rw [exact]
  exact ⟨origin, rfl, rfl, rfl⟩

abbrev Conforms {context} (sources : Support SourceValue context)
    (contract : Contract) (item : Citation) :=
  Cited sources item × Ref contract.allowed item.position

structure Output {context} (sources : Support SourceValue context) (contract : Contract) where
  item : Citation
  evidence : Conforms sources contract item

/-- Permission is consumed separately from action formation. The returned
content is the actual produced readout, never a replacement supplied by a model. -/
def authorize {context} {sources : Support SourceValue context} {origin}
    (contract : Contract) (action : Extraction sources origin)
    (permission : Ref contract.allowed origin.2.position) : Output sources contract :=
  ⟨action.citation, action.cited, permission⟩

/-- Positive admissibility supplies a primitive location and permission,
not an already completed dossier or a trace of its future execution. -/
structure Candidate {context} (sources : Support SourceValue context)
    (contract : Contract) (demand : Demand) where
  origin : Location context
  permission : Ref contract.allowed origin.2.position
  meets : Meets demand (sourceCitation sources origin)

inductive Admissible {context} (sources : Support SourceValue context) (contract : Contract) :
    List Demand → Type where
  | nil : Admissible sources contract []
  | cons {demand rest} (head : Candidate sources contract demand)
      (tail : Admissible sources contract rest) : Admissible sources contract (demand :: rest)

def fulfill {context} {sources : Support SourceValue context} {contract demand}
    (candidate : Candidate sources contract demand) :
    {output : Output sources contract // Meets demand output.item} :=
  let action := extract sources candidate.origin
  let output := authorize contract action candidate.permission
  ⟨output, by
    change Meets demand action.citation
    rw [action.citation_exact]
    exact candidate.meets⟩

structure Memory {context} (sources : Support SourceValue context) (contract : Contract) where
  items : List Citation
  valid : {item : Citation} → Ref items item → Conforms sources contract item

def empty {context} (sources : Support SourceValue context) (contract : Contract) :
    Memory sources contract := ⟨[], fun ref => nomatch ref⟩

/-- A single produced element is shared by the successor, receipt and evidence.
The previous dossier occurrences keep their identity through Ref.prior. -/
def incorporate {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (output : Output sources contract) :
    Memory sources contract × Citation :=
  (⟨output.item :: memory.items, fun ref => match ref with
      | .here => output.evidence
      | .prior old => memory.valid old⟩, output.item)

theorem incorporate_old_evidence {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (output : Output sources contract)
    {item} (old : Ref memory.items item) :
    (incorporate memory output).1.valid (.prior old) = memory.valid old := rfl

inductive ExecutionEvidence {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (origin : Location context) :
    (Memory sources contract × Option Citation) → Type where
  | refused (absent : resolvePermission contract.allowed origin.2.position = none) :
      ExecutionEvidence memory origin (memory, none)
  | incorporated (action : Extraction sources origin)
      (permission : Ref contract.allowed origin.2.position) :
      ExecutionEvidence memory origin
        (let produced := incorporate memory (authorize contract action permission)
         (produced.1, some produced.2))

/-- Actual operation and certificate are produced together. The positive
refusal and the permission on incorporation are never supplied by the model. -/
def executeCertified {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (origin : Location context) :
    (result : Memory sources contract × Option Citation) × ExecutionEvidence memory origin result :=
  let action := extract sources origin
  match found : resolvePermission contract.allowed origin.2.position with
  | none => ⟨(memory, none), .refused found⟩
  | some permission =>
      let produced := incorporate memory (authorize contract action permission)
      ⟨(produced.1, some produced.2), .incorporated action permission⟩

def execute {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (origin : Location context) :
    Memory sources contract × Option Citation :=
  (executeCertified memory origin).1

theorem execute_refused {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (origin : Location context)
    (absent : resolvePermission contract.allowed origin.2.position = none) :
    execute memory origin = (memory, none) := by
  dsimp only [execute, executeCertified]
  split
  · rfl
  · rename_i permission present
    cases absent.symm.trans present

theorem execute_allowed {context} {sources : Support SourceValue context} {contract}
    (memory : Memory sources contract) (origin : Location context)
    (permission : Ref contract.allowed origin.2.position)
    (found : resolvePermission contract.allowed origin.2.position = some permission) :
    execute memory origin =
      let produced := incorporate memory (authorize contract (extract sources origin) permission)
      (produced.1, some produced.2) := by
  dsimp only [execute, executeCertified]
  split
  · rename_i absent
    cases absent.symm.trans found
  · rename_i actual actualFound
    have same := Option.some.inj (actualFound.symm.trans found)
    cases same
    rfl

theorem incorporated_goal {context} {sources : Support SourceValue context} {contract demand}
    (memory : Memory sources contract) (candidate : Candidate sources contract demand) :
    Nonempty (Goal [demand] (incorporate memory (fulfill candidate).1).1.items) :=
  ⟨.cons demand (fulfill candidate).1.item .here (fulfill candidate).property (.nil _)⟩

/-- Incompatibility concerns every conforming dossier, not one failed search. -/
theorem forbidden_origin_incompatible {context} {sources : Support SourceValue context}
    {contract : Contract} (demand : Demand) (position : Nat)
    (pinned : demand.origin = some position)
    (absent : resolvePermission contract.allowed position = none)
    (memory : Memory sources contract) : Goal [demand] memory.items → False := by
  intro goal
  cases goal with
  | cons _ item located meets _ =>
      have same : item.position = position := by
        have origin := meets.2.2
        rw [pinned] at origin
        exact origin
      exact resolvePermission_none contract.allowed position absent
        (same ▸ (memory.valid located).2)

def eraseContext {context} {sources : Support SourceValue context} {contract}
    {Context : Type} (state : Memory sources contract × Context) (reset : Context → Context) :
    Memory sources contract × Context := (state.1, reset state.2)

theorem execute_after_context_erasure {context} {sources : Support SourceValue context} {contract}
    {Context : Type} (state : Memory sources contract × Context) (reset : Context → Context)
    (origin : Location context) :
    execute (eraseContext state reset).1 origin = execute state.1 origin := rfl

end ConstitutiveSearch.Agent.Local.Documentary
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SourceKey
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Passage
#print axioms ConstitutiveSearch.Agent.Local.Documentary.SourceValue
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Location
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Citation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Contract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Demand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Meets
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.meetsDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Meeting
#print axioms ConstitutiveSearch.Agent.Local.Documentary.findMeeting
#print axioms ConstitutiveSearch.Agent.Local.Documentary.GoalDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.decideGoal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.goalSucceeded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.goalSucceeded_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.goalSucceeded_missing
#print axioms ConstitutiveSearch.Agent.Local.Documentary.sourceCitation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.extractionProducer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.extract
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction.citation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction.citation_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction.transport
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction.old_read
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction.fresh_distinct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Cited
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Extraction.cited
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Conforms
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.authorize
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Candidate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Admissible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.fulfill
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Memory
#print axioms ConstitutiveSearch.Agent.Local.Documentary.empty
#print axioms ConstitutiveSearch.Agent.Local.Documentary.incorporate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.incorporate_old_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ExecutionEvidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.executeCertified
#print axioms ConstitutiveSearch.Agent.Local.Documentary.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.execute_refused
#print axioms ConstitutiveSearch.Agent.Local.Documentary.execute_allowed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.incorporated_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.forbidden_origin_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.eraseContext
#print axioms ConstitutiveSearch.Agent.Local.Documentary.execute_after_context_erasure
/- AXIOM_AUDIT_END -/
