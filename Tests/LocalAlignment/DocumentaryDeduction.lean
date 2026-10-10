import Tests.LocalAlignment.DocumentaryDossier

/-! Executable deductions over occurrences incorporated from actual master
outputs. Citation deposits consume authorized output packets; binary deduction
producers read two earlier occurrence ports. Rule admission is separate from
formation, and derived elements never become source citations. -/
set_option genInjectivity false
set_option maxHeartbeats 3000000
namespace ConstitutiveSearch.Agent.Local.Documentary.Deduction
open Resources EndogenousDecomposition

inductive Operation where
  | sum
  | difference

def evaluate : Operation → Int → Int → Int
  | .sum, left, right => left + right
  | .difference, left, right => right - left

structure Rule where
  name : Nat
  operation : Operation

structure Policy where
  rules : List Rule
  allowed : List Nat

abbrev Request (policy : Policy) := (rule : Rule) × Ref policy.rules rule

/-- Positions record the earlier occurrence ports at formation time. -/
inductive Kind where
  | quotation (item : Citation)
  | derived (rule : Rule) (rulePosition : Nat)
      (left : Kind) (leftPosition : Nat) (right : Kind) (rightPosition : Nat)

abbrev Value (_kind : Kind) : Type := Int

def Kind.origins : Kind → List Nat
  | .quotation item => [item.position]
  | .derived _ _ left _ right _ => left.origins ++ right.origins

/-- A justification tree keeps rule occurrences, permissions and source
identities. Its leaves require the original source contract without weakening it. -/
inductive Justified {context} (sources : Support SourceValue context)
    (contract : Contract) (policy : Policy) : Kind → Int → Type where
  | quotation (item : Citation) (evidence : Conforms sources contract item) :
      Justified sources contract policy (.quotation item) (Int.ofNat item.passage.value)
  | derived (request : Request policy)
      (permission : Ref policy.allowed request.2.position)
      {left right : Kind} (leftPosition rightPosition : Nat) {leftValue rightValue : Int}
      (leftEvidence : Justified sources contract policy left leftValue)
      (rightEvidence : Justified sources contract policy right rightValue) :
      Justified sources contract policy
        (.derived request.1 request.2.position left leftPosition right rightPosition)
        (evaluate request.1.operation leftValue rightValue)

structure Knowledge {context} (sources : Support SourceValue context)
    (contract : Contract) (policy : Policy) (kinds : List Kind) where
  resources : Support Value kinds
  valid : {kind : Kind} → (ref : Ref kinds kind) →
    Justified sources contract policy kind (resources.read ref)

def Justified.sources {context sources contract policy kind value} :
    @Justified context sources contract policy kind value → List (Output sources contract)
  | .quotation item evidence => [⟨item, evidence⟩]
  | .derived _ _ _ _ left right => left.sources ++ right.sources

def Justified.rules {context sources contract policy kind value} :
    @Justified context sources contract policy kind value → List Nat
  | .quotation _ _ => []
  | .derived request _ _ _ left right => request.2.position :: (left.rules ++ right.rules)

theorem sourcePositions_append {context sources contract}
    (left right : List (@Output context sources contract)) :
    (left ++ right).map (fun output => output.item.position) =
      left.map (fun output => output.item.position) ++ right.map (fun output => output.item.position) := by
  induction left with
  | nil => rfl
  | cons output rest tail => exact congrArg (List.cons output.item.position) tail

theorem Justified.origins_exact {context sources contract policy kind value}
    (evidence : @Justified context sources contract policy kind value) :
    evidence.sources.map (fun output => output.item.position) = kind.origins := by
  induction evidence with
  | quotation _ _ => rfl
  | derived request permission leftPosition rightPosition left right leftExact rightExact =>
      change (left.sources ++ right.sources).map (fun output => output.item.position) = _
      rw [sourcePositions_append, leftExact, rightExact]
      rfl

def empty {context} (sources : Support SourceValue context)
    (contract : Contract) (policy : Policy) : Knowledge sources contract policy [] :=
  ⟨.given PUnit.unit, fun ref => nomatch ref⟩

/-- Depositing the actual authorized packet is a new incorporation occurrence,
not another source extraction. The produced value is captured from that packet. -/
def quotationProducer {context sources contract kinds}
    (output : @Output context sources contract) : Producer Value kinds where
  inputKinds := []
  inputs := .nil
  outputKind := fun _ => .quotation output.item
  operation := fun _ => Int.ofNat output.item.passage.value

def quote {context sources contract policy kinds}
    (knowledge : @Knowledge context sources contract policy kinds)
    (output : Output sources contract) :
    Knowledge sources contract policy (.quotation output.item :: kinds) :=
  let produced := knowledge.resources.extend (quotationProducer output)
  ⟨produced, fun ref => match ref with
    | .here => .quotation output.item output.evidence
    | .prior old => knowledge.valid old⟩

theorem quote_reads_actual_output {context sources contract policy kinds}
    (knowledge : @Knowledge context sources contract policy kinds)
    (output : Output sources contract) :
    (quote knowledge output).resources.read .here = Int.ofNat output.item.passage.value := rfl

theorem quote_previous_evidence {context sources contract policy kinds}
    (knowledge : @Knowledge context sources contract policy kinds)
    (output : Output sources contract) {kind} (old : Ref kinds kind) :
    (quote knowledge output).valid (.prior old) = knowledge.valid old := rfl

abbrev Store {context} (sources : Support SourceValue context) (contract : Contract)
    (policy : Policy) := (kinds : List Kind) × Knowledge sources contract policy kinds

def ingest {context sources contract policy cursor demand left right memory}
    (store : @Store context sources contract policy)
    {stage : Master.Stage cursor sources contract demand left right}
    (decision : Master.Decision stage memory) : Store sources contract policy :=
  match decision with
  | .complete packet => ⟨_, quote store.2 packet.output⟩
  | .blocked _ _ => store

theorem ingest_length {context sources contract policy cursor demand left right memory}
    (store : @Store context sources contract policy)
    {stage : Master.Stage cursor sources contract demand left right}
    (decision : Master.Decision stage memory) :
    (ingest store decision).1.length = store.1.length +
      (match decision with | .complete _ => 1 | .blocked _ _ => 0) := by
  cases decision with
  | complete _ => rfl
  | blocked _ _ => exact (Nat.add_zero _).symm

/-- The packet used for the next dossier state also supplies the quotation.
The trace and knowledge store share this one actual execution. -/
def quoteAll {context sources contract policy} (start : @Dossier.State context sources contract)
    (store : Store sources contract policy) :
    (tasks : List (Dossier.Obligation context)) →
      (finish : Dossier.State sources contract) ×
        (Store sources contract policy × Dossier.Execution start tasks finish)
  | [] => ⟨start, store, .nil⟩
  | task :: rest =>
      let produced := Dossier.step start task
      let deposited := ingest store produced.2
      let tail := quoteAll produced.next deposited rest
      ⟨tail.1, tail.2.1, .cons produced rfl tail.2.2⟩

theorem quoteAll_goal {context sources contract policy} (start : @Dossier.State context sources contract)
    (store : Store sources contract policy) (tasks : List (Dossier.Obligation context))
    (admissible : Dossier.TaskAdmissible sources contract tasks) :
    Nonempty (Goal (Dossier.demands tasks) (quoteAll start store tasks).1.memory.items) :=
  ⟨(quoteAll start store tasks).2.2.goal admissible⟩

theorem quoteAll_depth {context sources contract policy}
    (start : @Dossier.State context sources contract) (store : Store sources contract policy)
    (tasks : List (Dossier.Obligation context)) :
    (quoteAll start store tasks).1.cursor.depth = start.cursor.depth + tasks.length :=
  (quoteAll start store tasks).2.2.depth

theorem quoteAll_occurrences {context sources contract policy}
    (start : @Dossier.State context sources contract) (store : Store sources contract policy)
    (tasks : List (Dossier.Obligation context)) :
    (quoteAll start store tasks).2.1.1.length = store.1.length +
      (quoteAll start store tasks).2.2.added := by
  induction tasks generalizing start store with
  | nil => rfl
  | cons task rest ih =>
      change (quoteAll (Dossier.step start task).next
        (ingest store (Dossier.step start task).2) rest).2.1.1.length =
          store.1.length + ((Dossier.step start task).added +
            (quoteAll (Dossier.step start task).next
              (ingest store (Dossier.step start task).2) rest).2.2.added)
      rw [ih, ingest_length]
      rcases Dossier.step start task with ⟨stage, decision⟩
      cases decision <;> exact Nat.add_assoc _ _ _

def producer {policy kinds left right} (request : Request policy)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) : Producer Value kinds where
  inputKinds := [left, right]
  inputs := .cons leftRef (.cons rightRef .nil)
  outputKind := fun _ => .derived request.1 request.2.position
    left leftRef.position right rightRef.position
  operation := fun arguments => evaluate request.1.operation arguments.1 arguments.2.1

def derivedKind {policy} {kinds : List Kind} {left right : Kind} (request : Request policy)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) : Kind :=
  .derived request.1 request.2.position left leftRef.position right rightRef.position

structure FormationAction {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right) where
  private mk ::
  resources : Support Value (derivedKind request leftRef rightRef :: kinds)
  actual : resources = knowledge.resources.extend (producer request leftRef rightRef)

def form {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    FormationAction knowledge request leftRef rightRef :=
  let produced := knowledge.resources.extend (producer request leftRef rightRef)
  ⟨produced, rfl⟩

/-- Consume the values already read, keeping the existing producer and its
positive formation. Equalities only align the indices of that formation. -/
def formFromReads {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (leftValue : Int) (rightValue : Int)
    (leftActual : leftValue = knowledge.resources.read leftRef)
    (rightActual : rightValue = knowledge.resources.read rightRef) :
    FormationAction knowledge request leftRef rightRef :=
  let output := evaluate request.1.operation leftValue rightValue
  ⟨⟨(output, knowledge.resources.values), by
      cases leftActual
      cases rightActual
      exact .produced knowledge.resources.formation (producer request leftRef rightRef)⟩,
    by
      cases leftActual
      cases rightActual
      rfl⟩

theorem formFromReads_actual {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (leftValue rightValue : Int)
    (leftActual : leftValue = knowledge.resources.read leftRef)
    (rightActual : rightValue = knowledge.resources.read rightRef) :
    formFromReads knowledge request leftRef rightRef leftValue rightValue leftActual rightActual =
      form knowledge request leftRef rightRef := by
  cases leftActual
  cases rightActual
  rfl

/-- Consume an already constituted producer and the already read arguments.
The retained positive formation stores this producer itself. -/
def formFromProducerReads {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (formed : Producer Value kinds) (formedActual : formed = producer request leftRef rightRef)
    (leftValue rightValue : Int)
    (leftActual : leftValue = knowledge.resources.read leftRef)
    (rightActual : rightValue = knowledge.resources.read rightRef) :
    FormationAction knowledge request leftRef rightRef :=
  let arguments : Values Value formed.inputKinds :=
    (congrArg Producer.inputKinds formedActual).symm ▸ (leftValue, rightValue, PUnit.unit)
  let output := formed.operation arguments
  let positive := Formation.produced knowledge.resources.formation formed
  let alignment :
      Formation Value (context := formed.outputKind (formed.arguments knowledge.resources.values) :: kinds)
        (formed.operation (formed.arguments knowledge.resources.values), knowledge.resources.values) =
      Formation Value (context := derivedKind request leftRef rightRef :: kinds)
        (output, knowledge.resources.values) := by
      cases formedActual
      cases leftActual
      cases rightActual
      rfl
  ⟨⟨(output, knowledge.resources.values), alignment ▸ positive⟩, by
    cases formedActual
    cases leftActual
    cases rightActual
    rfl⟩

theorem formFromProducerReads_actual {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (formed : Producer Value kinds) (formedActual : formed = producer request leftRef rightRef)
    (leftValue rightValue : Int)
    (leftActual : leftValue = knowledge.resources.read leftRef)
    (rightActual : rightValue = knowledge.resources.read rightRef) :
    formFromProducerReads knowledge request leftRef rightRef formed formedActual
      leftValue rightValue leftActual rightActual = form knowledge request leftRef rightRef := by
  cases formedActual
  cases leftActual
  cases rightActual
  rfl

theorem FormationAction.eq_form {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef) :
    action = form knowledge request leftRef rightRef := by
  obtain ⟨resources, actual⟩ := action
  cases actual
  rfl

/-- Package the support actually assembled by the controlled formation. -/
def formFromSupport {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (resources : Support Value (derivedKind request leftRef rightRef :: kinds))
    (actual : resources = knowledge.resources.extend (producer request leftRef rightRef)) :
    FormationAction knowledge request leftRef rightRef := ⟨resources, actual⟩

theorem formFromSupport_actual {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (resources : Support Value (derivedKind request leftRef rightRef :: kinds))
    (actual : resources = knowledge.resources.extend (producer request leftRef rightRef)) :
    formFromSupport knowledge request leftRef rightRef resources actual =
      form knowledge request leftRef rightRef := by
  cases actual
  rfl

theorem FormationAction.value {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef) :
    action.resources.read .here =
      evaluate request.1.operation (knowledge.resources.read leftRef) (knowledge.resources.read rightRef) := by
  rw [action.actual]
  rfl

theorem FormationAction.old_value {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef)
    {kind} (old : Ref kinds kind) :
    action.resources.read (.prior old) = knowledge.resources.read old := by
  rw [action.actual]
  rfl

def incorporateDerived {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef)
    (permission : Ref policy.allowed request.2.position) :
    Knowledge sources contract policy (derivedKind request leftRef rightRef :: kinds) :=
  ⟨action.resources, fun ref => match ref with
    | .here => action.value.symm ▸ Justified.derived request permission
        leftRef.position rightRef.position (knowledge.valid leftRef) (knowledge.valid rightRef)
    | .prior old => (action.old_value old).symm ▸ knowledge.valid old⟩

theorem incorporation_uses_actual_resources {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef)
    (permission : Ref policy.allowed request.2.position) :
    (incorporateDerived action permission).resources = action.resources := rfl

def FormationAction.transport {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef) :
    Support.Extension knowledge.resources action.resources := by
  rcases action with ⟨produced, actual⟩
  cases actual
  exact Support.Extension.produced knowledge.resources (producer request leftRef rightRef)

theorem incorporation_previous_evidence {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef)
    (permission : Ref policy.allowed request.2.position) {kind} (old : Ref kinds kind) :
    (incorporateDerived action permission).valid (.prior old) =
      (action.old_value old).symm ▸ knowledge.valid old := rfl

inductive Decision {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right) where
  | accepted (action : FormationAction knowledge request leftRef rightRef)
      (permission : Ref policy.allowed request.2.position)
  | refused (absent : resolvePermission policy.allowed request.2.position = none)

def execute {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    Decision knowledge request leftRef rightRef :=
  match found : resolvePermission policy.allowed request.2.position with
  | none => .refused found
  | some permission =>
      let action := form knowledge request leftRef rightRef
      .accepted action permission

def Decision.result {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (decision : @Decision context sources contract policy kinds left right knowledge request leftRef rightRef) :
    Store sources contract policy × Option Int :=
  match decision with
  | .refused _ => (⟨kinds, knowledge⟩, none)
  | .accepted action permission =>
      let next := incorporateDerived action permission
      (⟨_, next⟩, some (next.resources.read .here))

theorem execute_refused {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (absent : resolvePermission policy.allowed request.2.position = none) :
    (execute knowledge request leftRef rightRef).result = (⟨kinds, knowledge⟩, none) := by
  unfold execute
  split
  · rfl
  · rename_i permission present
    cases absent.symm.trans present

/-- The received goal states an output and optional rule occurrence, independently
of execution and admission. A numerical match alone does not give rule identity. -/
structure Demand where
  value : Int
  rulePosition : Option Nat
  origins : Option (List Nat) := none

def Meets (demand : Demand) (kind : Kind) (value : Int) : Prop :=
  value = demand.value ∧ (match kind with
    | .quotation _ => False
    | .derived _ position _ _ _ _ =>
        match demand.rulePosition with
        | none => True
        | some pinned => position = pinned) ∧
    (match demand.origins with | none => True | some received => kind.origins = received)

def meetsDecision (demand : Demand) (kind : Kind) (value : Int) : Decidable (Meets demand kind value) := by
  unfold Meets
  cases kind <;> cases demand.rulePosition <;> cases demand.origins <;> infer_instance

def meetsCheck (demand : Demand) (kind : Kind) (value : Int) : Bool :=
  match meetsDecision demand kind value with | .isTrue _ => true | .isFalse _ => false

theorem meetsCheck_correct (demand : Demand) (kind : Kind) (value : Int)
    (passed : meetsCheck demand kind value = true) : Meets demand kind value := by
  unfold meetsCheck at passed
  split at passed
  · assumption
  · cases passed

structure Goal (demand : Demand) (kinds : List Kind) (values : Support Value kinds) where
  kind : Kind
  located : Ref kinds kind
  meets : Meets demand kind (values.read located)

theorem actual_conclusion_goal {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef)
    (permission : Ref policy.allowed request.2.position) (demand : Demand)
    (correct : evaluate request.1.operation (knowledge.resources.read leftRef)
      (knowledge.resources.read rightRef) = demand.value)
    (origin : match demand.rulePosition with | none => True | some p => request.2.position = p)
    (dependencies : match demand.origins with
      | none => True
      | some received => (derivedKind request leftRef rightRef).origins = received) :
    Nonempty (Goal demand (derivedKind request leftRef rightRef :: kinds) (incorporateDerived action permission).resources) :=
  ⟨⟨derivedKind request leftRef rightRef, .here,
    ⟨(congrArg (fun resources => resources.read .here) (incorporation_uses_actual_resources action permission)).trans
      (action.value.trans correct), origin, dependencies⟩⟩⟩

def transportGoal {demand before after} {old : Support Value before} {new : Support Value after}
    (extension : Support.Extension old new) (goal : Goal demand before old) : Goal demand after new :=
  ⟨goal.kind, extension.references goal.located,
    (extension.reads goal.located).symm ▸ goal.meets⟩

def incorporation_previous_goal {context sources contract policy kinds left right knowledge request leftRef rightRef demand}
    (action : @FormationAction context sources contract policy kinds left right knowledge request leftRef rightRef)
    (permission : Ref policy.allowed request.2.position)
    (goal : Goal demand kinds knowledge.resources) :
    Goal demand (derivedKind request leftRef rightRef :: kinds) (incorporateDerived action permission).resources :=
  transportGoal action.transport goal

theorem execute_goal {context sources contract policy kinds left right}
    (knowledge : @Knowledge context sources contract policy kinds)
    (request : Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (permission : Ref policy.allowed request.2.position) (demand : Demand)
    (correct : evaluate request.1.operation (knowledge.resources.read leftRef)
      (knowledge.resources.read rightRef) = demand.value)
    (origin : match demand.rulePosition with | none => True | some p => request.2.position = p)
    (dependencies : match demand.origins with
      | none => True
      | some received => (derivedKind request leftRef rightRef).origins = received) :
    Nonempty (Goal demand (execute knowledge request leftRef rightRef).result.1.1
      (execute knowledge request leftRef rightRef).result.1.2.resources) :=
  match execute knowledge request leftRef rightRef with
  | .accepted action admitted => actual_conclusion_goal action admitted demand correct origin dependencies
  | .refused absent => False.elim (resolvePermission_none policy.allowed request.2.position absent permission)

theorem justified_forbidden {context sources contract policy kind value}
    (evidence : @Justified context sources contract policy kind value) (demand : Demand) (position : Nat)
    (pinned : demand.rulePosition = some position)
    (absent : resolvePermission policy.allowed position = none)
    (meets : Meets demand kind value) : False := by
  cases evidence with
  | quotation item evidence => exact meets.2.1
  | derived request permission leftPosition rightPosition leftEvidence rightEvidence =>
      have same : request.2.position = position := by
        have origin := meets.2.1
        rw [pinned] at origin
        exact origin
      exact resolvePermission_none policy.allowed position absent (same ▸ permission)

theorem forbidden_rule_incompatible {context sources contract policy kinds}
    (knowledge : @Knowledge context sources contract policy kinds) (demand : Demand) (position : Nat)
    (pinned : demand.rulePosition = some position)
    (absent : resolvePermission policy.allowed position = none) :
    Goal demand kinds knowledge.resources → False :=
  fun goal => justified_forbidden (knowledge.valid goal.located) demand position pinned absent goal.meets

theorem execute_after_context_erasure {context sources contract policy kinds left right}
    {Context : Type} (state : @Knowledge context sources contract policy kinds × Context)
    (reset : Context → Context) (request : Request policy)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    execute (state.1, reset state.2).1 request leftRef rightRef =
      execute state.1 request leftRef rightRef := rfl

end ConstitutiveSearch.Agent.Local.Documentary.Deduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.FormationAction.eq_form
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.formFromSupport
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.formFromSupport_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.formFromProducerReads
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.formFromProducerReads_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.formFromReads
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.formFromReads_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Operation
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.evaluate
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Rule
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Policy
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Request
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Kind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Kind.origins
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Justified
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Knowledge
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Justified.sources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Justified.rules
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.sourcePositions_append
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Justified.origins_exact
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.empty
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quotationProducer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quote
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quote_reads_actual_output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quote_previous_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Store
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.ingest
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.ingest_length
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quoteAll
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quoteAll_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quoteAll_depth
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.quoteAll_occurrences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.producer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.derivedKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.FormationAction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.form
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.FormationAction.value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.FormationAction.old_value
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.incorporateDerived
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.incorporation_uses_actual_resources
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.FormationAction.transport
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.incorporation_previous_evidence
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Decision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.execute
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Decision.result
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.execute_refused
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Demand
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Meets
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.meetsDecision
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.meetsCheck
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.meetsCheck_correct
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.Goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.actual_conclusion_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.transportGoal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.incorporation_previous_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.execute_goal
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.justified_forbidden
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.forbidden_rule_incompatible
#print axioms ConstitutiveSearch.Agent.Local.Documentary.Deduction.execute_after_context_erasure
/- AXIOM_AUDIT_END -/
