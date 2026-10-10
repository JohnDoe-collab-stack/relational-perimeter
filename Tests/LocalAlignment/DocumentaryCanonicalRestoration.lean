import Tests.LocalAlignment.DocumentaryPortable

/-! Faithful restoration for arbitrary finite canonical documentary formations.
The language uses the received source/rule configuration and the existing actual
quotation and binary-rule producers. The loader constructs witnesses directly;
the theorem does not replay those producers. This is a component of the complete
present checkpoint, not a serialization of the higher-order master cursor. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration
open Resources Portable

theorem locate_reference {Kind : Type} {kinds : List Kind} {kind : Kind}
    (ref : Ref kinds kind) : Adaptive.locate kinds ref.position = some ⟨kind, ref⟩ := by
  induction ref with
  | here => rfl
  | @prior kind added rest old ih =>
      exact congrArg (fun found : Option ((k : Kind) × Ref rest k) =>
        match found with
        | none => none
        | some prior => some (⟨prior.1, .prior prior.2⟩ : (k : Kind) × Ref (added :: rest) k)) ih

def canonicalOutput {context} (sources : Support SourceValue context) (contract : Contract)
    (origin : Location context) (permission : Ref contract.allowed origin.2.position) :
    Output sources contract :=
  ⟨sourceCitation sources origin, ⟨⟨origin, rfl, rfl, rfl⟩, permission⟩⟩

theorem canonicalOutput_actual {context} (sources : Support SourceValue context) (contract : Contract)
    (origin : Location context) (permission : Ref contract.allowed origin.2.position) :
    canonicalOutput sources contract origin permission =
      authorize contract (extract sources origin) permission := rfl

theorem quotation_layer {context sources contract policy}
    (old : @Deduction.Store context sources contract policy) (origin : Location context)
    (permission : Ref contract.allowed origin.2.position)
    (admitted : resolvePermission contract.allowed origin.2.position = some permission) :
    loadNode sources contract policy old
      (.quotation origin.2.position (Int.ofNat (sources.read origin.2).value)) =
      .ok ⟨_, Deduction.quote old.2 (canonicalOutput sources contract origin permission)⟩ := by
  dsimp only [loadNode]
  rw [locate_reference origin.2]
  dsimp only [require, Bind.bind, Except.bind]
  rw [admitted]
  dsimp only [require, Bind.bind, Except.bind]
  split
  · rfl
  · rename_i impossible
    exact False.elim (impossible rfl)

theorem derived_layer {context sources contract policy}
    (old : @Deduction.Store context sources contract policy) (request : Deduction.Request policy)
    {left right : Deduction.Kind} (leftRef : Ref old.1 left) (rightRef : Ref old.1 right)
    (permission : Ref policy.allowed request.2.position)
    (admitted : resolvePermission policy.allowed request.2.position = some permission)
    (action : Deduction.FormationAction old.2 request leftRef rightRef) :
    loadNode sources contract policy old
      (.derived request.2.position leftRef.position rightRef.position
        (action.resources.read .here)) =
      .ok ⟨_, Deduction.incorporateDerived action permission⟩ := by
  rcases action with ⟨resources, actual⟩
  cases actual
  dsimp only [loadNode]
  rw [locate_reference request.2]
  dsimp only [require, Bind.bind, Except.bind]
  rw [admitted]
  dsimp only [require, Bind.bind, Except.bind]
  rw [locate_reference leftRef, locate_reference rightRef]
  dsimp only [require, Bind.bind, Except.bind]
  split
  · rfl
  · rename_i impossible
    exact False.elim (impossible rfl)

/-- A positive formation history. Each deduction retains the actual action
already executed; its successor consumes that action. The admission equations
refer to the unchanged received permissions, including their occurrences. -/
inductive Formed {context} (sources : Support SourceValue context) (contract : Contract)
    (policy : Deduction.Policy) : Deduction.Store sources contract policy → Type where
  | empty : Formed sources contract policy ⟨[], Deduction.empty sources contract policy⟩
  | quotation {old} (prior : Formed sources contract policy old) (origin : Location context)
      (permission : Ref contract.allowed origin.2.position)
      (admitted : resolvePermission contract.allowed origin.2.position = some permission) :
      Formed sources contract policy
        ⟨_, Deduction.quote old.2 (canonicalOutput sources contract origin permission)⟩
  | derived {old} (prior : Formed sources contract policy old) (request : Deduction.Request policy)
      {left right : Deduction.Kind} (leftRef : Ref old.1 left) (rightRef : Ref old.1 right)
      (permission : Ref policy.allowed request.2.position)
      (admitted : resolvePermission policy.allowed request.2.position = some permission)
      (action : Deduction.FormationAction old.2 request leftRef rightRef) :
      Formed sources contract policy ⟨_, Deduction.incorporateDerived action permission⟩

def decisionPermission {context sources contract policy kinds left right knowledge request leftRef rightRef}
    (decision : @Deduction.Decision context sources contract policy kinds left right knowledge request leftRef rightRef) :
    Option (Ref policy.allowed request.2.position) :=
  match decision with
  | .refused _ => none
  | .accepted _ permission => some permission

theorem actual_decision_permission {context sources contract policy kinds left right}
    (knowledge : @Deduction.Knowledge context sources contract policy kinds)
    (request : Deduction.Request policy) (leftRef : Ref kinds left) (rightRef : Ref kinds right) :
    decisionPermission (Deduction.execute knowledge request leftRef rightRef) =
      resolvePermission policy.allowed request.2.position := by
  unfold Deduction.execute
  split
  · exact (by assumption : resolvePermission policy.allowed request.2.position = none).symm
  · exact (by assumption : resolvePermission policy.allowed request.2.position = some _).symm

/-- Consume the passed actual decision and its action, rather than constructing
an independent deduction for the restoration certificate. Refusal retains the
previous formation and contributes no fictitious node. -/
def decision_formed {context sources contract policy store}
    (prior : @Formed context sources contract policy store) (request : Deduction.Request policy)
    {left right : Deduction.Kind} (leftRef : Ref store.1 left) (rightRef : Ref store.1 right)
    (decision : Deduction.Decision store.2 request leftRef rightRef)
    (actual : decision = Deduction.execute store.2 request leftRef rightRef) :
    Formed sources contract policy decision.result.1 :=
  match decision with
  | .refused _ => prior
  | .accepted action permission =>
      .derived prior request leftRef rightRef permission
        ((actual_decision_permission store.2 request leftRef rightRef).symm.trans
          (congrArg decisionPermission actual).symm) action

theorem checked_candidate_permission {context sources contract demand origin}
    (checked : @Selection.Checked context sources contract demand origin)
    (actual : checked = Selection.check sources contract demand origin)
    (accepted : checked.flag = true) :
    resolvePermission contract.allowed (checked.candidate accepted).origin.2.position =
      some (checked.candidate accepted).permission := by
  cases actual
  revert accepted
  unfold Selection.check
  split
  · intro accepted
    cases accepted
  · rename_i permission admitted
    dsimp only
    split
    · intro accepted
      exact admitted
    · intro accepted
      cases accepted

def candidateFor {context sources contract demand left right}
    (leftCheck : @Selection.Checked context sources contract demand left)
    (rightCheck : Selection.Checked sources contract demand right) (value : Bool)
    (eligible : (if value then rightCheck.flag else leftCheck.flag) = true) :
    Candidate sources contract demand := by
  cases same : value
  · rw [same] at eligible
    exact leftCheck.candidate eligible
  · rw [same] at eligible
    exact rightCheck.candidate eligible

theorem candidateFor_permission {context sources contract demand left right}
    (leftCheck : @Selection.Checked context sources contract demand left)
    (rightCheck : Selection.Checked sources contract demand right)
    (leftActual : leftCheck = Selection.check sources contract demand left)
    (rightActual : rightCheck = Selection.check sources contract demand right)
    (value : Bool) (eligible : (if value then rightCheck.flag else leftCheck.flag) = true) :
    resolvePermission contract.allowed (candidateFor leftCheck rightCheck value eligible).origin.2.position =
      some (candidateFor leftCheck rightCheck value eligible).permission := by
  cases value
  · exact checked_candidate_permission leftCheck leftActual eligible
  · exact checked_candidate_permission rightCheck rightActual eligible

theorem stage_candidate_permission {context cursor sources contract demand left right}
    (stage : @Master.Stage context cursor sources contract demand left right)
    (assignment : SAT.Assignment) (accepted : SAT.Satisfies assignment stage.formula) :
    resolvePermission contract.allowed (stage.candidate assignment accepted).origin.2.position =
      some (stage.candidate assignment accepted).permission := by
  have eligible := (Selection.choiceFormula_exact
    (EndogenousDecomposition.VariableMaster.selected stage.head) stage.leftCheck.flag stage.rightCheck.flag
    assignment).1 accepted
  change resolvePermission contract.allowed
    (candidateFor stage.leftCheck stage.rightCheck
      (assignment (EndogenousDecomposition.VariableMaster.selected stage.head)) eligible).origin.2.position = _
  exact candidateFor_permission stage.leftCheck stage.rightCheck stage.leftExact stage.rightExact _ eligible

theorem packet_permission {context cursor sources contract demand left right stage memory}
    (packet : @Master.Completion context cursor sources contract demand left right stage memory) :
    resolvePermission contract.allowed packet.candidate.origin.2.position = some packet.candidate.permission := by
  rw [packet.candidateExact]
  exact stage_candidate_permission stage _ _

theorem packet_output {context cursor sources contract demand left right stage memory}
    (packet : @Master.Completion context cursor sources contract demand left right stage memory) :
    packet.output = canonicalOutput sources contract packet.candidate.origin packet.candidate.permission := by
  rw [packet.outputExact, packet.actionExact]
  rfl

def packet_formed {context sources contract policy store cursor demand left right stage memory}
    (prior : @Formed context sources contract policy store)
    (packet : @Master.Completion context cursor sources contract demand left right stage memory) :
    Formed sources contract policy ⟨_, Deduction.quote store.2 packet.output⟩ := by
  rw [packet_output packet]
  exact .quotation prior packet.candidate.origin packet.candidate.permission (packet_permission packet)

def quotationStep_formed {context sources contract policy slots}
    (before : @Program.Frame context sources contract policy slots)
    (prior : Formed sources contract policy before.store) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) :
    Formed sources contract policy (Program.quotationStep before task produced).next.store :=
  match produced with
  | ⟨_, .complete packet⟩ => packet_formed prior packet
  | ⟨_, .blocked _ _⟩ => prior

theorem step_formed {context sources contract policy slots spec}
    (before : @Program.Frame context sources contract policy slots)
    (prior : Formed sources contract policy before.store)
    (instruction : Program.Instruction context policy slots spec)
    (produced : Program.Step before instruction) (actual : produced = Program.step before instruction) :
    Nonempty (Formed sources contract policy produced.next.store) := by
  cases actual
  cases instruction with
  | quotation task => exact ⟨quotationStep_formed before prior task (Dossier.step before.dossier task)⟩
  | conclusion request leftSlot rightSlot demand =>
      dsimp only [Program.step]
      split
      · exact ⟨prior⟩
      · rename_i leftOccurrence leftActual
        split
        · exact ⟨prior⟩
        · rename_i rightOccurrence rightActual
          have next := decision_formed prior request leftOccurrence.2 rightOccurrence.2
            (Deduction.execute before.store.2 request leftOccurrence.2 rightOccurrence.2) rfl
          cases chosen : Deduction.execute before.store.2 request leftOccurrence.2 rightOccurrence.2
          all_goals rw [chosen] at next
          all_goals exact ⟨next⟩

/-- The actual trace supplies its shared steps. The theorem neither requires
task success nor replaces permitted-but-unsuitable outputs, refusals or missing
bindings by a successful alternate execution. -/
theorem execution_formed {context sources contract policy before after start script finish}
    (trace : @Program.Execution context sources contract policy before after start script finish)
    (initial : Formed sources contract policy start.store) :
    Nonempty (Formed sources contract policy finish.store) := by
  induction trace with
  | done => exact ⟨initial⟩
  | cons produced actual rest ih =>
      rcases step_formed _ initial _ produced actual with ⟨next⟩
      exact ih next

/-- Exact equality of the dependent store, including formation producers and
justification readers. No equality of values is used in place of this equality. -/
theorem store_roundtrip {context sources contract policy store}
    (formed : @Formed context sources contract policy store) :
    loadStore sources contract policy (record store) = .ok store := by
  induction formed with
  | empty => rfl
  | quotation prior origin permission admitted ih =>
      change (do
        let old ← loadStore sources contract policy (record _)
        loadNode sources contract policy old
          (.quotation origin.2.position (Int.ofNat (sources.read origin.2).value))) = _
      rw [ih]
      exact quotation_layer _ origin permission admitted
  | derived prior request leftRef rightRef permission admitted action ih =>
      rcases action with ⟨resources, actual⟩
      cases actual
      change (do
        let old ← loadStore sources contract policy (record _)
        loadNode sources contract policy old
          (.derived request.2.position leftRef.position rightRef.position
            ((Deduction.form _ request leftRef rightRef).resources.read .here))) = _
      rw [ih]
      exact derived_layer _ request leftRef rightRef permission admitted (Deduction.form _ request leftRef rightRef)

theorem execution_store_roundtrip {context sources contract policy before after start script finish}
    (trace : @Program.Execution context sources contract policy before after start script finish)
    (initial : Formed sources contract policy start.store) :
    loadStore sources contract policy (record finish.store) = .ok finish.store := by
  rcases execution_formed trace initial with ⟨formed⟩
  exact store_roundtrip formed

end ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.locate_reference
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.canonicalOutput
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.canonicalOutput_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.quotation_layer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.derived_layer
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.Formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.decisionPermission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.actual_decision_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.decision_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.checked_candidate_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.candidateFor
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.candidateFor_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.stage_candidate_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.packet_permission
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.packet_output
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.packet_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.quotationStep_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.step_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.execution_formed
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.store_roundtrip
#print axioms ConstitutiveSearch.Agent.Local.Documentary.CanonicalRestoration.execution_store_roundtrip
/- AXIOM_AUDIT_END -/
