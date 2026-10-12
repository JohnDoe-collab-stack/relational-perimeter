import Tests.LocalAlignment.DocumentaryControlBindingReader
import Tests.LocalAlignment.DocumentaryControlQuotationAssembly
import Tests.LocalAlignment.DocumentaryControlAssembly
import Tests.LocalAlignment.DocumentaryControlMissingAssembly

/-! Assembly retains a realization of bindings and evidence from the same
received store, extension and output used to form the original complete Step. -/
set_option genInjectivity false
set_option backward.match.sparseCases false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution
open Resources Program Control ControlBindings ControlMasterData ControlDeferred ControlBindingReader ControlReference
variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification}
  {left right : Specification}

structure Produced {spec : Specification} {before : Frame sources contract rules slots}
    {instruction : Instruction context rules slots spec} (expected : Step before instruction) where
  step : Actual expected
  bindings : Reader step.1.next.bindings
  knowledge : KnowledgeRecipe step.1.next.store.2

@[inline] def knowledgeCast (left right : Deduction.Store sources contract rules)
    (same : left = right) (recipe : KnowledgeRecipe left.2) : KnowledgeRecipe right.2 := by
  cases same; exact recipe

def quotationFinishCode (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (task : Dossier.Obligation context) (produced : Dossier.Step before.dossier task)
    (after : Deduction.Store sources contract rules)
    (afterActual : after = Deduction.ingest before.store produced.2)
    (extension : Support.Extension before.store.2.resources after.2.resources)
    (extensionActual : extension = (afterActual.symm ▸
      (match produced.2 with
      | .complete packet => Support.Extension.produced before.store.2.resources (Deduction.quotationProducer packet.output)
      | .blocked _ _ => Support.Extension.identity before.store.2.resources)))
    (references : ReferenceReader extension) (knowledge : KnowledgeRecipe after.2)
    (output : Option (Occurrence after))
    (outputActual : output = (afterActual.symm ▸
      (match produced.2 with | .complete _ => some ⟨_, .here⟩ | .blocked _ _ => none))) :
    Code Label (Produced (quotationStep before task produced)) :=
  .step .assemblyDossier (fun _ =>
    let dossier : Dossier.State sources contract := match produced.2 with
      | .complete packet => ⟨produced.1.next, packet.result.1⟩
      | .blocked _ _ => ⟨produced.1.next, before.dossier.memory⟩
    have dossierActual : dossier = produced.next := by
      obtain ⟨stage, decision⟩ := produced; cases decision <;> rfl
    .step .assemblyFrame (fun _ =>
      let next := assemble before dossier after extension output
      .step .controlClosure (fun _ =>
        let bindings := assembledReader before prior dossier after extension references output
        .step .assemblyPacket (fun _ =>
          let step : Actual (quotationStep before task produced) :=
            ⟨ControlQuotationAssembly.fromParts before task produced after afterActual extension extensionActual output outputActual
                dossier dossierActual next rfl,
              ControlQuotationAssembly.fromParts_actual before task produced after afterActual extension extensionActual output outputActual
                dossier dossierActual next rfl⟩
          .step .executionPayload (fun _ => .done ⟨step, bindings, knowledge⟩)))))

def quotationCode (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (knowledge : KnowledgeRecipe before.store.2) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) : Code Label (Produced (quotationStep before task produced)) :=
  match produced with
  | ⟨stage, .complete packet⟩ =>
    (ControlQuotationAssembly.quoteCode before.store.2 packet.output).bind (fun quoted =>
      .step .assemblyKind (fun _ =>
        let kind := Deduction.Kind.quotation packet.output.item
        .step .assemblyKinds (fun _ =>
          let kinds := kind :: before.store.1
          .step .assemblyStore (fun _ =>
            let after : Deduction.Store sources contract rules := ⟨kinds, quoted.1⟩
            have afterActual : after = Deduction.ingest before.store (.complete packet) := by
              obtain ⟨_, actual⟩ := quoted; cases actual; rfl
            .step .assemblyExtension (fun _ =>
              let extension : Support.Extension before.store.2.resources after.2.resources :=
                afterActual.symm ▸ Support.Extension.produced before.store.2.resources
                  (Deduction.quotationProducer packet.output)
              .step .assemblyOutput (fun _ =>
                let output : Option (Occurrence after) := some ⟨kind, .here⟩
                quotationFinishCode before prior task ⟨stage, .complete packet⟩ after afterActual extension rfl
                  (by obtain ⟨_, actual⟩ := quoted; cases actual
                      exact shiftedAlignedReferenceReader kind rfl extension (fun _ => rfl))
                  (by obtain ⟨_, actual⟩ := quoted; cases actual; exact .quotation knowledge packet.output) output
                  (by obtain ⟨_, actual⟩ := quoted; cases actual; rfl)))))))
  | ⟨stage, .blocked leftImpossible rightImpossible⟩ =>
    .step .assemblyExtension (fun _ =>
      let extension := Support.Extension.identity before.store.2.resources
      .step .assemblyOutput (fun _ =>
        quotationFinishCode before prior task ⟨stage, .blocked leftImpossible rightImpossible⟩ before.store rfl extension rfl
          (identityReferenceReader before.store.2.resources) knowledge none rfl))

theorem quotation_finite (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (knowledge : KnowledgeRecipe before.store.2) (task : Dossier.Obligation context)
    (produced : Dossier.Step before.dossier task) : Finite (quotationCode before prior knowledge task produced) := by
  obtain ⟨stage, decision⟩ := produced
  cases decision with
  | complete packet =>
    apply finite_bind (ControlQuotationAssembly.quote_finite before.store.2 packet.output)
    intro quoted
    repeat apply finite_step
    exact finite_done _
  | blocked _ _ =>
    repeat apply finite_step
    exact finite_done _

def deductionFinishCode (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (request : Deduction.Request rules) (leftSlot : Ref slots left) (rightSlot : Ref slots right)
    (demand : Deduction.Demand) (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (after : {store : Deduction.Store sources contract rules // store = decision.result.1})
    (extension : Support.Extension before.store.2.resources after.1.2.resources)
    (extensionActual : extension = (after.2.symm ▸ decisionExtension decision))
    (references : ReferenceReader extension) (knowledge : KnowledgeRecipe after.1.2)
    (output : Option (Occurrence after.1))
    (outputActual : output = (after.2.symm ▸ decisionOutput decision)) :
    Code Label (Produced (deductionStep before request leftSlot rightSlot demand
      leftOccurrence rightOccurrence leftActual rightActual decision)) :=
  .step .assemblyFrame (fun _ =>
    let next := assemble before before.dossier after.1 extension output
    .step .controlClosure (fun _ =>
      let bindings := assembledReader before prior before.dossier after.1 extension references output
      .step .assemblyPacket (fun _ =>
        let step : Actual (deductionStep before request leftSlot rightSlot demand
            leftOccurrence rightOccurrence leftActual rightActual decision) :=
          ⟨deductionStepFromParts before request leftSlot rightSlot demand
            leftOccurrence rightOccurrence leftActual rightActual decision
            after.1 after.2 extension extensionActual output outputActual next rfl,
            deductionStepFromParts_actual before request leftSlot rightSlot demand
              leftOccurrence rightOccurrence leftActual rightActual decision
              after.1 after.2 extension extensionActual output outputActual next rfl⟩
        .step .executionPayload (fun _ => .done ⟨step, bindings, knowledge⟩))))

@[inline] def deductionReferences {kinds : List Deduction.Kind} {left right : Deduction.Kind}
    (knowledge : Deduction.Knowledge sources contract rules kinds) (request : Deduction.Request rules)
    (leftRef : Ref kinds left) (rightRef : Ref kinds right)
    (action : Deduction.FormationAction knowledge request leftRef rightRef)
    (permission : Ref rules.allowed request.2.position)
    (kind : Actual (Deduction.derivedKind request leftRef rightRef))
    (after : {store : Deduction.Store sources contract rules // store = (Deduction.Decision.accepted action permission).result.1})
    (extension : Support.Extension knowledge.resources after.1.2.resources)
    (extensionActual : extension = after.2.symm ▸ action.transport) : ReferenceReader extension :=
  shiftedAlignedReferenceReader kind.1
    (by rw [after.2, kind.2]; rfl) extension (by
      intro oldKind ref
      obtain ⟨_, actual⟩ := after; cases actual
      obtain ⟨_, actual⟩ := kind; cases actual
      rw [extensionActual]
      obtain ⟨_, actual⟩ := action; cases actual; rfl)

def deductionCode (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (knowledgeRecipe : KnowledgeRecipe before.store.2) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    Code Label (Produced (deductionStep before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision)) :=
  .step .deductionAssembly (fun _ => match decision with
    | .accepted action permission =>
      (positionCode request.2).bind (fun rulePosition =>
      (positionCode leftOccurrence.2).bind (fun leftPosition =>
      (positionCode rightOccurrence.2).bind (fun rightPosition =>
      .step .assemblyKind (fun _ =>
        let kind : {kind : Deduction.Kind // kind = Deduction.derivedKind request leftOccurrence.2 rightOccurrence.2} :=
          ⟨.derived request.1 rulePosition.1 leftOccurrence.1 leftPosition.1 rightOccurrence.1 rightPosition.1, by
            obtain ⟨_, ruleActual⟩ := rulePosition
            obtain ⟨_, leftPositionActual⟩ := leftPosition
            obtain ⟨_, rightPositionActual⟩ := rightPosition
            cases ruleActual; cases leftPositionActual; cases rightPositionActual
            rfl⟩
        .step .assemblyKinds (fun _ =>
          let kinds : {kinds : List Deduction.Kind // kinds = Deduction.derivedKind request leftOccurrence.2 rightOccurrence.2 :: before.store.1} :=
            ⟨kind.1 :: before.store.1, congrArg (fun kind => kind :: before.store.1) kind.2⟩
          .step .assemblyKnowledge (fun _ =>
            let knowledge := Deduction.incorporateDerived action permission
            .step .assemblyStore (fun _ =>
              let aligned : Deduction.Knowledge sources contract rules kinds.1 := kinds.2.symm ▸ knowledge
              let after : {store : Deduction.Store sources contract rules //
                  store = (Deduction.Decision.accepted action permission).result.1} :=
                ⟨⟨kinds.1, aligned⟩, by obtain ⟨_, actualKinds⟩ := kinds; cases actualKinds; rfl⟩
              .step .assemblyExtension (fun _ =>
                let direct : Support.Extension before.store.2.resources action.resources :=
                  ControlAssembly.extensionFromKind action kind
                let extension : Support.Extension before.store.2.resources after.1.2.resources := after.2.symm ▸ direct
                have extensionActual : extension = after.2.symm ▸ action.transport := by
                  have directActual : direct = action.transport := by
                    exact ControlAssembly.extensionFromKind_actual action kind
                  dsimp only [extension]
                  rw [directActual]
                .step .assemblyOutput (fun _ =>
                  let canonical : Occurrence (Deduction.Decision.accepted action permission).result.1 :=
                    ⟨kind.1, Eq.ndrec (motive := fun added => Ref (added :: before.store.1) kind.1)
                      (Ref.here (kind := kind.1) (rest := before.store.1)) kind.2⟩
                  let output : Option (Occurrence after.1) := after.2.symm ▸ some canonical
                  have outputActual : output = after.2.symm ▸ some ⟨_, Ref.here⟩ := by
                    have canonicalActual : canonical = ⟨_, Ref.here⟩ := by
                      obtain ⟨_, actualKind⟩ := kind
                      cases actualKind
                      rfl
                    exact congrArg (fun (out : Option (Occurrence (Deduction.Decision.accepted action permission).result.1)) =>
                      after.2.symm ▸ out) (congrArg some canonicalActual)
                  deductionFinishCode before prior request leftSlot rightSlot demand leftOccurrence rightOccurrence
                    leftActual rightActual (.accepted action permission) after extension extensionActual
                    (deductionReferences before.store.2 request leftOccurrence.2 rightOccurrence.2 action permission kind after extension extensionActual)
                    (.derivedAt knowledgeRecipe request leftOccurrence.2 rightOccurrence.2 action permission
                      kind.1 kind.2 aligned (by obtain ⟨_, actual⟩ := kind; cases actual; rfl))
                    output outputActual)))))))))
    | .refused absent =>
      .step .assemblyExtension (fun _ =>
        let refused : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2 := .refused absent
        let after : {store : Deduction.Store sources contract rules // store = refused.result.1} := ⟨before.store, rfl⟩
        let extension := Support.Extension.identity before.store.2.resources
        .step .assemblyOutput (fun _ =>
          deductionFinishCode before prior request leftSlot rightSlot demand leftOccurrence rightOccurrence
            leftActual rightActual (.refused absent) after extension rfl
            (identityReferenceReader before.store.2.resources) knowledgeRecipe none rfl)))

theorem deduction_finite (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (knowledgeRecipe : KnowledgeRecipe before.store.2) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    Finite (deductionCode before prior knowledgeRecipe request leftSlot rightSlot demand leftOccurrence rightOccurrence leftActual rightActual decision) := by
  apply finite_step
  cases decision with
  | accepted action permission =>
      apply finite_bind ⟨_, _, ⟨positionTrace request.2⟩⟩
      intro rulePosition
      apply finite_bind ⟨_, _, ⟨positionTrace leftOccurrence.2⟩⟩
      intro leftPosition
      apply finite_bind ⟨_, _, ⟨positionTrace rightOccurrence.2⟩⟩
      intro rightPosition
      apply finite_step; apply finite_step; apply finite_step; apply finite_step
      repeat apply finite_step
      exact finite_done _
  | refused absent =>
      repeat apply finite_step
      exact finite_done _

def missingCode (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (knowledge : KnowledgeRecipe before.store.2) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False) :
    Code Label (Produced (missingStep before request leftSlot rightSlot demand missing)) :=
  .step .missingAssembly (fun _ =>
    .step .assemblyExtension (fun _ =>
      let extension := Support.Extension.identity before.store.2.resources
      .step .assemblyOutput (fun _ =>
        let output : Option (Occurrence before.store) := none
        .step .assemblyFrame (fun _ =>
          let next := assemble before before.dossier before.store extension output
          .step .controlClosure (fun _ =>
            let bindings := assembledReader before prior before.dossier before.store extension
              (identityReferenceReader before.store.2.resources) output
            .step .assemblyPacket (fun _ =>
              let step : Actual (missingStep before request leftSlot rightSlot demand missing) :=
                ⟨ControlMissingAssembly.fromParts before request leftSlot rightSlot demand missing extension rfl output rfl next rfl,
                  ControlMissingAssembly.fromParts_actual before request leftSlot rightSlot demand missing extension rfl output rfl next rfl⟩
              .step .executionPayload (fun _ => .done ⟨step, bindings, knowledge⟩)))))))

theorem missing_finite (before : Frame sources contract rules slots) (prior : Reader before.bindings)
    (knowledge : KnowledgeRecipe before.store.2) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (missing : Complete before → False) : Finite (missingCode before prior knowledge request leftSlot rightSlot demand missing) := by
  repeat apply finite_step
  exact finite_done _

end ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.Produced
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.knowledgeCast
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.quotationFinishCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.quotationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.quotation_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.deductionFinishCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.deductionReferences
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.deductionCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.deduction_finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.missingCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssemblyExecution.missing_finite
/- AXIOM_AUDIT_END -/
