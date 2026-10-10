import Tests.LocalAlignment.DocumentaryControlDeduction

/-! Controlled deduction assembly. The actual action supplies the support;
reference positions, store, extension, output, frame and final packet are paid
before construction. Deferred binding and justification reads are separate
future operations. Administrative interpreter allocations are not heap costs. -/
set_option genInjectivity false
set_option maxHeartbeats 4000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly
open Resources Program Control ControlBindings ControlReference

variable {context : List SourceKey} {sources : Support SourceValue context}
  {contract : Contract} {rules : Deduction.Policy} {slots : List Specification}
  {left right : Specification}

def extensionFromKind {kinds : List Deduction.Kind} {left right : Deduction.Kind}
    {knowledge : Deduction.Knowledge sources contract rules kinds} {request : Deduction.Request rules}
    {leftRef : Ref kinds left} {rightRef : Ref kinds right}
    (action : Deduction.FormationAction knowledge request leftRef rightRef)
    (kind : {kind : Deduction.Kind // kind = Deduction.derivedKind request leftRef rightRef}) :
    Support.Extension knowledge.resources action.resources :=
  ⟨fun ref => kind.2 ▸ Ref.prior (added := kind.1) ref,
    by obtain ⟨_, actualKind⟩ := kind; cases actualKind; exact action.old_value,
    by obtain ⟨_, actualKind⟩ := kind; cases actualKind; exact prior_injective,
    1, by obtain ⟨_, actualKind⟩ := kind; cases actualKind; exact fun _ => rfl⟩

theorem extensionFromKind_actual {kinds : List Deduction.Kind} {left right : Deduction.Kind}
    {knowledge : Deduction.Knowledge sources contract rules kinds} {request : Deduction.Request rules}
    {leftRef : Ref kinds left} {rightRef : Ref kinds right}
    (action : Deduction.FormationAction knowledge request leftRef rightRef)
    (kind : {kind : Deduction.Kind // kind = Deduction.derivedKind request leftRef rightRef}) :
    extensionFromKind action kind = action.transport := by
  obtain ⟨_, actualKind⟩ := kind
  cases actualKind
  obtain ⟨resources, actual⟩ := action
  cases actual
  rfl

abbrev Packet (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :=
  {produced : Step before (.conclusion request leftSlot rightSlot demand) //
    produced = deductionStep before request leftSlot rightSlot demand
      leftOccurrence rightOccurrence leftActual rightActual decision}

def finishCode (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (after : {store : Deduction.Store sources contract rules // store = decision.result.1})
    (extension : Support.Extension before.store.2.resources after.1.2.resources)
    (extensionActual : extension = (after.2.symm ▸ decisionExtension decision))
    (output : Option (Occurrence after.1))
    (outputActual : output = (after.2.symm ▸ decisionOutput decision)) :
    Code Label (Packet before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision) :=
  .step .assemblyFrame (fun _ =>
    let next := assemble before before.dossier after.1 extension output
    .step .assemblyPacket (fun _ =>
      .done ⟨deductionStepFromParts before request leftSlot rightSlot demand
        leftOccurrence rightOccurrence leftActual rightActual decision
        after.1 after.2 extension extensionActual output outputActual next rfl,
        deductionStepFromParts_actual before request leftSlot rightSlot demand
          leftOccurrence rightOccurrence leftActual rightActual decision
          after.1 after.2 extension extensionActual output outputActual next rfl⟩))

theorem finish_bounded (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (after : {store : Deduction.Store sources contract rules // store = decision.result.1})
    (extension : Support.Extension before.store.2.resources after.1.2.resources)
    (extensionActual : extension = (after.2.symm ▸ decisionExtension decision))
    (output : Option (Occurrence after.1))
    (outputActual : output = (after.2.symm ▸ decisionOutput decision)) :
    Within (finishCode before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision after extension extensionActual output outputActual) 2 :=
  within_step _ _ (within_step _ _ (within_done _))

def code (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    Code Label (Packet before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision) :=
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
                  extensionFromKind action kind
                let extension : Support.Extension before.store.2.resources after.1.2.resources := after.2.symm ▸ direct
                have extensionActual : extension = after.2.symm ▸ action.transport := by
                  have directActual : direct = action.transport := by
                    exact extensionFromKind_actual action kind
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
                  finishCode before request leftSlot rightSlot demand leftOccurrence rightOccurrence
                    leftActual rightActual (.accepted action permission) after extension extensionActual output outputActual)))))))))
    | .refused absent =>
      .step .assemblyExtension (fun _ =>
        let refused : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2 := .refused absent
        let after : {store : Deduction.Store sources contract rules // store = refused.result.1} := ⟨before.store, rfl⟩
        let extension := Support.Extension.identity before.store.2.resources
        .step .assemblyOutput (fun _ =>
          finishCode before request leftSlot rightSlot demand leftOccurrence rightOccurrence
            leftActual rightActual (.refused absent) after extension rfl none rfl)))

def bound (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) : Nat :=
  match decision with
  | .accepted _ _ =>
      (positionBound request.2 + (positionBound leftOccurrence.2 + (positionBound rightOccurrence.2 + 8))) + 1
  | .refused _ => 5

theorem bounded (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    Within (code before request leftSlot rightSlot demand leftOccurrence rightOccurrence leftActual rightActual decision)
      (bound before request leftOccurrence rightOccurrence decision) := by
  cases decision with
  | accepted action permission =>
      apply within_step
      apply within_bind (position_bounded request.2)
      intro rulePosition
      apply within_bind (position_bounded leftOccurrence.2)
      intro leftPosition
      apply within_bind (position_bounded rightOccurrence.2)
      intro rightPosition
      apply within_step; apply within_step; apply within_step; apply within_step
      apply within_step; apply within_step; apply within_step; apply within_step
      exact within_done _
  | refused absent =>
      apply within_step
      apply within_step; apply within_step; apply within_step; apply within_step
      exact within_done _

theorem finite (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2) :
    Finite (code before request leftSlot rightSlot demand leftOccurrence rightOccurrence leftActual rightActual decision) := by
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
      apply finite_step; apply finite_step; apply finite_step; apply finite_step
      exact finite_done _
  | refused absent =>
      apply finite_step; apply finite_step; apply finite_step; apply finite_step
      exact finite_done _

theorem actual_step (before : Frame sources contract rules slots) (request : Deduction.Request rules)
    (leftSlot : Ref slots left) (rightSlot : Ref slots right) (demand : Deduction.Demand)
    (leftOccurrence rightOccurrence : Occurrence before.store)
    (leftActual : before.bindings leftSlot = some leftOccurrence)
    (rightActual : before.bindings rightSlot = some rightOccurrence)
    (decision : Deduction.Decision before.store.2 request leftOccurrence.2 rightOccurrence.2)
    (fuel : Nat) (actual : Result (code before request leftSlot rightSlot demand leftOccurrence rightOccurrence
      leftActual rightActual decision) fuel) :
    actual.value.1 = deductionStep before request leftSlot rightSlot demand
      leftOccurrence rightOccurrence leftActual rightActual decision := actual.value.2

end ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.Packet
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.extensionFromKind
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.extensionFromKind_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.finishCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.finish_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.code
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.bound
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.finite
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlAssembly.actual_step
/- AXIOM_AUDIT_END -/
