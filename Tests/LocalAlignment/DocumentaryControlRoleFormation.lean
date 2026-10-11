import Tests.LocalAlignment.DocumentaryControlMeasuredSchedule
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProfiles
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization

/-! Open role and occurrence construction. Realizations consume the endpoints
already retained by the executed schedule. The original split/merge functions
are formed explicitly; the cost of invoking their assignment query is a
separate deferred-reader obligation, not paid by closure formation. -/
set_option genInjectivity false
set_option maxHeartbeats 8000000
namespace ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation
open SAT EndogenousDecomposition RelationalExtensive Control ControlBindings ControlMasterData

structure Endpoints {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source) where
  left : GeneratedStructuralBranchContext source.rootFormula
  leftExact : left = causalOpeningLeft source run.selected run.fresh
  right : GeneratedStructuralBranchContext source.rootFormula
  rightExact : right = causalOpeningRight source run.selected run.fresh

def endpointsFromThreaded {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : Endpoints (causalStageOfThreadedStage run) :=
  { left := stage.storedSchedule.entry.source
    leftExact := by rw [stage.storedSchedule.entryExact]; rfl
    right := stage.storedSchedule.entry.target
    rightExact := by rw [stage.storedSchedule.entryExact]; rfl }

def endpointsCode {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    Code Label (Actual (endpointsFromThreaded run)) :=
  .step .controlInspect (fun _ => .step .formationResources (fun _ =>
    .done ⟨endpointsFromThreaded run, rfl⟩))

theorem endpoints_bounded {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment} {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : Within (endpointsCode run) 2 :=
  within_step _ _ (within_step _ _ (within_done _))

def splitFunction (parent : StructuralBranchContext) (selected : Var)
    (continuation : StructuralBranchContinuation parent) :
    StructuralBranchContinuation (structuralChildContext parent selected false) ⊕
      StructuralBranchContinuation (structuralChildContext parent selected true) :=
  if valueFalse : continuation.1 selected = false then
    .inl ⟨continuation.1, ⟨valueFalse, continuation.2⟩⟩
  else .inr ⟨continuation.1,
    ⟨bool_true_of_not_false_for_split (continuation.1 selected) valueFalse, continuation.2⟩⟩

def mergeFunction {parent : StructuralBranchContext} {selected : Var} :
    StructuralBranchContinuation (structuralChildContext parent selected false) ⊕
      StructuralBranchContinuation (structuralChildContext parent selected true) →
    StructuralBranchContinuation parent
  | .inl continuation => ⟨continuation.1, continuation.2.2⟩
  | .inr continuation => ⟨continuation.1, continuation.2.2⟩

def openingCode {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source) :
    Code Label (Actual (generatedStructuralSplit source.operationalState run.selected run.fresh)) :=
  .step .controlClosure (fun _ =>
    let split := splitFunction source.operationalState.context run.selected
    .step .controlClosure (fun _ =>
      let merge := mergeFunction (parent := source.operationalState.context) (selected := run.selected)
      .step .formationWitness (fun _ =>
        let opening : AcceptingExactBinarySplit (generatedStructuralBranchSystem source.rootFormula)
            source.operationalState (causalOpeningLeft source run.selected run.fresh)
            (causalOpeningRight source run.selected run.fresh) :=
          { split := split, merge := merge
            splitMerge := (generatedStructuralSplit source.operationalState run.selected run.fresh).splitMerge
            mergeSplit := (generatedStructuralSplit source.operationalState run.selected run.fresh).mergeSplit
            splitPreservesAccept :=
              (generatedStructuralSplit source.operationalState run.selected run.fresh).splitPreservesAccept
            mergePreservesAccept :=
              (generatedStructuralSplit source.operationalState run.selected run.fresh).mergePreservesAccept }
        .done ⟨opening, rfl⟩)))

theorem opening_bounded {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source) :
    Within (openingCode run) 3 :=
  within_step _ _ (within_step _ _ (within_step _ _ (within_done _)))

def roleFromOpening {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source)
    (opening : Actual (generatedStructuralSplit source.operationalState run.selected run.fresh)) :
    RelationalConstitutiveRoleStage run := by
  constructor
  case structuralOpening => exact opening.1
  case reconstructedRelation => exact run.relation
  case reconstructedRelationExact => rfl
  case executedInput => exact run.sourceContinuation
  case executedInputExact => rfl
  case completedOutput => exact run.outputContinuation
  case completedOutputExact => rfl
  case actionExact => exact run.outputExact
  case preservation => exact run.outputAccepted

theorem role_from_opening_actual {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source)
    (opening : Actual (generatedStructuralSplit source.operationalState run.selected run.fresh)) :
    roleFromOpening run opening = relationalConstitutiveRoleStage run := by
  obtain ⟨_, actual⟩ := opening; cases actual; rfl

def roleCode {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source) :
    Code Label (Actual (relationalConstitutiveRoleStage run)) :=
  .step .citationOpening (fun _ => (openingCode run).bind (fun opening =>
    .step .masterConstructionReturn (fun _ => .done
      ⟨roleFromOpening run opening, role_from_opening_actual run opening⟩)))

theorem role_bounded {source : CausalConstitutiveState} (run : CausalConstitutiveStageExecution source) :
    Within (roleCode run) 5 := by
  apply within_step
  apply within_bind (more := 1) (opening_bounded run); intro opening
  exact within_step _ _ (within_done _)

def realizationFromState {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (position : OpeningRolePosition role)
    (state : GeneratedStructuralBranchContext source.rootFormula) (actual : state = position.state role) :
    RoleOpeningOccurrence role :=
  { position := position, state := state
    formationWitness := Eq.rec (motive := fun state _ => RoleFormationAgreement role position state)
      (by cases position <;> exact .formed) actual.symm }

theorem realization_from_state_actual {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (position : OpeningRolePosition role)
    (state : GeneratedStructuralBranchContext source.rootFormula) (actual : state = position.state role) :
    realizationFromState role position state actual = roleOpeningOccurrenceAt role position := by
  cases actual; cases position <;> rfl

def realizationCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (endpoints : Endpoints run)
    (position : OpeningRolePosition role) : Code Label (Actual (roleOpeningOccurrenceAt role position)) :=
  .step .controlInspect (fun _ => match position with
    | .left => .step .formationWitness (fun _ =>
      let occurrence := realizationFromState role .left endpoints.left endpoints.leftExact
      .step .formationValues (fun _ => .done ⟨occurrence, realization_from_state_actual _ _ _ _⟩))
    | .right => .step .formationWitness (fun _ =>
      let occurrence := realizationFromState role .right endpoints.right endpoints.rightExact
      .step .formationValues (fun _ => .done ⟨occurrence, realization_from_state_actual _ _ _ _⟩)))

theorem realization_bounded {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (endpoints : Endpoints run) (position : OpeningRolePosition role) :
    Within (realizationCode role endpoints position) 3 := by
  apply within_step; cases position <;> exact within_step _ _ (within_step _ _ (within_done _))

def identityFromRealization {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (position : OpeningRolePosition role)
    (realized : Actual (roleOpeningOccurrenceAt role position)) : RoleConstitutedOccurrence role := by
  constructor
  case realized => exact realized.1
  case sourceWitness => exact ⟨rfl⟩
  case sourceWitnessExact => rfl
  case formationWitness => exact ⟨⟨rfl⟩, realized.1.formationWitness⟩
  case formationWitnessExact => obtain ⟨_, actual⟩ := realized; cases actual; rfl
  case targetWitness => exact ⟨rfl⟩
  case targetWitnessExact => rfl
  case provenanceWitness => exact ⟨⟨rfl⟩, ⟨rfl⟩, realized.1.formationWitness⟩
  case provenanceWitnessExact => obtain ⟨_, actual⟩ := realized; cases actual; rfl

theorem identity_from_realization_actual {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (position : OpeningRolePosition role)
    (realized : Actual (roleOpeningOccurrenceAt role position)) :
    identityFromRealization role position realized = roleConstitutedOccurrenceAt role position := by
  obtain ⟨_, actual⟩ := realized; cases actual; rfl

def identityCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (endpoints : Endpoints run) (position : OpeningRolePosition role) :
    Code Label (Actual (roleConstitutedOccurrenceAt role position)) :=
  (realizationCode role endpoints position).bind (fun realized =>
    .step .formationWitness (fun _ => .step .formationWitness (fun _ =>
      .step .formationWitness (fun _ => .step .formationWitness (fun _ =>
        .step .formationValues (fun _ => .done
          ⟨identityFromRealization role position realized, identity_from_realization_actual _ _ _⟩))))))

theorem identity_bounded {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (endpoints : Endpoints run) (position : OpeningRolePosition role) :
    Within (identityCode role endpoints position) 8 := by
  apply within_bind (more := 5) (realization_bounded role endpoints position); intro realized
  repeat apply within_step
  exact within_done _

def evidenceCode {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (identity : RoleConstitutedOccurrence role) :
    Code Label (Actual (roleConstitutionEvidence role identity)) :=
  .step .formationWitness (fun _ =>
    .done ⟨⟨identity.sourceWitness, identity.targetWitness, identity.formationWitness, identity.provenanceWitness⟩, rfl⟩)

theorem evidence_bounded {source : CausalConstitutiveState} {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) (identity : RoleConstitutedOccurrence role) :
    Within (evidenceCode role identity) 1 := within_step _ _ (within_done _)

end ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.Endpoints
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.endpointsFromThreaded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.endpointsCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.endpoints_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.splitFunction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.mergeFunction
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.openingCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.opening_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.roleFromOpening
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.role_from_opening_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.roleCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.role_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.realizationFromState
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.realization_from_state_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.realizationCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.realization_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.identityFromRealization
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.identity_from_realization_actual
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.identityCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.identity_bounded
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.evidenceCode
#print axioms ConstitutiveSearch.Agent.Local.Documentary.ControlRoleFormation.evidence_bounded
/- AXIOM_AUDIT_END -/
