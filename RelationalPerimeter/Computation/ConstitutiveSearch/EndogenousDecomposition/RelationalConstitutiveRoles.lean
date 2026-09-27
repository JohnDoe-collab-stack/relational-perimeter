import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalConstitutiveExecution

/-!
# Relational constitutive roles determined by causal execution

A role stage is not a free label.  It is the exact reading, at one executed
stage, of the search state, the binary opening, the reconstructed relation, the
relation's total action, its separate preservation result, and the next state.
The role history follows the dependent tail of the causal history.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT

/-- The relational functions constituted together by one executed stage. -/
structure RelationalConstitutiveRoleStage
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source) where
  private mk ::
  searchState : CausalConstitutiveState
  searchStateExact : searchState = source
  structuralOpening :
    AcceptingExactBinarySplit
      (generatedStructuralBranchSystem source.rootFormula)
      source.operationalState
      (causalOpeningLeft source run.selected run.fresh)
      (causalOpeningRight source run.selected run.fresh)
  reconstructedRelation :
    GeneratedStructuralFlipAtRelation run.selected
      (causalOpeningLeft source run.selected run.fresh)
      (causalOpeningRight source run.selected run.fresh)
  reconstructedRelationExact : reconstructedRelation = run.relation
  executedInput :
    GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)
  executedInputExact : executedInput = run.sourceContinuation
  completedOutput :
    GeneratedStructuralBranchContinuation
      (causalOpeningRight source run.selected run.fresh)
  completedOutputExact : completedOutput = run.outputContinuation
  actionExact :
    completedOutput = reconstructedRelation.mapContinuation executedInput
  preservation :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      completedOutput
  nextState : CausalConstitutiveState
  nextStateExact : nextState = run.next

/-- Canonical role reading; no caller supplies any relational component. -/
def relationalConstitutiveRoleStage
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source) :
    RelationalConstitutiveRoleStage run :=
  { searchState := source
    searchStateExact := rfl
    structuralOpening :=
      generatedStructuralSplit source.operationalState run.selected run.fresh
    reconstructedRelation := run.relation
    reconstructedRelationExact := rfl
    executedInput := run.sourceContinuation
    executedInputExact := rfl
    completedOutput := run.outputContinuation
    completedOutputExact := rfl
    actionExact := run.outputExact
    preservation := run.outputAccepted
    nextState := run.next
    nextStateExact := rfl }

/--
An explicit certificate exposing how every role component is determined by its
executed stage.  It adds no data and requires no external hypothesis.
-/
structure RelationalRoleConstitutionExact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) : Prop where
  generationOriginExact :
    role.searchState.constitutedHistory = source.constitutedHistory
  searchStateExact : role.searchState = source
  openingExact :
    role.structuralOpening =
      generatedStructuralSplit source.operationalState run.selected run.fresh
  relationFromExecution : role.reconstructedRelation = run.relation
  continuationFromExecutedAction :
    role.completedOutput =
      role.reconstructedRelation.mapContinuation role.executedInput
  nextStateFromExecutedOutput : role.nextState = run.next

/-- The canonical role carries its full exact constitution certificate. -/
theorem relationalConstitutiveRoleStage_exact
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source) :
    RelationalRoleConstitutionExact
      (relationalConstitutiveRoleStage run) :=
  { generationOriginExact := rfl
    searchStateExact := rfl
    openingExact := rfl
    relationFromExecution := rfl
    continuationFromExecutedAction := run.outputExact
    nextStateFromExecutedOutput := rfl }

/--
The authoritative role history.  Its tail roles are indexed by exactly the
causal tail following the state produced by the head.
-/
inductive RelationalConstitutiveRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      RelationalConstitutiveRoleHistory
        (CausalConstitutiveExecutionHistory.nil state)
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      (headRole : RelationalConstitutiveRoleStage head)
      (tailRoles : RelationalConstitutiveRoleHistory tail) :
      RelationalConstitutiveRoleHistory
        (CausalConstitutiveExecutionHistory.step head tail)

/-- Build the unique canonical role reading of a causal history. -/
def buildRelationalConstitutiveRoleHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) →
      RelationalConstitutiveRoleHistory run
  | _, _, .nil _ => .nil
  | _, _, .step head tail =>
      .step (relationalConstitutiveRoleStage head)
        (buildRelationalConstitutiveRoleHistory tail)

/-- Recursive exactness certificate for the whole role history. -/
inductive RelationalRoleHistoryConstitutionExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      RelationalConstitutiveRoleHistory run → Prop where
  | nil {state : CausalConstitutiveState} :
      RelationalRoleHistoryConstitutionExact
        (RelationalConstitutiveRoleHistory.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      (headExact : RelationalRoleConstitutionExact headRole)
      (tailExact : RelationalRoleHistoryConstitutionExact tailRoles) :
      RelationalRoleHistoryConstitutionExact
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)

/-- The canonical role history is exact at every stage. -/
theorem buildRelationalConstitutiveRoleHistory_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) →
      RelationalRoleHistoryConstitutionExact
        (buildRelationalConstitutiveRoleHistory run)
  | _, _, .nil _ => .nil
  | _, _, .step head tail =>
      .step (relationalConstitutiveRoleStage_exact head)
        (buildRelationalConstitutiveRoleHistory_exact tail)

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.relationalConstitutiveRoleStage
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalRoleConstitutionExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.relationalConstitutiveRoleStage_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildRelationalConstitutiveRoleHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalRoleHistoryConstitutionExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildRelationalConstitutiveRoleHistory_exact
/- AXIOM_AUDIT_END -/
