import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy

/-!
# Executed reduction indexed by role, action, and preservation

The reduction certificate cannot be built from a width or a singleton alone.
At every role it is indexed by the authoritative atom and records that the
atom's transformed interpretation reaches the completed output, that the
separate preservation theorem accepts that result, that the retained output is
accepted, and that the two source occurrences remain distinct.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open Extensive

/-- Causal local license for absorbing the transformed occurrence. -/
structure ExecutedRoleReductionLicense
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (atom : RoleStageAtom role) where
  private mk ::
  transformedOccurrence : RoleOpeningOccurrence role
  transformedOccurrenceExact :
    transformedOccurrence = roleOpeningOccurrenceAt role .left
  retainedOccurrence : RoleOpeningOccurrence role
  retainedOccurrenceExact :
    retainedOccurrence = roleOpeningOccurrenceAt role .right
  transformedOutputExact :
    interpretRoleStageAtom atom
        transformedOccurrence
        (transformedOccurrenceExact ▸ role.executedInput) =
      role.completedOutput
  transformedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      (interpretRoleStageAtom atom
        transformedOccurrence
        (transformedOccurrenceExact ▸ role.executedInput))
  retainedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      role.completedOutput
  actionChangesSource :
    (atom.action role.executedInput).1 ≠ role.executedInput.1
  occurrencesRemainDistinct :
    transformedOccurrence ≠ retainedOccurrence

/-- Canonical license; every field is discharged by the executed role. -/
def executedRoleReductionLicense
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ExecutedRoleReductionLicense role (compileRoleStageAtom role) :=
  { transformedOccurrence := roleOpeningOccurrenceAt role .left
    transformedOccurrenceExact := rfl
    retainedOccurrence := roleOpeningOccurrenceAt role .right
    retainedOccurrenceExact := rfl
    transformedOutputExact := by
      exact Eq.trans
        (interpretCompiledRoleStage_left role role.executedInput)
        role.actionExact.symm
    transformedAccepted := by
      exact (compileRoleStageAtom role).preservesAccepted
        role.executedInput
        (role.executedInputExact ▸ run.sourceAccepted)
    retainedAccepted := role.preservation
    actionChangesSource := by
      rw [role.executedInputExact]
      exact compiledRoleStage_action_changes_executed_source run role
    occurrencesRemainDistinct :=
      roleOpeningOccurrence_left_ne_right role }

/-- Dependent reduction history for exactly the atoms of one role program. -/
inductive ExecutedRoleReductionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      (program : RoleIndexedProgram roles) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedRoleReductionHistory
        (RoleIndexedProgram.nil (state := state))
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      (license : ExecutedRoleReductionLicense headRole atom)
      (tailReduction : ExecutedRoleReductionHistory tailProgram) :
      ExecutedRoleReductionHistory
        (RoleIndexedProgram.step atom tailProgram)

/-- Canonical reduction history, structurally tied to the compiled program. -/
def buildExecutedRoleReductionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      ExecutedRoleReductionHistory (compileRoleHistory roles)
  | _, _, _, .nil => .nil
  | _, _, _, .step headRole tailRoles =>
      .step (executedRoleReductionLicense headRole)
        (buildExecutedRoleReductionHistory tailRoles)

/-- One retained operational status, indexed by the causal reduction history. -/
inductive ExecutedOperationalObligation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (_reduction : ExecutedRoleReductionHistory program) : Type where
  | retained

def executedOperationalObligationDecEq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    DecidableEq (ExecutedOperationalObligation reduction)
  | .retained, .retained => isTrue rfl

def executedOperationalFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    List (ExecutedOperationalObligation reduction) :=
  [.retained]

theorem executedOperationalFrontier_complete
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (obligation : ExecutedOperationalObligation reduction) :
    obligation ∈ executedOperationalFrontier reduction := by
  cases obligation
  exact .head _

theorem executedOperationalFrontier_nodup
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    (executedOperationalFrontier reduction).Nodup :=
  .cons (fun _ impossible _ => nomatch impossible) .nil

/--
Carrying a profile is only available relative to the causal reduction witness.
The profile identities remain in the source carrier; only their operational
status is grouped.
-/
def carryByExecutedReduction
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    RoleOccurrenceProfile roles → ExecutedOperationalObligation reduction :=
  fun _ => .retained

/-- Operational regime causally indexed by one explicit reduction history. -/
def executedObligationRegimeOfReduction
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  { Obligation := ExecutedOperationalObligation reduction
    decEq := executedOperationalObligationDecEq reduction
    frontier := executedOperationalFrontier reduction
    complete := executedOperationalFrontier_complete reduction
    nodup := executedOperationalFrontier_nodup reduction
    carry := carryByExecutedReduction reduction
    carry_surjective := fun obligation => by
      cases obligation
      exact ⟨defaultRoleOccurrenceProfile roles, rfl⟩ }

/-- Canonical operational regime from the compiled executed reduction. -/
def executedObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  executedObligationRegimeOfReduction roles
    (buildExecutedRoleReductionHistory roles)

theorem executedObligationRegime_width
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    (executedObligationRegime roles).frontier.length = 1 :=
  rfl

/-- Two distinct profiles differing at the first role. -/
def firstRoleSeparatedProfiles
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    RoleOccurrenceProfile
        (RelationalConstitutiveRoleHistory.step headRole tailRoles) ×
      RoleOccurrenceProfile
        (RelationalConstitutiveRoleHistory.step headRole tailRoles) :=
  let tailDefault := defaultRoleOccurrenceProfile tailRoles
  ((roleOpeningOccurrenceAt headRole .left, tailDefault),
    (roleOpeningOccurrenceAt headRole .right, tailDefault))

theorem firstRoleSeparatedProfiles_distinct
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    (firstRoleSeparatedProfiles headRole tailRoles).1 ≠
      (firstRoleSeparatedProfiles headRole tailRoles).2 := by
  intro same
  exact roleOpeningOccurrence_left_ne_right headRole
    (congrArg Prod.fst same)

theorem executedRegime_groups_distinct_firstRoleProfiles
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    (executedObligationRegime
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)).carry
          (firstRoleSeparatedProfiles headRole tailRoles).1 =
      (executedObligationRegime
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)).carry
          (firstRoleSeparatedProfiles headRole tailRoles).2 :=
  rfl

theorem executedRegime_not_separately_preserving
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    ¬ PreservesIdentitiesSeparately
      (executedObligationRegime
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)) := by
  intro preserves
  exact firstRoleSeparatedProfiles_distinct headRole tailRoles
    (preserves
      (executedRegime_groups_distinct_firstRoleProfiles headRole tailRoles))

/-- Width record computed from the actual local and retained frontiers. -/
structure ExecutedLocalReductionWidth where
  sourceWidth : Nat
  retainedWidth : Nat

def executedLocalReductionWidth
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    ExecutedLocalReductionWidth :=
  { sourceWidth := (openingOccurrenceFrontier role).length
    retainedWidth :=
      (executedOperationalFrontier
        (ExecutedRoleReductionHistory.step
          (executedRoleReductionLicense role)
          ExecutedRoleReductionHistory.nil)).length }

theorem executedLocalReductionWidth_exact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (executedLocalReductionWidth role).sourceWidth = 2 ∧
      (executedLocalReductionWidth role).retainedWidth = 1 :=
  ⟨rfl, rfl⟩

/-- Local width records derived recursively from the actual reduction history. -/
def executedReductionLocalWidths :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      ExecutedRoleReductionHistory program →
      List ExecutedLocalReductionWidth
  | _, _, _, _, _, .nil => []
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ _ _ headRole _ _ _ _ tailReduction =>
        executedLocalReductionWidth headRole ::
          executedReductionLocalWidths tailReduction

/-- Every derived local width record is exactly the causal `2 → 1` reduction. -/
def AllExecutedLocalWidthsExact : List ExecutedLocalReductionWidth → Prop
  | [] => True
  | head :: tail =>
      head.sourceWidth = 2 ∧ head.retainedWidth = 1 ∧
        AllExecutedLocalWidthsExact tail

theorem executedReductionLocalWidths_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      AllExecutedLocalWidthsExact
        (executedReductionLocalWidths reduction)
  | _, _, _, _, _, .nil => True.intro
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      _ _ _ _ headRole _ _ _ _ tailReduction =>
        ⟨(executedLocalReductionWidth_exact headRole).1,
          (executedLocalReductionWidth_exact headRole).2,
          executedReductionLocalWidths_exact tailReduction⟩

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.carryByExecutedReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedObligationRegimeOfReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedObligationRegime_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.firstRoleSeparatedProfiles
#print axioms ConstitutiveSearch.EndogenousDecomposition.firstRoleSeparatedProfiles_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRegime_groups_distinct_firstRoleProfiles
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRegime_not_separately_preserving
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedLocalReductionWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedLocalReductionWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedLocalReductionWidth_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedReductionLocalWidths
#print axioms ConstitutiveSearch.EndogenousDecomposition.AllExecutedLocalWidthsExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedReductionLocalWidths_exact
/- AXIOM_AUDIT_END -/
