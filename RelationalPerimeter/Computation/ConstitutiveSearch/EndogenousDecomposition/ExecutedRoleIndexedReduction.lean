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
  preservesCriterion :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation)
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
    preservesCriterion := (compileRoleStageAtom role).preservesAccepted
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

/--
The operational decomposition available from one executed stage alone.  Its
type mentions the current stage but not any future tail: the role, atom and
reduction license are therefore available at the prefix where that stage has
just produced its output.
-/
structure ExecutedStageDecomposition
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) where
  private mk ::
  role : RelationalConstitutiveRoleStage stage
  roleExact : role = relationalConstitutiveRoleStage stage
  license : ExecutedRoleReductionLicense role (compileRoleStageAtom role)

/-- Canonical local decomposition, constructed from no data beyond the stage. -/
def executedStageDecomposition
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    ExecutedStageDecomposition stage :=
  let role := relationalConstitutiveRoleStage stage
  { role := role
    roleExact := rfl
    license := executedRoleReductionLicense role }

/--
Stagewise decomposition of a causal execution.  The tail is indexed by the
exact state produced by the head, while the head decomposition is already
typed using the head stage alone.
-/
inductive StagewiseExecutedDecompositionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) → Type 2 where
  | nil {state : CausalConstitutiveState} :
      StagewiseExecutedDecompositionHistory
        (CausalConstitutiveExecutionHistory.nil state)
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      (headDecomposition : ExecutedStageDecomposition head)
      (tailDecomposition : StagewiseExecutedDecompositionHistory tail) :
      StagewiseExecutedDecompositionHistory
        (CausalConstitutiveExecutionHistory.step head tail)

/-- Build each local decomposition at the corresponding causal prefix. -/
def buildStagewiseExecutedDecompositionHistory :
    {count : Nat} → {state : CausalConstitutiveState} →
      (run : CausalConstitutiveExecutionHistory count state) →
      StagewiseExecutedDecompositionHistory run
  | _, _, .nil _ => .nil
  | _, _, .step head tail =>
      .step (executedStageDecomposition head)
        (buildStagewiseExecutedDecompositionHistory tail)

/-- The role history is read directly from the stagewise decomposition. -/
def StagewiseExecutedDecompositionHistory.roles :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      StagewiseExecutedDecompositionHistory run →
      RelationalConstitutiveRoleHistory run
  | _, _, _, .nil => .nil
  | _, _, _, .step headDecomposition tailDecomposition =>
      .step headDecomposition.role tailDecomposition.roles

/-- The canonical stagewise roles are definitionally the canonical role readout. -/
theorem buildStagewiseExecutedDecompositionHistory_roles_exact
    {count : Nat} {state : CausalConstitutiveState}
    (run : CausalConstitutiveExecutionHistory count state) :
    (buildStagewiseExecutedDecompositionHistory run).roles =
      buildRelationalConstitutiveRoleHistory run := by
  induction run with
  | nil => rfl
  | step head tail inductionHypothesis =>
      change
        RelationalConstitutiveRoleHistory.step
            (relationalConstitutiveRoleStage head)
            (buildStagewiseExecutedDecompositionHistory tail).roles =
          RelationalConstitutiveRoleHistory.step
            (relationalConstitutiveRoleStage head)
            (buildRelationalConstitutiveRoleHistory tail)
      exact congrArg
        (RelationalConstitutiveRoleHistory.step
          (relationalConstitutiveRoleStage head))
        inductionHypothesis

/-- Every stagewise role is exactly the role constituted by its executed stage. -/
theorem StagewiseExecutedDecompositionHistory.rolesConstitutionExact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (history : StagewiseExecutedDecompositionHistory run) →
      RelationalRoleHistoryConstitutionExact history.roles
  | _, _, _, .nil => .nil
  | _, _, _, .step headDecomposition tailDecomposition =>
      .step
        (by
          rw [headDecomposition.roleExact]
          exact relationalConstitutiveRoleStage_exact _)
        tailDecomposition.rolesConstitutionExact

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

/-- The reduction history is read from the same stagewise decomposition. -/
def StagewiseExecutedDecompositionHistory.reduction :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (history : StagewiseExecutedDecompositionHistory run) →
      ExecutedRoleReductionHistory (compileRoleHistory history.roles)
  | _, _, _, .nil => .nil
  | _, _, _, .step headDecomposition tailDecomposition =>
      .step headDecomposition.license tailDecomposition.reduction

/-- The canonical stagewise reduction agrees with the role-indexed builder. -/
theorem buildStagewiseExecutedDecompositionHistory_reduction_exact
    {count : Nat} {state : CausalConstitutiveState}
    (run : CausalConstitutiveExecutionHistory count state) :
    (buildStagewiseExecutedDecompositionHistory run).reduction =
      buildExecutedRoleReductionHistory
        (buildStagewiseExecutedDecompositionHistory run).roles := by
  induction run with
  | nil => rfl
  | step head tail inductionHypothesis =>
      change
        ExecutedRoleReductionHistory.step
            (executedRoleReductionLicense
              (relationalConstitutiveRoleStage head))
            (buildStagewiseExecutedDecompositionHistory tail).reduction =
          ExecutedRoleReductionHistory.step
            (executedRoleReductionLicense
              (relationalConstitutiveRoleStage head))
            (buildExecutedRoleReductionHistory
              (buildStagewiseExecutedDecompositionHistory tail).roles)
      exact congrArg
        (ExecutedRoleReductionHistory.step
          (executedRoleReductionLicense
            (relationalConstitutiveRoleStage head)))
        inductionHypothesis

/--
One local operational decision.  The transformed constructor consumes the
actual relational action, its exact executed output, its separate preservation
proof, and the proof that the action is non-identity on the executed source.
The retained constructor consumes the positive viability of the retained
occurrence.  Neither constructor identifies the two source occurrences.
-/
inductive ExecutedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    RoleOpeningOccurrence role → Type 2 where
  | transformed
      (outputExact :
        interpretRoleStageAtom atom
            license.transformedOccurrence
            (license.transformedOccurrenceExact ▸ role.executedInput) =
          role.completedOutput)
      (accepted :
        GeneratedStructuralBranchAccept
          (causalOpeningRight source run.selected run.fresh)
          (interpretRoleStageAtom atom
            license.transformedOccurrence
            (license.transformedOccurrenceExact ▸ role.executedInput)))
      (preservesCriterion :
        (continuation : GeneratedStructuralBranchContinuation
          (causalOpeningLeft source run.selected run.fresh)) →
        GeneratedStructuralBranchAccept
            (causalOpeningLeft source run.selected run.fresh) continuation →
          GeneratedStructuralBranchAccept
            (causalOpeningRight source run.selected run.fresh)
            (atom.action continuation))
      (changesSource :
        (atom.action role.executedInput).1 ≠ role.executedInput.1)
      (sourceTargetDistinct :
        license.transformedOccurrence ≠ license.retainedOccurrence) :
      ExecutedRoleOccurrenceDecision license
        license.transformedOccurrence
  | retained
      (accepted :
        GeneratedStructuralBranchAccept
          (causalOpeningRight source run.selected run.fresh)
          role.completedOutput) :
      ExecutedRoleOccurrenceDecision license license.retainedOccurrence

/-- Decide the operational case by inspecting the constituted occurrence. -/
def executedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom)
    (occurrence : RoleOpeningOccurrence role) :
    ExecutedRoleOccurrenceDecision license occurrence := by
  cases occurrence with
  | mk position occurrenceState formedAt =>
      let occurrence : RoleOpeningOccurrence role :=
        { position := position
          state := occurrenceState
          formedAt := formedAt }
      cases position with
      | left =>
          have occurrenceExact :
              license.transformedOccurrence = occurrence :=
            Eq.trans license.transformedOccurrenceExact
              (openingOccurrence_roundTrip occurrence)
          change ExecutedRoleOccurrenceDecision license occurrence
          rw [← occurrenceExact]
          exact ExecutedRoleOccurrenceDecision.transformed
            license.transformedOutputExact
            license.transformedAccepted
            license.preservesCriterion
            license.actionChangesSource
            license.occurrencesRemainDistinct
      | right =>
          have occurrenceExact : license.retainedOccurrence = occurrence :=
            Eq.trans license.retainedOccurrenceExact
              (openingOccurrence_roundTrip occurrence)
          change ExecutedRoleOccurrenceDecision license occurrence
          rw [← occurrenceExact]
          exact ExecutedRoleOccurrenceDecision.retained license.retainedAccepted

/-- The transformed operational decision retains the separate preservation map. -/
theorem executedTransformedDecisionPreservesCriterion
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation) :=
  license.preservesCriterion

/-- The profile retained by every license of one reduction history. -/
def retainedRoleProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      ExecutedRoleReductionHistory program → RoleOccurrenceProfile roles
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, .step license tailReduction =>
      (license.retainedOccurrence, retainedRoleProfile tailReduction)

/--
Proof-relevant global reduction from one constituted source profile to one
target profile.  Its head decision consumes the corresponding local license and
its tail follows the exact dependent reduction history.
-/
inductive ExecutedRoleProfileReduction :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      RoleOccurrenceProfile roles → RoleOccurrenceProfile roles → Type 2 where
  | nil {state : CausalConstitutiveState} :
      ExecutedRoleProfileReduction
        (ExecutedRoleReductionHistory.nil (state := state)) () ()
  | step {count : Nat} {state : CausalConstitutiveState}
      {head : CausalConstitutiveStageExecution state}
      {tail : CausalConstitutiveExecutionHistory count head.next}
      {headRole : RelationalConstitutiveRoleStage head}
      {tailRoles : RelationalConstitutiveRoleHistory tail}
      {atom : RoleStageAtom headRole}
      {tailProgram : RoleIndexedProgram tailRoles}
      {license : ExecutedRoleReductionLicense headRole atom}
      {tailReduction : ExecutedRoleReductionHistory tailProgram}
      {headSource : RoleOpeningOccurrence headRole}
      {tailSource tailTarget : RoleOccurrenceProfile tailRoles}
      (headDecision : ExecutedRoleOccurrenceDecision license headSource)
      (tailTrace :
        ExecutedRoleProfileReduction tailReduction tailSource tailTarget) :
      ExecutedRoleProfileReduction
        (ExecutedRoleReductionHistory.step license tailReduction)
        (headSource, tailSource)
        (license.retainedOccurrence, tailTarget)

/-- Every constituted profile is reduced by the executed history itself. -/
def normalizeExecutedRoleProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      (profile : RoleOccurrenceProfile roles) →
      Sigma fun target =>
        ExecutedRoleProfileReduction reduction profile target
  | _, state, _, _, _, .nil, profile => by
      cases profile
      exact
        ⟨(), ExecutedRoleProfileReduction.nil (state := state)⟩
  | _, _, _, _, _, .step license tailReduction, profile =>
      let tailNormalization :=
        normalizeExecutedRoleProfile tailReduction profile.2
      ⟨(license.retainedOccurrence, tailNormalization.1),
        .step
          (executedRoleOccurrenceDecision license profile.1)
          tailNormalization.2⟩

/-- Every trace target is exactly the retained profile read from its licenses. -/
theorem executedRoleProfileReduction_target_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      {sourceProfile targetProfile : RoleOccurrenceProfile roles} →
      (trace :
        ExecutedRoleProfileReduction reduction sourceProfile targetProfile) →
      targetProfile = retainedRoleProfile reduction := by
  intro count state run roles program reduction sourceProfile targetProfile trace
  induction trace with
  | nil => rfl
  | step headDecision tailTrace tailExact =>
      exact congrArg (fun tail => (_, tail)) tailExact

/-- The normalizer target is computed from exactly the executed licenses. -/
theorem normalizeExecutedRoleProfile_target_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (profile : RoleOccurrenceProfile roles) :
    (normalizeExecutedRoleProfile reduction profile).1 =
      retainedRoleProfile reduction :=
  executedRoleProfileReduction_target_exact
    (normalizeExecutedRoleProfile reduction profile).2

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.roles
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory_roles_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.rolesConstitutionExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.reduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory_reduction_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedTransformedDecisionPreservesCriterion
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedRoleProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleProfileReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeExecutedRoleProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleProfileReduction_target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeExecutedRoleProfile_target_exact
/- AXIOM_AUDIT_END -/
