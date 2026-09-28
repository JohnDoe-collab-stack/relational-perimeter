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

/-- A positive profile selecting the transformed occurrence at the first role. -/
def RelationalConstitutiveRoleHistory.headTransformedProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles
  | _, _, _, .nil => ()
  | _, _, _, .step headRole tailRoles =>
      (roleOpeningOccurrenceAt headRole .left,
        defaultRoleOccurrenceProfile tailRoles)

/-- A positive profile selecting the retained occurrence at the first role. -/
def RelationalConstitutiveRoleHistory.headRetainedProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      (roles : RelationalConstitutiveRoleHistory run) →
      RoleOccurrenceProfile roles
  | _, _, _, .nil => ()
  | _, _, _, .step headRole tailRoles =>
      (roleOpeningOccurrenceAt headRole .right,
        defaultRoleOccurrenceProfile tailRoles)

/-- The two profiles remain distinct before any operational grouping. -/
theorem RelationalConstitutiveRoleHistory.headProfilesDistinct
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run)
    (positive : 0 < count) :
    roles.headTransformedProfile ≠ roles.headRetainedProfile := by
  cases roles with
  | nil => exact False.elim (Nat.not_lt_zero 0 positive)
  | step headRole tailRoles =>
      intro same
      exact roleOpeningOccurrence_left_ne_right headRole
        (congrArg Prod.fst same)

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
Positive witness that the transformed occurrence is absorbed into the retained
operational target.  Its constructor is private: the target is licensed only by
the executed action together with its universal preservation map, positive
acceptance, non-identity and occurrence distinction.
-/
structure CriterionPreservingAbsorption
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) : Type where
  private mk ::
  outputExact :
    interpretRoleStageAtom atom
        license.transformedOccurrence
        (license.transformedOccurrenceExact ▸ role.executedInput) =
      role.completedOutput
  accepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      (interpretRoleStageAtom atom
        license.transformedOccurrence
        (license.transformedOccurrenceExact ▸ role.executedInput))
  preservesCriterion :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation)
  changesSource :
    (atom.action role.executedInput).1 ≠ role.executedInput.1
  sourceTargetDistinct :
    license.transformedOccurrence ≠ license.retainedOccurrence

/-- The canonical absorption is constituted from the complete executed license. -/
def criterionPreservingAbsorption
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    CriterionPreservingAbsorption license :=
  { outputExact := license.transformedOutputExact
    accepted := license.transformedAccepted
    preservesCriterion := license.preservesCriterion
    changesSource := license.actionChangesSource
    sourceTargetDistinct := license.occurrencesRemainDistinct }

/--
The operational target carrier at one role is the full continuation space in
the codomain of the executed relation.  It is deliberately not restricted to
the completed output: convergence must be proved from execution rather than
built into the target type.
-/
abbrev ExecutedRoleOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (_license : ExecutedRoleReductionLicense role atom) : Type :=
  GeneratedStructuralBranchContinuation
    (causalOpeningRight source run.selected run.fresh)

/-- The target positively produced by applying the executed relation. -/
def transformedExecutedRoleOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (_absorption : CriterionPreservingAbsorption license) :
    ExecutedRoleOperationalTarget license :=
  interpretRoleStageAtom atom
    license.transformedOccurrence
    (license.transformedOccurrenceExact ▸ role.executedInput)

/-- The transformed target exposes the executed action result definitionally. -/
theorem transformedExecutedRoleOperationalTarget_is_executed_action
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    transformedExecutedRoleOperationalTarget absorption =
      interpretRoleStageAtom atom
        license.transformedOccurrence
        (license.transformedOccurrenceExact ▸ role.executedInput) :=
  rfl

/-- The already completed right-hand continuation as an operational target. -/
def retainedExecutedRoleOperationalTarget
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    ExecutedRoleOperationalTarget license :=
  role.completedOutput

/-- The executed action, rather than the target carrier, proves convergence. -/
theorem transformedExecutedRoleOperationalTarget_eq_retained
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    transformedExecutedRoleOperationalTarget absorption =
      retainedExecutedRoleOperationalTarget license :=
  absorption.outputExact

/--
One local operational decision, indexed by both its constituted source and the
target it actually produces.  The transformed constructor consumes the complete
preserving absorption witness.  The retained constructor consumes positive
viability.  Neither constructor identifies the source occurrences.
-/
inductive ExecutedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom) :
    RoleOpeningOccurrence role → ExecutedRoleOperationalTarget license → Type 2 where
  | transformed
      (absorption : CriterionPreservingAbsorption license) :
      ExecutedRoleOccurrenceDecision license
        license.transformedOccurrence
        (transformedExecutedRoleOperationalTarget absorption)
  | retained
      (accepted :
        GeneratedStructuralBranchAccept
          (causalOpeningRight source run.selected run.fresh)
          role.completedOutput) :
      ExecutedRoleOccurrenceDecision license
        license.retainedOccurrence
        (retainedExecutedRoleOperationalTarget license)

/-- Decide the operational case by inspecting the constituted occurrence. -/
def executedRoleOccurrenceDecision
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    (license : ExecutedRoleReductionLicense role atom)
    (occurrence : RoleOpeningOccurrence role) :
    Sigma fun target : ExecutedRoleOperationalTarget license =>
      ExecutedRoleOccurrenceDecision license occurrence target := by
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
          change Sigma fun target : ExecutedRoleOperationalTarget license =>
            ExecutedRoleOccurrenceDecision license occurrence target
          rw [← occurrenceExact]
          let absorption := criterionPreservingAbsorption license
          exact ⟨transformedExecutedRoleOperationalTarget absorption,
            ExecutedRoleOccurrenceDecision.transformed absorption⟩
      | right =>
          have occurrenceExact : license.retainedOccurrence = occurrence :=
            Eq.trans license.retainedOccurrenceExact
              (openingOccurrence_roundTrip occurrence)
          change Sigma fun target : ExecutedRoleOperationalTarget license =>
            ExecutedRoleOccurrenceDecision license occurrence target
          rw [← occurrenceExact]
          exact ⟨retainedExecutedRoleOperationalTarget license,
            ExecutedRoleOccurrenceDecision.retained license.retainedAccepted⟩

/-- Every local target is obtained by eliminating the produced decision. -/
theorem ExecutedRoleOccurrenceDecision.target_exact
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    {sourceOccurrence : RoleOpeningOccurrence role}
    {target : ExecutedRoleOperationalTarget license}
    (decision : ExecutedRoleOccurrenceDecision
      license sourceOccurrence target) :
    target = retainedExecutedRoleOperationalTarget license := by
  cases decision with
  | transformed absorption =>
      exact transformedExecutedRoleOperationalTarget_eq_retained absorption
  | retained => rfl

/-- The preserving absorption used to form a transformed decision retains the
separate preservation map. -/
theorem criterionPreservingAbsorption_preservesCriterion
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    {role : RelationalConstitutiveRoleStage run}
    {atom : RoleStageAtom role}
    {license : ExecutedRoleReductionLicense role atom}
    (absorption : CriterionPreservingAbsorption license) :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) →
    GeneratedStructuralBranchAccept
        (causalOpeningLeft source run.selected run.fresh) continuation →
      GeneratedStructuralBranchAccept
        (causalOpeningRight source run.selected run.fresh)
        (atom.action continuation) :=
  absorption.preservesCriterion

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
Dependent carrier of outputs produced by the executed reduction.  Unlike the
source occurrence profile, every head component contains the continuation
actually produced in the codomain of that stage relation.
-/
def ExecutedOperationalTargetProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      ExecutedRoleReductionHistory program → Type
  | _, _, _, _, _, .nil => Unit
  | _, _, _, _, _, .step license tailReduction =>
      ExecutedRoleOperationalTarget license ×
        ExecutedOperationalTargetProfile tailReduction

/-- The completed output profile against which produced outputs are compared. -/
def retainedExecutedOperationalTargetProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      ExecutedOperationalTargetProfile reduction
  | _, _, _, _, _, .nil => ()
  | _, _, _, _, _, .step license tailReduction =>
      (retainedExecutedRoleOperationalTarget license,
        retainedExecutedOperationalTargetProfile tailReduction)

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
      RoleOccurrenceProfile roles →
        ExecutedOperationalTargetProfile reduction → Type 2 where
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
      {headTarget : ExecutedRoleOperationalTarget license}
      {tailSource : RoleOccurrenceProfile tailRoles}
      {tailTarget : ExecutedOperationalTargetProfile tailReduction}
      (headDecision :
        ExecutedRoleOccurrenceDecision license headSource headTarget)
      (tailTrace :
        ExecutedRoleProfileReduction tailReduction tailSource tailTarget) :
      ExecutedRoleProfileReduction
        (ExecutedRoleReductionHistory.step license tailReduction)
        (headSource, tailSource)
        (headTarget, tailTarget)

/-- Every constituted profile is reduced by the executed history itself. -/
def normalizeExecutedRoleProfile :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
      (profile : RoleOccurrenceProfile roles) →
      Sigma fun target : ExecutedOperationalTargetProfile reduction =>
        ExecutedRoleProfileReduction reduction profile target
  | _, state, _, _, _, .nil, profile => by
      cases profile
      exact
        ⟨(), ExecutedRoleProfileReduction.nil (state := state)⟩
  | _, _, _, _, _, .step license tailReduction, profile =>
      let headDecision :=
        executedRoleOccurrenceDecision license profile.1
      let tailNormalization :=
        normalizeExecutedRoleProfile tailReduction profile.2
      ⟨(headDecision.1, tailNormalization.1),
        .step
          headDecision.2
          tailNormalization.2⟩

/-- Every trace target equals the completed profile through executed outputs. -/
theorem executedRoleProfileReduction_target_exact :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      {reduction : ExecutedRoleReductionHistory program} →
      {sourceProfile : RoleOccurrenceProfile roles} →
      {targetProfile : ExecutedOperationalTargetProfile reduction} →
      (trace :
        ExecutedRoleProfileReduction reduction sourceProfile targetProfile) →
      targetProfile = retainedExecutedOperationalTargetProfile reduction := by
  intro count state run roles program reduction sourceProfile targetProfile trace
  induction trace with
  | nil => rfl
  | step headDecision tailTrace tailExact =>
      cases headDecision with
      | transformed absorption =>
          exact Prod.ext
            (transformedExecutedRoleOperationalTarget_eq_retained absorption)
            tailExact
      | retained =>
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
      retainedExecutedOperationalTargetProfile reduction :=
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
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory.headTransformedProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory.headRetainedProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.RelationalConstitutiveRoleHistory.headProfilesDistinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildExecutedRoleReductionHistory
#print axioms ConstitutiveSearch.EndogenousDecomposition.StagewiseExecutedDecompositionHistory.reduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.buildStagewiseExecutedDecompositionHistory_reduction_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CriterionPreservingAbsorption
#print axioms ConstitutiveSearch.EndogenousDecomposition.criterionPreservingAbsorption
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.transformedExecutedRoleOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.transformedExecutedRoleOperationalTarget_is_executed_action
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedExecutedRoleOperationalTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.transformedExecutedRoleOperationalTarget_eq_retained
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleOccurrenceDecision
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleOccurrenceDecision.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.criterionPreservingAbsorption_preservesCriterion
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedRoleProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalTargetProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.retainedExecutedOperationalTargetProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleProfileReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeExecutedRoleProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleProfileReduction_target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.normalizeExecutedRoleProfile_target_exact
/- AXIOM_AUDIT_END -/
