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

/--
One operational obligation contains the retained role profile derived from the
reduction.  It is not a new source identity and does not identify profiles in
the source carrier.
-/
structure ExecutedOperationalObligation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) where
  private mk ::
  profile : RoleOccurrenceProfile roles
  retainedExact : profile = retainedRoleProfile reduction

/-- Canonical retained obligation read from the complete reduction history. -/
def executedRetainedObligation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    ExecutedOperationalObligation reduction :=
  { profile := retainedRoleProfile reduction
    retainedExact := rfl }

/-- Every operational obligation denotes the same reduction-derived profile. -/
theorem executedOperationalObligation_unique
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (left right : ExecutedOperationalObligation reduction) :
    left = right := by
  cases left
  cases right
  rename_i leftProfile leftExact rightProfile rightExact
  cases leftExact
  cases rightExact
  rfl

def executedOperationalObligationDecEq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    DecidableEq (ExecutedOperationalObligation reduction) :=
  fun left right =>
    isTrue (executedOperationalObligation_unique reduction left right)

/-- The frontier member is derived from the reduction's retained occurrences. -/
def executedOperationalFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    List (ExecutedOperationalObligation reduction) :=
  [executedRetainedObligation reduction]

theorem executedOperationalFrontier_complete
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (obligation : ExecutedOperationalObligation reduction) :
    obligation ∈ executedOperationalFrontier reduction := by
  have same : obligation = executedRetainedObligation reduction :=
    executedOperationalObligation_unique reduction _ _
  exact same ▸ .head _

theorem executedOperationalFrontier_nodup
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    (executedOperationalFrontier reduction).Nodup :=
  .cons (fun _ impossible _ => nomatch impossible) .nil

/-- Package the target computed by one reduction trace as an obligation. -/
def obligationOfExecutedRoleProfileReduction
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {sourceProfile targetProfile : RoleOccurrenceProfile roles}
    (trace :
      ExecutedRoleProfileReduction reduction sourceProfile targetProfile) :
    ExecutedOperationalObligation reduction :=
  { profile := targetProfile
    retainedExact := executedRoleProfileReduction_target_exact trace }

/--
The proof-relevant derivation carried with one source profile and one resulting
obligation.  The obligation is indexed explicitly: a trace cannot be attached
afterwards to an unrelated carry value.
-/
structure ExecutedCarryDerivation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (sourceProfile : RoleOccurrenceProfile roles)
    (obligation : ExecutedOperationalObligation reduction) where
  targetProfile : RoleOccurrenceProfile roles
  trace :
    ExecutedRoleProfileReduction reduction sourceProfile targetProfile
  carriedProfileExact : obligation.profile = targetProfile

/--
Reduce one source profile and return the resulting obligation together with the
source-indexed trace that produces it.  This dependent pair is the primitive
operation; the plain `carry` map below is only its first projection.
-/
def reduceExecutedRoleProfile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (sourceProfile : RoleOccurrenceProfile roles) :
    Sigma fun obligation : ExecutedOperationalObligation reduction =>
      ExecutedCarryDerivation reduction sourceProfile obligation :=
  let normalization :=
    normalizeExecutedRoleProfile reduction sourceProfile
  let obligation :=
    obligationOfExecutedRoleProfileReduction normalization.2
  ⟨obligation,
    { targetProfile := normalization.1
      trace := normalization.2
      carriedProfileExact := rfl }⟩

/--
Carrying a source profile is definitionally the first projection of its
proof-relevant reduction.  There is no separately supplied carry function.
-/
def carryByExecutedReduction
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedOperationalObligation reduction :=
  (reduceExecutedRoleProfile reduction sourceProfile).1

theorem carryByExecutedReduction_profile_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (profile : RoleOccurrenceProfile roles) :
    (carryByExecutedReduction reduction profile).profile =
      (normalizeExecutedRoleProfile reduction profile).1 :=
  (reduceExecutedRoleProfile reduction profile).2.carriedProfileExact

/-- Construct the full carry derivation, rather than only its width readout. -/
def executedCarryDerivation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedCarryDerivation reduction sourceProfile
      (carryByExecutedReduction reduction sourceProfile) :=
  (reduceExecutedRoleProfile reduction sourceProfile).2

/-- Operational regime induced by one explicit, proof-relevant reduction. -/
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
      let sourceProfile := defaultRoleOccurrenceProfile roles
      exact
        ⟨sourceProfile,
          executedOperationalObligation_unique reduction _ obligation⟩ }

/--
The causal package keeps the reduction and the dependent reduction operation in
one private-constructor object.  Its operational `carry` is not a field: it is
definitionally projected from `reduce`, together with the source-indexed trace.
-/
structure ExecutedRoleObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) where
  private mk ::
  reduction :
    ExecutedRoleReductionHistory (compileRoleHistory roles)
  reduce :
    (profile : RoleOccurrenceProfile roles) →
      Sigma fun obligation : ExecutedOperationalObligation reduction =>
        ExecutedCarryDerivation reduction profile obligation
  reduceExact :
    (profile : RoleOccurrenceProfile roles) →
      reduce profile = reduceExecutedRoleProfile reduction profile

/-- The regime is a projection of the package's own reduction witness. -/
def ExecutedRoleObligationRegime.regime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (package : ExecutedRoleObligationRegime roles) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  { Obligation := ExecutedOperationalObligation package.reduction
    decEq := executedOperationalObligationDecEq package.reduction
    frontier := executedOperationalFrontier package.reduction
    complete := executedOperationalFrontier_complete package.reduction
    nodup := executedOperationalFrontier_nodup package.reduction
    carry := fun profile => (package.reduce profile).1
    carry_surjective := fun obligation => by
      let sourceProfile := defaultRoleOccurrenceProfile roles
      exact
        ⟨sourceProfile,
          executedOperationalObligation_unique package.reduction _ obligation⟩ }

/-- `carry` is definitionally the result component of the dependent reduction. -/
theorem ExecutedRoleObligationRegime.carryFromReduction
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (package : ExecutedRoleObligationRegime roles)
    (profile : RoleOccurrenceProfile roles) :
    package.regime.carry profile =
      (package.reduce profile).1 :=
  rfl

/-- The package exposes the source-indexed reduction behind each carry value. -/
def ExecutedRoleObligationRegime.carryDerivation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (package : ExecutedRoleObligationRegime roles)
    (profile : RoleOccurrenceProfile roles) :
    ExecutedCarryDerivation package.reduction profile
      (package.regime.carry profile) :=
  (package.reduce profile).2

theorem ExecutedRoleObligationRegime.frontierFromReduction
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (package : ExecutedRoleObligationRegime roles) :
    package.regime.frontier =
      executedOperationalFrontier package.reduction :=
  rfl

/-- Canonical causal regime built only from the authoritative role history. -/
def executedRoleObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    ExecutedRoleObligationRegime roles :=
  let reduction := buildExecutedRoleReductionHistory roles
  { reduction := reduction
    reduce := reduceExecutedRoleProfile reduction
    reduceExact := fun _ => rfl }

/--
Build the closed causal package directly from the stagewise decomposition of
the execution.  The reduction consumed by the regime is therefore the one
constructed at the same causal prefixes as its roles.
-/
def executedRoleObligationRegimeOfStagewise
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (history : StagewiseExecutedDecompositionHistory run) :
    ExecutedRoleObligationRegime history.roles :=
  let reduction := history.reduction
  { reduction := reduction
    reduce := reduceExecutedRoleProfile reduction
    reduceExact := fun _ => rfl }

/-- Canonical operational regime projected from its causal package. -/
def executedObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (roles : RelationalConstitutiveRoleHistory run) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  (executedRoleObligationRegime roles).regime

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

/--
Positive witness that one nonempty executed regime groups two distinct source
profiles.  The profiles remain inhabitants of the role-constituted carrier;
only their operational obligations coincide.
-/
structure ExecutedRoleProfileGrouping
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory (count + 1) state}
    (roles : RelationalConstitutiveRoleHistory run)
    (package : ExecutedRoleObligationRegime roles) where
  firstProfile : RoleOccurrenceProfile roles
  secondProfile : RoleOccurrenceProfile roles
  profilesDistinct : firstProfile ≠ secondProfile
  obligationsEqual :
    package.regime.carry firstProfile =
      package.regime.carry secondProfile

/-- Construct the grouping witness from an explicit first executed role. -/
def executedRoleObligationRegimeGrouping
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    (headRole : RelationalConstitutiveRoleStage head)
    (tailRoles : RelationalConstitutiveRoleHistory tail) :
    ExecutedRoleProfileGrouping
      (RelationalConstitutiveRoleHistory.step headRole tailRoles)
      (executedRoleObligationRegime
        (RelationalConstitutiveRoleHistory.step headRole tailRoles)) :=
  { firstProfile :=
      (firstRoleSeparatedProfiles headRole tailRoles).1
    secondProfile :=
      (firstRoleSeparatedProfiles headRole tailRoles).2
    profilesDistinct :=
      firstRoleSeparatedProfiles_distinct headRole tailRoles
    obligationsEqual :=
      executedRegime_groups_distinct_firstRoleProfiles headRole tailRoles }

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
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRetainedObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalObligation_unique
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedOperationalFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.obligationOfExecutedRoleProfileReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCarryDerivation
#print axioms ConstitutiveSearch.EndogenousDecomposition.reduceExecutedRoleProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.carryByExecutedReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.carryByExecutedReduction_profile_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedCarryDerivation
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedObligationRegimeOfReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleObligationRegime.regime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleObligationRegime.carryFromReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleObligationRegime.carryDerivation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleObligationRegime.frontierFromReduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleObligationRegimeOfStagewise
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedObligationRegime_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.firstRoleSeparatedProfiles
#print axioms ConstitutiveSearch.EndogenousDecomposition.firstRoleSeparatedProfiles_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRegime_groups_distinct_firstRoleProfiles
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleProfileGrouping
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleObligationRegimeGrouping
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRegime_not_separately_preserving
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedLocalReductionWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedLocalReductionWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedLocalReductionWidth_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedReductionLocalWidths
#print axioms ConstitutiveSearch.EndogenousDecomposition.AllExecutedLocalWidthsExact
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedReductionLocalWidths_exact
/- AXIOM_AUDIT_END -/
