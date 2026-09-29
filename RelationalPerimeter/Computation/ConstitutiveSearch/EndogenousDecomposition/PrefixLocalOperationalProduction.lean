import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy

/-!
# Prefix-local operational production

Its producer can receive only the stage that has just been executed. No future
tail, completed history, remaining-stage count or post-hoc readout occurs in
the producer's type.
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
  transformedOccurrence : RoleConstitutedOccurrence role
  transformedOccurrenceExact :
    transformedOccurrence = roleConstitutedOccurrenceAt role .left
  transformedConstitution :
    RoleConstitutionEvidence role transformedOccurrence
  retainedOccurrence : RoleConstitutedOccurrence role
  retainedOccurrenceExact :
    retainedOccurrence = roleConstitutedOccurrenceAt role .right
  retainedConstitution :
    RoleConstitutionEvidence role retainedOccurrence
  transformedOutputExact :
    interpretRoleStageAtom atom
        transformedOccurrence
        transformedConstitution
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
        transformedConstitution
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
  { transformedOccurrence := roleConstitutedOccurrenceAt role .left
    transformedOccurrenceExact := rfl
    transformedConstitution :=
      roleConstitutionEvidence role (roleConstitutedOccurrenceAt role .left)
    retainedOccurrence := roleConstitutedOccurrenceAt role .right
    retainedOccurrenceExact := rfl
    retainedConstitution :=
      roleConstitutionEvidence role (roleConstitutedOccurrenceAt role .right)
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
      (fun same => openingRolePosition_left_ne_right role
        (congrArg
          (fun occurrence : RoleConstitutedOccurrence role =>
            occurrence.position)
          same)) }

/--
The operational decomposition available from one executed stage alone. Its
type mentions the current stage but not any future tail.
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
Operational material produced from one executed stage alone. The private
constructor pins the stored decomposition to the canonical decomposition of
that exact stage.
-/
structure ExecutedStageOperationalProduction
    {Context : Type 2}
    (context : Context)
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) : Type 2 where
  private mk ::
  priorContext : Context
  priorContextExact : priorContext = context
  decomposition : ExecutedStageDecomposition stage
  decompositionExact : decomposition = executedStageDecomposition stage

/-- The exact interface of a producer that has no access to future data. -/
abbrev PrefixLocalOperationalProducer : Type 3 :=
  {Context : Type 2} → (context : Context) →
    {source : CausalConstitutiveState} →
    (stage : CausalConstitutiveStageExecution source) →
      ExecutedStageOperationalProduction context stage

/-- Produce the operational material of the current stage alone. -/
def prefixLocalOperationalProducer : PrefixLocalOperationalProducer :=
  fun {_} context {_} stage =>
    { priorContext := context
      priorContextExact := rfl
      decomposition := executedStageDecomposition stage
      decompositionExact := rfl }

/-- The canonical production is exactly the local function of its stage. -/
theorem prefixLocalOperationalProducer_decomposition_exact
    {Context : Type 2}
    (context : Context)
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    (prefixLocalOperationalProducer context stage).decomposition =
      executedStageDecomposition stage :=
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedRoleReductionLicense
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedStageDecomposition
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.PrefixLocalOperationalProducer
#print axioms ConstitutiveSearch.EndogenousDecomposition.prefixLocalOperationalProducer
#print axioms ConstitutiveSearch.EndogenousDecomposition.prefixLocalOperationalProducer_decomposition_exact
/- AXIOM_AUDIT_END -/
