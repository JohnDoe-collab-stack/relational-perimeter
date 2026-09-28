import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationPolicy

/-!
# Prefix-local operational production

This module is intentionally earlier than every complete operational-history
type. Its producer can receive only the stage that has just been executed. No
future tail, completed history, remaining-stage count or post-hoc readout is
available in its type or imports.
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
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) : Type 2 where
  private mk ::
  decomposition : ExecutedStageDecomposition stage
  decompositionExact : decomposition = executedStageDecomposition stage

/-- The exact interface of a producer that has no access to future data. -/
abbrev PrefixLocalOperationalProducer : Type 2 :=
  {source : CausalConstitutiveState} →
    (stage : CausalConstitutiveStageExecution source) →
      ExecutedStageOperationalProduction stage

/-- Produce the operational material of the current stage alone. -/
def prefixLocalOperationalProducer : PrefixLocalOperationalProducer :=
  fun stage =>
    { decomposition := executedStageDecomposition stage
      decompositionExact := rfl }

/-- The canonical production is exactly the local function of its stage. -/
theorem prefixLocalOperationalProducer_decomposition_exact
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    (prefixLocalOperationalProducer stage).decomposition =
      executedStageDecomposition stage :=
  rfl

/--
There is exactly one operational production for a fixed executed stage. This
is the typed prefix-locality statement consumed by the history layer: no tail
can select another head production.
-/
theorem ExecutedStageOperationalProduction.unique
    {source : CausalConstitutiveState}
    {stage : CausalConstitutiveStageExecution source}
    (left right : ExecutedStageOperationalProduction stage) :
    left = right := by
  have sameDecomposition : left.decomposition = right.decomposition :=
    Eq.trans left.decompositionExact right.decompositionExact.symm
  cases left
  cases right
  cases sameDecomposition
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
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction.unique
/- AXIOM_AUDIT_END -/
