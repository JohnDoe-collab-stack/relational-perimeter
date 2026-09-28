import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization

/-!
# Causally admitted operational regime

This layer keeps construction, exact image realization, criterion admission,
and the final obligation regime distinct. Criterion admission follows the
same executed reduction licenses that generate every output trace. The generic
`ObligationRegime` is exposed only as the final projection.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT

/-- Positive criterion material retained at one executed reduction step. -/
structure ExecutedReductionStepCriterionAdmission
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    {headRole : RelationalConstitutiveRoleStage head}
    {tailRoles : RelationalConstitutiveRoleHistory tail}
    {atom : RoleStageAtom headRole}
    {tailProgram : RoleIndexedProgram tailRoles}
    (license : ExecutedRoleReductionLicense headRole atom)
    (TailAdmission : Type 2) where
  preservesCriterion :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft state head.selected head.fresh)) →
      GeneratedStructuralBranchAccept
          (causalOpeningLeft state head.selected head.fresh) continuation →
        GeneratedStructuralBranchAccept
          (causalOpeningRight state head.selected head.fresh)
          (atom.action continuation)
  retainedAccepted :
    GeneratedStructuralBranchAccept
      (causalOpeningRight state head.selected head.fresh)
      headRole.completedOutput
  tailAdmission : TailAdmission

/--
Positive criterion admission for the exact licenses that generate every
source-indexed output trace. At each stage it retains both the preservation
map for arbitrary transformed continuations and the retained output's own
acceptance witness. Since every trace is indexed by this reduction history,
no foreign decision can use this admission.
-/
def ExecutedReductionCriterionAdmission :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) → Type 2
  | _, _, _, _, _, .nil => ULift.{2} Unit
  | _, _, _, _, _, @ExecutedRoleReductionHistory.step
      count state head tail headRole tailRoles atom tailProgram
      license tailReduction =>
      ExecutedReductionStepCriterionAdmission
        (count := count) (state := state) (head := head) (tail := tail)
        (headRole := headRole) (tailRoles := tailRoles)
        (atom := atom) (tailProgram := tailProgram) license
        (ExecutedReductionCriterionAdmission tailReduction)

/-- Construct admission only from the authoritative reduction licenses. -/
def executedReductionCriterionAdmission :
    {count : Nat} → {state : CausalConstitutiveState} →
      {run : CausalConstitutiveExecutionHistory count state} →
      {roles : RelationalConstitutiveRoleHistory run} →
      {program : RoleIndexedProgram roles} →
      (reduction : ExecutedRoleReductionHistory program) →
        ExecutedReductionCriterionAdmission reduction
  | _, _, _, _, _, .nil => ULift.up.{2} ()
  | _, _, _, _, _, .step license tailReduction =>
      { preservesCriterion := license.preservesCriterion
        retainedAccepted := license.retainedAccepted
        tailAdmission := executedReductionCriterionAdmission tailReduction }

/-- Recover the exact arbitrary-continuation preservation at the head stage. -/
theorem ExecutedReductionCriterionAdmission.headPreservesCriterion
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    {headRole : RelationalConstitutiveRoleStage head}
    {tailRoles : RelationalConstitutiveRoleHistory tail}
    {atom : RoleStageAtom headRole}
    {tailProgram : RoleIndexedProgram tailRoles}
    {license : ExecutedRoleReductionLicense headRole atom}
    {tailReduction : ExecutedRoleReductionHistory tailProgram}
    (admission : ExecutedReductionCriterionAdmission
      (ExecutedRoleReductionHistory.step license tailReduction)) :
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft state head.selected head.fresh)) →
      GeneratedStructuralBranchAccept
          (causalOpeningLeft state head.selected head.fresh) continuation →
        GeneratedStructuralBranchAccept
          (causalOpeningRight state head.selected head.fresh)
          (atom.action continuation) :=
  admission.preservesCriterion

/-- Recover the positive viability of the retained output at the head stage. -/
theorem ExecutedReductionCriterionAdmission.headRetainedAccepted
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    {headRole : RelationalConstitutiveRoleStage head}
    {tailRoles : RelationalConstitutiveRoleHistory tail}
    {atom : RoleStageAtom headRole}
    {tailProgram : RoleIndexedProgram tailRoles}
    {license : ExecutedRoleReductionLicense headRole atom}
    {tailReduction : ExecutedRoleReductionHistory tailProgram}
    (admission : ExecutedReductionCriterionAdmission
      (ExecutedRoleReductionHistory.step license tailReduction)) :
    GeneratedStructuralBranchAccept
      (causalOpeningRight state head.selected head.fresh)
      headRole.completedOutput :=
  admission.retainedAccepted

/-- Admission of the dependent tail is retained without reconstruction. -/
def ExecutedReductionCriterionAdmission.tail
    {count : Nat} {state : CausalConstitutiveState}
    {head : CausalConstitutiveStageExecution state}
    {tail : CausalConstitutiveExecutionHistory count head.next}
    {headRole : RelationalConstitutiveRoleStage head}
    {tailRoles : RelationalConstitutiveRoleHistory tail}
    {atom : RoleStageAtom headRole}
    {tailProgram : RoleIndexedProgram tailRoles}
    {license : ExecutedRoleReductionLicense headRole atom}
    {tailReduction : ExecutedRoleReductionHistory tailProgram}
    (admission : ExecutedReductionCriterionAdmission
      (ExecutedRoleReductionHistory.step license tailReduction)) :
    ExecutedReductionCriterionAdmission tailReduction :=
  admission.tailAdmission

/--
The closed public causal package. Its normalizer is pinned pointwise to the
canonical stagewise reduction, and admission is supplied for every exact
source-indexed trace.
-/
structure CausallyAdmittedRoleRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (stagewise : StagewiseExecutedDecompositionHistory run) where
  private mk ::
  normalization : ExecutedCausalNormalization stagewise.reduction
  normalizationTargetExact :
    (sourceProfile : RoleOccurrenceProfile stagewise.roles) →
      normalization.target sourceProfile =
        (normalizeExecutedRoleProfileOutput
          stagewise.reduction sourceProfile).1
  criterionAdmission :
    ExecutedReductionCriterionAdmission stagewise.reduction

/-- Canonical admitted package built from the same stagewise execution. -/
def causallyAdmittedRoleRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    (stagewise : StagewiseExecutedDecompositionHistory run) :
    CausallyAdmittedRoleRegime stagewise :=
  let normalization := executedCausalNormalization stagewise.reduction
  { normalization := normalization
    normalizationTargetExact := fun _ => rfl
    criterionAdmission :=
      executedReductionCriterionAdmission stagewise.reduction }

/-- The generic obligation regime is only a downstream projection. -/
def CausallyAdmittedRoleRegime.toObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise) :
    Extensive.ObligationRegime
      (roleProfileFiniteCarrier stagewise.roles) :=
  admitted.normalization.toObligationRegime

/-- The produced operational target is the output of the executed trace. -/
theorem CausallyAdmittedRoleRegime.target_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise)
    (sourceProfile : RoleOccurrenceProfile stagewise.roles) :
    admitted.normalization.target sourceProfile =
      completedRoleOperationalOutputProfile stagewise.roles :=
  admitted.normalization.target_exact sourceProfile

/-- The admitted target's representation is the compiled interpreter output. -/
theorem CausallyAdmittedRoleRegime.targetAssignments_eq_interpreted_profile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise)
    (sourceProfile : RoleOccurrenceProfile stagewise.roles) :
    admitted.normalization.targetAssignments sourceProfile =
      interpretRoleOccurrenceProfile
        (compileRoleHistory stagewise.roles) sourceProfile
        (canonicalRoleProfilePayload stagewise.roles sourceProfile) :=
  admitted.normalization.targetAssignments_eq_interpreted_profile sourceProfile

/-- The exact realized target-image frontier is derived after convergence. -/
theorem CausallyAdmittedRoleRegime.producedTargetFrontier_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise) :
    admitted.normalization.producedTargetFrontier = [()] :=
  admitted.normalization.producedTargetFrontier_exact

/-- The image width is derived from the executed normalization. -/
theorem CausallyAdmittedRoleRegime.producedTargetWidth_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise) :
    admitted.normalization.producedTargetFrontier.length = 1 :=
  admitted.normalization.producedTargetWidth_exact

/-- Width one exactly characterizes convergence of the admitted produced targets. -/
theorem CausallyAdmittedRoleRegime.producedTargetWidth_one_iff_targets_converge
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise) :
    admitted.normalization.producedTargetFrontier.length = 1 ↔
      ∀ left right : RoleOccurrenceProfile stagewise.roles,
        admitted.normalization.target left =
          admitted.normalization.target right :=
  admitted.normalization.producedTargetWidth_one_iff_targets_converge

/-- The projected regime has the same width as the exact produced image. -/
theorem CausallyAdmittedRoleRegime.regimeWidth_eq_producedTargetWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise) :
    admitted.toObligationRegime.frontier.length =
      admitted.normalization.producedTargetFrontier.length :=
  admitted.normalization.regimeWidth_eq_producedTargetWidth

/-- Hence the causally admitted operational regime has width one. -/
theorem CausallyAdmittedRoleRegime.width_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise) :
    admitted.toObligationRegime.frontier.length = 1 :=
  Eq.trans admitted.regimeWidth_eq_producedTargetWidth
    admitted.producedTargetWidth_exact

/-- Equality of obligations is exactly equality of executed target outputs. -/
theorem CausallyAdmittedRoleRegime.carry_eq_iff_target_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {stagewise : StagewiseExecutedDecompositionHistory run}
    (admitted : CausallyAdmittedRoleRegime stagewise)
    (left right : RoleOccurrenceProfile stagewise.roles) :
    admitted.toObligationRegime.carry left =
        admitted.toObligationRegime.carry right ↔
      admitted.normalization.target left =
        admitted.normalization.target right :=
  admitted.normalization.carry_eq_iff_target_eq left right

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCriterionAdmission
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionStepCriterionAdmission
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedReductionCriterionAdmission
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCriterionAdmission.headPreservesCriterion
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCriterionAdmission.headRetainedAccepted
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedReductionCriterionAdmission.tail
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.causallyAdmittedRoleRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.toObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.targetAssignments_eq_interpreted_profile
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.producedTargetFrontier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.producedTargetWidth_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.producedTargetWidth_one_iff_targets_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.regimeWidth_eq_producedTargetWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.width_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.carry_eq_iff_target_eq
/- AXIOM_AUDIT_END -/
