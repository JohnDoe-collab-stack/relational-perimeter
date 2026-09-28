import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction

/-!
# Operational image computed by the executed role reduction

The relation-indexed reduction is executed first. For every constituted source
profile it produces a target profile together with the dependent trace that
produced it. The obligation regime is then the duplicate-free image of that
very target map. Its carrier, frontier and carry map are therefore not
independent data and no width is prescribed in advance.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open Extensive

/-- Source-indexed results actually produced by one executed reduction. -/
structure ExecutedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) where
  result :
    (sourceProfile : RoleOccurrenceProfile roles) →
      Sigma fun targetProfile : RoleOccurrenceProfile roles =>
        ExecutedRoleProfileReduction reduction sourceProfile targetProfile

/-- Canonical normalization is the execution of the reduction history. -/
def executedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    ExecutedCausalNormalization reduction :=
  { result := normalizeExecutedRoleProfile reduction }

/-- Target profile produced for one constituted source profile. -/
def ExecutedCausalNormalization.target
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    RoleOccurrenceProfile roles :=
  (normalization.result sourceProfile).1

/-- Dependent executed trace producing that target. -/
def ExecutedCausalNormalization.trace
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedRoleProfileReduction
      reduction sourceProfile (normalization.target sourceProfile) :=
  (normalization.result sourceProfile).2

/-- Each target is fixed by the executed decisions in its trace. -/
theorem ExecutedCausalNormalization.target_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.target sourceProfile = retainedRoleProfile reduction :=
  executedRoleProfileReduction_target_exact
    (normalization.trace sourceProfile)

/-- Positive occurrence of one target with its source and executed trace. -/
structure ProducedOperationalTargetOccurrence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) where
  source : RoleOccurrenceProfile roles
  target : RoleOccurrenceProfile roles
  trace : ExecutedRoleProfileReduction reduction source target
  targetExact : target = normalization.target source

/-- Construct the positive target occurrence produced from one source. -/
def ExecutedCausalNormalization.producedTargetOccurrence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ProducedOperationalTargetOccurrence normalization :=
  { source := sourceProfile
    target := normalization.target sourceProfile
    trace := normalization.trace sourceProfile
    targetExact := rfl }

/-- Complete source-indexed list of produced occurrences before deduplication. -/
def ExecutedCausalNormalization.rawProducedTargetOccurrences
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    List (ProducedOperationalTargetOccurrence normalization) :=
  (roleProfileFiniteCarrier roles).frontier.map
    normalization.producedTargetOccurrence

/-- Duplicate-free image computed from the executed target map. -/
def ExecutedCausalNormalization.producedTargetFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    List (RoleOccurrenceProfile roles) :=
  exactTargetImageFrontier
    (roleProfileFiniteCarrier roles)
    (roleOccurrenceProfileDecEq roles)
    normalization.target

/--
The operational regime is definitionally the computed image of the executed
target map. There is no separately supplied obligation carrier or carry map.
-/
def ExecutedCausalNormalization.operationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  computedTargetImageRegime
    (roleProfileFiniteCarrier roles)
    (roleOccurrenceProfileDecEq roles)
    normalization.target

/-- The public regime is exactly, not merely extensionally, that computed image. -/
theorem ExecutedCausalNormalization.operationalRegime_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime =
      computedTargetImageRegime
        (roleProfileFiniteCarrier roles)
        (roleOccurrenceProfileDecEq roles)
        normalization.target :=
  rfl

/-- Obligation equality is exactly equality of targets produced by execution. -/
theorem ExecutedCausalNormalization.carry_eq_iff_target_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.operationalRegime.carry left =
        normalization.operationalRegime.carry right ↔
      normalization.target left = normalization.target right :=
  computedTargetImageRegime_carry_eq_iff_target_eq
    (roleProfileFiniteCarrier roles)
    (roleOccurrenceProfileDecEq roles)
    normalization.target left right

/-- The executed traces prove convergence of the computed targets. -/
theorem ExecutedCausalNormalization.targets_converge
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.target left = normalization.target right :=
  Eq.trans (normalization.target_exact left)
    (normalization.target_exact right).symm

/-- The computed target image, not a prescribed carrier, is a singleton. -/
theorem ExecutedCausalNormalization.producedTargetFrontier_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.producedTargetFrontier = [retainedRoleProfile reduction] := by
  have imageExact := exactTargetImage_eq_singleton_of_all_targets_equal
    (roleProfileFiniteCarrier roles)
    (roleOccurrenceProfileDecEq roles)
    normalization.target
    (defaultRoleOccurrenceProfile roles)
    normalization.targets_converge
  exact Eq.trans imageExact
    (congrArg (fun target => [target])
      (normalization.target_exact (defaultRoleOccurrenceProfile roles)))

/-- The regime width is the width of the image computed from execution. -/
theorem ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length =
      normalization.producedTargetFrontier.length :=
  computedTargetImageRegime_width_eq_image_width
    (roleProfileFiniteCarrier roles)
    (roleOccurrenceProfileDecEq roles)
    normalization.target

/-- Width one is the terminal readout of the computed singleton image. -/
theorem ExecutedCausalNormalization.width_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length = 1 := by
  rw [normalization.regimeWidth_eq_producedTargetWidth]
  rw [normalization.producedTargetFrontier_exact]
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedCausalNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedOperationalTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.rawProducedTargetOccurrences
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.operationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.operationalRegime_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targets_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.width_exact
/- AXIOM_AUDIT_END -/
