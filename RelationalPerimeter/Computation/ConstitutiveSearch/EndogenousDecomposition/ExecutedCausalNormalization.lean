import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction

/-!
# Operational image computed by the executed role reduction

The relation-indexed reduction is executed first. For every constituted source
profile it produces a target profile together with the dependent trace that
produced it. Those traces prove that all produced targets converge. The
obligation regime then retains each actual target value together with its proof
of membership in that executed convergent fibre. Its carrier, frontier and
carry map are therefore not independent data and no width premise is supplied.
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
  private mk ::
  result :
    (sourceProfile : RoleOccurrenceProfile roles) →
      Sigma fun targetProfile : ExecutedOperationalTargetProfile reduction =>
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
    ExecutedOperationalTargetProfile reduction :=
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
    normalization.target sourceProfile =
      retainedExecutedOperationalTargetProfile reduction :=
  executedRoleProfileReduction_target_exact
    (normalization.trace sourceProfile)

/-- The executed traces, not the ambient target carrier, prove convergence. -/
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

/-- Positive occurrence of one target with its source and executed trace. -/
structure ProducedOperationalTargetOccurrence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) where
  source : RoleOccurrenceProfile roles
  target : ExecutedOperationalTargetProfile reduction
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

/-- Complete source-indexed list of produced target occurrences. -/
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

/-- The frontier representative is itself one target produced by execution. -/
def ExecutedCausalNormalization.producedTargetFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    List (ExecutedOperationalTargetProfile reduction) :=
  [normalization.target (defaultRoleOccurrenceProfile roles)]

/--
The operational regime is definitionally the exact convergent fibre of the
executed target map. Every carried value is the target produced for its source;
there is no separately supplied obligation carrier or carry map.
-/
def ExecutedCausalNormalization.operationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  convergedTargetImageRegime
    (roleProfileFiniteCarrier roles)
    normalization.target
    (defaultRoleOccurrenceProfile roles)
    normalization.targets_converge

/-- The public regime is exactly that executed convergent-target regime. -/
theorem ExecutedCausalNormalization.operationalRegime_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime =
      convergedTargetImageRegime
        (roleProfileFiniteCarrier roles)
        normalization.target
        (defaultRoleOccurrenceProfile roles)
        normalization.targets_converge :=
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
  convergedTargetImageRegime_carry_eq_iff_target_eq
    (roleProfileFiniteCarrier roles)
    normalization.target
    (defaultRoleOccurrenceProfile roles)
    normalization.targets_converge left right

/--
Positive relation between two constituted profiles whose executed traces
produce one and the same operational target.  This relation records the two
traces themselves; it is not a label inferred from a constant carry map.
-/
structure OperationallyCoDetermined
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) : Type 2 where
  target : ExecutedOperationalTargetProfile reduction
  leftTrace : ExecutedRoleProfileReduction reduction left target
  rightTrace : ExecutedRoleProfileReduction reduction right target
  leftTargetExact : target = normalization.target left
  rightTargetExact : target = normalization.target right

/-- Equal produced targets positively yield two traces to their common target. -/
def ExecutedCausalNormalization.coDeterminationOfTargetEq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles)
    (sameTarget : normalization.target left = normalization.target right) :
    OperationallyCoDetermined normalization left right :=
  { target := normalization.target left
    leftTrace := normalization.trace left
    rightTrace := sameTarget.symm ▸ normalization.trace right
    leftTargetExact := rfl
    rightTargetExact := sameTarget }

/-- Codetermination recovers equality of the targets actually produced. -/
theorem OperationallyCoDetermined.target_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    {left right : RoleOccurrenceProfile roles}
    (witness : OperationallyCoDetermined normalization left right) :
    normalization.target left = normalization.target right :=
  Eq.trans witness.leftTargetExact.symm witness.rightTargetExact

/-- Obligation equality is exactly inhabited executed codetermination. -/
theorem ExecutedCausalNormalization.carry_eq_iff_coDetermined
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.operationalRegime.carry left =
        normalization.operationalRegime.carry right ↔
      Nonempty (OperationallyCoDetermined normalization left right) := by
  constructor
  · intro sameCarry
    exact ⟨normalization.coDeterminationOfTargetEq left right
      ((normalization.carry_eq_iff_target_eq left right).mp sameCarry)⟩
  · intro witness
    let ⟨produced⟩ := witness
    exact (normalization.carry_eq_iff_target_eq left right).mpr
      produced.target_eq

/--
Exact public realization of the operational regime.  Its private constructor
prevents an independently supplied carrier or carry map from replacing the
executed convergent-target regime while preserving only numerical readouts.
-/
structure ExactExecutedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type 2 where
  private mk ::
  regime : ObligationRegime (roleProfileFiniteCarrier roles)
  regimeExact : regime = normalization.operationalRegime
  producedOccurrence :
    (source : RoleOccurrenceProfile roles) →
      ProducedOperationalTargetOccurrence normalization
  producedSourceExact :
    (source : RoleOccurrenceProfile roles) →
      (producedOccurrence source).source = source

/-- Canonical exact realization of the regime constructed from executed traces. -/
def exactExecutedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExactExecutedOperationalRegime normalization :=
  { regime := normalization.operationalRegime
    regimeExact := rfl
    producedOccurrence := normalization.producedTargetOccurrence
    producedSourceExact := fun _ => rfl }

/-- Executed convergence makes the produced-target frontier a singleton. -/
theorem ExecutedCausalNormalization.producedTargetFrontier_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.producedTargetFrontier =
      [retainedExecutedOperationalTargetProfile reduction] := by
  exact congrArg (fun target => [target])
    (normalization.target_exact (defaultRoleOccurrenceProfile roles))

/-- The regime width is the width of the executed convergent-target frontier. -/
theorem ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime.frontier.length =
      normalization.producedTargetFrontier.length :=
  rfl

/-- Width one is the terminal readout of executed target convergence. -/
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
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationallyCoDetermined
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.coDeterminationOfTargetEq
#print axioms ConstitutiveSearch.EndogenousDecomposition.OperationallyCoDetermined.target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_eq_iff_coDetermined
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExactExecutedOperationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.exactExecutedOperationalRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targets_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.width_exact
/- AXIOM_AUDIT_END -/
