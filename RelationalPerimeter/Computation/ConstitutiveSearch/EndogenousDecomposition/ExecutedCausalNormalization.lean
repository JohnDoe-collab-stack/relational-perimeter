import RelationalPerimeter.Computation.ConstitutiveSearch.ExactOperationalImage
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleIndexedReduction

/-!
# Exact target image of the executed role-indexed reduction

The target of this normalizer is the dependent profile of full operational
outputs actually returned by the interpreted role atoms. It is not a
homogeneous assignment readout or a structural occurrence chosen in advance.
Every source profile carries a proof-relevant executed trace to that target.
Only after trace convergence has been proved is the exact image realized as a
finite obligation regime; assignments are exposed strictly downstream as a
representation readout.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open SAT
open Extensive

/-- A produced operational target accompanied by its executed reduction trace. -/
structure ExecutedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) where
  result :
    (sourceProfile : RoleOccurrenceProfile roles) →
      Sigma fun targetOutput : RoleOperationalOutputProfile roles =>
        ExecutedRoleProfileOutputReduction
          reduction sourceProfile targetOutput

/-- Canonical normalization computed by the executed reduction history. -/
def executedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    ExecutedCausalNormalization reduction :=
  { result := normalizeExecutedRoleProfileOutput reduction }

/-- Full dependent operational target produced for one constituted profile. -/
def ExecutedCausalNormalization.target
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    RoleOperationalOutputProfile roles :=
  (normalization.result sourceProfile).1

/-- Proof-relevant trace producing that operational target. -/
def ExecutedCausalNormalization.trace
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedRoleProfileOutputReduction
      reduction sourceProfile (normalization.target sourceProfile) :=
  (normalization.result sourceProfile).2

/-- Every produced target is fixed by the outputs of its executed trace. -/
theorem ExecutedCausalNormalization.target_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.target sourceProfile =
      completedRoleOperationalOutputProfile roles :=
  executedRoleProfileOutputReduction_target_exact
    (normalization.trace sourceProfile)

/-- Homogeneous representation readout of one typed operational target. -/
def ExecutedCausalNormalization.targetAssignments
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) : List Assignment :=
  roleOperationalOutputAssignments (normalization.target sourceProfile)

/--
The representation readout of the produced operational target is exactly the
result of interpreting the compiled role program on the same constituted
profile and its canonical typed payload.
-/
theorem ExecutedCausalNormalization.targetAssignments_eq_interpreted_profile
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.targetAssignments sourceProfile =
      interpretRoleOccurrenceProfile
        (compileRoleHistory roles) sourceProfile
        (canonicalRoleProfilePayload roles sourceProfile) :=
  Eq.trans
    (congrArg roleOperationalOutputAssignments
      (normalization.target_exact sourceProfile))
    (Eq.trans
      (completedRoleOperationalOutputProfile_assignments roles)
      (interpretCompiledRoleHistory_exact roles sourceProfile).symm)

/--
One positive occurrence of a produced operational target. Source, target and
the executed trace connecting them remain available before representation of
the finite image forgets that provenance.
-/
structure ProducedOperationalTargetOccurrence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) where
  source : RoleOccurrenceProfile roles
  target : RoleOperationalOutputProfile roles
  trace : ExecutedRoleProfileOutputReduction reduction source target
  targetExact : target = normalization.target source

/-- Retain the source, computed target and exact trace for one source profile. -/
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

/--
Complete positive enumeration of produced targets with source and trace
provenance still attached.
-/
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

/-- Raw operational readout before any finite image realization. -/
def ExecutedCausalNormalization.rawTargetReadout
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    List (RoleOperationalOutputProfile roles) :=
  normalization.rawProducedTargetOccurrences.map
    ProducedOperationalTargetOccurrence.target

/-- Forgetting provenance yields exactly the direct target readout. -/
theorem ExecutedCausalNormalization.rawTargetReadout_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.rawTargetReadout =
      (roleProfileFiniteCarrier roles).frontier.map normalization.target := by
  unfold ExecutedCausalNormalization.rawTargetReadout
  unfold ExecutedCausalNormalization.rawProducedTargetOccurrences
  unfold roleProfileFiniteCarrier
  change
    List.map ProducedOperationalTargetOccurrence.target
        (List.map normalization.producedTargetOccurrence
          (roleProfileFrontier roles)) =
      List.map normalization.target (roleProfileFrontier roles)
  induction roleProfileFrontier roles with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      exact congrArg
        (List.cons (normalization.target head))
        inductionHypothesis

/-- Executed traces force all produced operational targets to coincide. -/
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

/-- Positive convergence witness extracted from the executed traces. -/
theorem ExecutedCausalNormalization.targetImageConvergence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ConvergentExactTargetImage
      (roleProfileFiniteCarrier roles)
      normalization.target
      (defaultRoleOccurrenceProfile roles) :=
  { targetConverges := fun identity =>
      normalization.targets_converge identity
        (defaultRoleOccurrenceProfile roles) }

/-- Exact finite realization of the image of the executed target computation. -/
def ExecutedCausalNormalization.targetRealization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExactTargetImageRealization
      (roleProfileFiniteCarrier roles) normalization.target :=
  convergentExactTargetImageRealization
    (roleProfileFiniteCarrier roles)
    normalization.target
    (defaultRoleOccurrenceProfile roles)
    normalization.targetImageConvergence

/-- The generic regime is only the downstream projection of that exact image. -/
def ExecutedCausalNormalization.toObligationRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  normalization.targetRealization.toObligationRegime

/-- Equality of carried obligations is exactly equality of executed targets. -/
theorem ExecutedCausalNormalization.carry_eq_iff_target_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (left right : RoleOccurrenceProfile roles) :
    normalization.toObligationRegime.carry left =
        normalization.toObligationRegime.carry right ↔
      normalization.target left = normalization.target right :=
  normalization.targetRealization.carry_eq_iff_target_eq left right

/-- The finite frontier realizing the exact produced-target image. -/
def ExecutedCausalNormalization.producedTargetFrontier
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    List normalization.targetRealization.Obligation :=
  normalization.targetRealization.frontier

/-- Each realized obligation evaluates to exactly its source's produced target. -/
theorem ExecutedCausalNormalization.realizedTarget_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.targetRealization.value
        (normalization.targetRealization.carry sourceProfile) =
      normalization.target sourceProfile :=
  normalization.targetRealization.carry_exact sourceProfile

/-- The one-element shape is downstream of trace convergence and realization. -/
theorem ExecutedCausalNormalization.producedTargetFrontier_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.producedTargetFrontier = [()] := by
  unfold ExecutedCausalNormalization.producedTargetFrontier
  unfold ExecutedCausalNormalization.targetRealization
  unfold convergentExactTargetImageRealization
  rfl

/-- Numeric width one is downstream of the exact target realization. -/
theorem ExecutedCausalNormalization.producedTargetWidth_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.producedTargetFrontier.length = 1 :=
  congrArg List.length normalization.producedTargetFrontier_exact

/--
For this exact realization, width one is equivalent to convergence of all
trace-produced targets; no additional quotienting can explain the width.
-/
theorem ExecutedCausalNormalization.producedTargetWidth_one_iff_targets_converge
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.producedTargetFrontier.length = 1 ↔
      ∀ left right : RoleOccurrenceProfile roles,
        normalization.target left = normalization.target right :=
  normalization.targetRealization.width_one_iff_all_targets_equal
    (roleProfileFiniteCarrier roles)
    normalization.target
    (defaultRoleOccurrenceProfile roles)

/-- The projected regime frontier is literally the exact-image frontier. -/
theorem ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.toObligationRegime.frontier.length =
      normalization.producedTargetFrontier.length :=
  rfl

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.executedCausalNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targetAssignments
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targetAssignments_eq_interpreted_profile
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedOperationalTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.rawProducedTargetOccurrences
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.rawTargetReadout
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.rawTargetReadout_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targets_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targetImageConvergence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.targetRealization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.toObligationRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.carry_eq_iff_target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.realizedTarget_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetWidth_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetWidth_one_iff_targets_converge
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.regimeWidth_eq_producedTargetWidth
/- AXIOM_AUDIT_END -/
