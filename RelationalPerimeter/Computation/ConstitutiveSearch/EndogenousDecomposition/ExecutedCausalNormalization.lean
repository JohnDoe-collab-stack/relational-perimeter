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
  constitutiveChain : ExecutedReductionConstitutiveChain reduction
  constitutiveChainExact : ExecutedReductionCausalExact constitutiveChain

/-- Canonical normalization is the execution of the reduction history. -/
def executedCausalNormalization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    (reduction : ExecutedRoleReductionHistory program) :
    ExecutedCausalNormalization reduction :=
  { constitutiveChain := executedReductionConstitutiveChain reduction
    constitutiveChainExact :=
      (executedReductionConstitutiveChain reduction).causalExact }

/-- Preservation is recovered from the exact chain consumed by normalization. -/
def ExecutedCausalNormalization.constitutivePreservation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedReductionPreservationExact normalization.constitutiveChain :=
  normalization.constitutiveChainExact.preservationExact

/-- Primitive relational witnesses are recovered from the consumed chain. -/
def ExecutedCausalNormalization.constitutiveRelationalEvidence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedReductionRelationalConstitutionExact
      normalization.constitutiveChain :=
  normalization.constitutiveChainExact.relationalConstitutionExact

/-- Source separation is recovered from that same consumed exact chain. -/
def ExecutedCausalNormalization.constitutiveOccurrenceSeparation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedReductionOccurrenceSeparationExact normalization.constitutiveChain :=
  normalization.constitutiveChainExact.occurrenceSeparationExact

/--
Positive authorization for operational grouping.  It is not a width premise:
it is the ordered preservation and source-separation material extracted from
the very chain whose decisions produce the normalized targets.
-/
structure ExecutedOperationalGroupingAuthorization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type 2 where
  private mk ::
  causalExact : ExecutedReductionCausalExact normalization.constitutiveChain

/-- Preservation licensed by the exact causal chain of this authorization. -/
def ExecutedOperationalGroupingAuthorization.preservation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ExecutedReductionPreservationExact normalization.constitutiveChain :=
  authorization.causalExact.preservationExact

/-- Relational constitution licensed by the exact causal chain. -/
def ExecutedOperationalGroupingAuthorization.relationalConstitution
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ExecutedReductionRelationalConstitutionExact
      normalization.constitutiveChain :=
  authorization.causalExact.relationalConstitutionExact

/-- Occurrence separation licensed by the same exact causal chain. -/
def ExecutedOperationalGroupingAuthorization.occurrenceSeparation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ExecutedReductionOccurrenceSeparationExact normalization.constitutiveChain :=
  authorization.causalExact.occurrenceSeparationExact

/-- The grouping authorization is read from the stored causal chain. -/
def ExecutedCausalNormalization.groupingAuthorization
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ExecutedOperationalGroupingAuthorization normalization :=
  { causalExact := normalization.constitutiveChainExact }

/--
The result is not a field that a caller or an alternative constructor can
replace. It is computed by eliminating the exact constitutive chain stored in
the normalization.
-/
def ExecutedCausalNormalization.result
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    ExecutedChainNormalization
      normalization.constitutiveChain sourceProfile :=
  normalizeExecutedRoleProfileFromChain
    normalization.constitutiveChain sourceProfile

/-- The result is definitionally the execution of the stored causal chain. -/
theorem ExecutedCausalNormalization.result_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (sourceProfile : RoleOccurrenceProfile roles) :
    normalization.result sourceProfile =
      normalizeExecutedRoleProfileFromChain
        normalization.constitutiveChain sourceProfile :=
  rfl

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
  (normalization.result sourceProfile).target

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
  (normalization.result sourceProfile).trace

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
def ExecutedCausalNormalization.producedTargetOccurrences
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
One produced target admitted by the exact grouping authorization.  The
authorization is an index of the obligation type itself, so an operational
regime cannot be formed first and authorized afterwards.
-/
inductive AuthorizedProducedTargetObligation
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (_authorization : ExecutedOperationalGroupingAuthorization normalization) :
    Type where
  | admitted
      (value : ExecutedOperationalTargetProfile reduction)
      (valueExact : value = normalization.target
        (defaultRoleOccurrenceProfile roles)) :
      AuthorizedProducedTargetObligation normalization _authorization

/-- Recover the executed target value carried by an admitted obligation. -/
def AuthorizedProducedTargetObligation.value
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    {normalization : ExecutedCausalNormalization reduction}
    {authorization : ExecutedOperationalGroupingAuthorization normalization} :
    AuthorizedProducedTargetObligation normalization authorization →
      ExecutedOperationalTargetProfile reduction
  | .admitted value _ => value

/-- Every admitted obligation belongs to the same execution-produced fibre. -/
theorem AuthorizedProducedTargetObligation.all_eq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (authorization : ExecutedOperationalGroupingAuthorization normalization)
    (left right :
      AuthorizedProducedTargetObligation normalization authorization) :
    left = right := by
  cases left with
  | admitted leftValue leftExact =>
      cases right with
      | admitted rightValue rightExact =>
          have same : leftValue = rightValue :=
            Eq.trans leftExact rightExact.symm
          cases same
          rfl

/-- Constructive equality follows from the common executed target. -/
def authorizedProducedTargetObligationDecEq
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    DecidableEq
      (AuthorizedProducedTargetObligation normalization authorization) :=
  fun left right => isTrue
    (AuthorizedProducedTargetObligation.all_eq
      normalization authorization left right)

/--
The operational regime realizes the exact convergent fibre of the executed
target map. This is the realization layer: its target carrier and carry map
are computed from executed traces. Authorization of that realization as an
operational grouping is recorded separately by
`ExactExecutedOperationalRegime`.
-/
def ExecutedCausalNormalization.authorizedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction)
    (authorization : ExecutedOperationalGroupingAuthorization normalization) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  let anchor := defaultRoleOccurrenceProfile roles
  let anchorObligation :
      AuthorizedProducedTargetObligation normalization authorization :=
    .admitted (normalization.target anchor) rfl
  { Obligation :=
      AuthorizedProducedTargetObligation normalization authorization
    decEq := authorizedProducedTargetObligationDecEq normalization authorization
    frontier := [anchorObligation]
    complete := fun obligation => by
      cases obligation with
      | admitted value valueExact =>
          have same :
              AuthorizedProducedTargetObligation.admitted value valueExact =
                anchorObligation := by
            cases valueExact
            rfl
          exact same ▸ .head []
    nodup := .cons (fun _ member _ => nomatch member) .nil
    carry := fun identity =>
      .admitted (normalization.target identity)
        (normalization.targets_converge identity anchor)
    carry_surjective := fun obligation => by
      cases obligation with
      | admitted value valueExact =>
          exact ⟨anchor, by cases valueExact; rfl⟩ }

/-- The public regime is formed only through its exact grouping authorization. -/
def ExecutedCausalNormalization.operationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    ObligationRegime (roleProfileFiniteCarrier roles) :=
  normalization.authorizedOperationalRegime
    normalization.groupingAuthorization

/-- The public regime is exactly that executed convergent-target regime. -/
theorem ExecutedCausalNormalization.operationalRegime_exact
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) :
    normalization.operationalRegime =
      normalization.authorizedOperationalRegime
        normalization.groupingAuthorization :=
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
  by
    constructor
    · intro same
      exact congrArg AuthorizedProducedTargetObligation.value same
    · intro _
      exact AuthorizedProducedTargetObligation.all_eq
        normalization normalization.groupingAuthorization _ _

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
  groupingAuthorization :
    ExecutedOperationalGroupingAuthorization normalization
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
    groupingAuthorization := normalization.groupingAuthorization
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
Authorized exact incorporation of the executed target-image realization. Its
private constructor joins the causal authorization to that exact realization;
neither an independently supplied regime nor authorization detached from the
same causal chain can replace it.
-/
structure ExactExecutedOperationalRegime
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type 2 where
  private mk ::
  groupingAuthorization :
    ExecutedOperationalGroupingAuthorization normalization
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
    groupingAuthorization := normalization.groupingAuthorization
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
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.constitutivePreservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.constitutiveRelationalEvidence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.constitutiveOccurrenceSeparation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.preservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.relationalConstitution
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedOperationalGroupingAuthorization.occurrenceSeparation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.groupingAuthorization
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.result
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.result_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.trace
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.target_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.ProducedOperationalTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetOccurrence
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetOccurrences
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.producedTargetFrontier
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.value
#print axioms ConstitutiveSearch.EndogenousDecomposition.AuthorizedProducedTargetObligation.all_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.authorizedProducedTargetObligationDecEq
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.authorizedOperationalRegime
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
