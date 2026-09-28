import RelationalPerimeter

/-!
# Regression gate for the relational extensive `iff`

These checks import only the public root. They protect the direction of
constitution: relational histories produce occurrence profiles; programs act
on those profiles; obligation regimes are downstream; and exact exponential
width is equivalent to separate conservation in the general binary class.
-/

namespace RelationalPerimeter.Tests.RelationalExtensiveIffRegression

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.Extensive
open ConstitutiveSearch.RelationalExtensive
open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

set_option maxHeartbeats 800000

/-- The target is stated for an arbitrary member of the general class. -/
theorem classLevelTarget
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        regime :=
  binary_family_exponential_width_iff_distinct_separate_conservation
    family problem regime

/-- Exact address capacity, forced to factor through the regime, is equivalent
to the same exponential condition. -/
theorem classLevelCapacityTarget
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  binary_family_exponential_width_iff_exact_separate_capacity
    family problem regime

/-- The general binary class has an unbounded inhabitant independent of the
public SAT execution. -/
theorem independentBinaryMemberIsUnbounded (bound : Nat) :
    bound ≤ abstractBinaryRelationalFamily.stageCount
      (abstractBinaryRelationalFamily.unboundedProblem bound) :=
  abstractBinaryRelationalFamily_unbounded bound

/-- The wider relational class also contains genuinely variable local arity. -/
theorem generalClassIsNotOnlyBinary :
    (increasingArityStage 1).occurrenceFrontier.length = 3 :=
  increasingArityRelationalFamily_variable 1

/-- The public instance is obtained from the same already executed role
history and is a member of the general binary class. -/
theorem publicBinaryMemberHasExactSourceWidth (input : Nat) :
    (publicBinaryExtensiveFamily.sourceCarrier
        (index := input) ()).frontier.length = 2 ^ (input + 1) :=
  publicBinaryExtensiveFamily.sourceWidth_eq_twoPow ()

/-- The stronger public statement keeps identity, distinction, and
factorized separate addressability together. -/
theorem publicTarget
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  constituted_exponential_width_iff_distinct_separate_conservation
    input regime

/-- The exponential side is positively inhabited on the public chain. -/
theorem publicSeparateRegimeHasExponentialWidth (input : Nat) :
    (constitutedDistinctSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  constituted_distinct_separate_regime_has_exponential_width input

/-- The same explicit regime witnesses the complete conservation side. -/
theorem publicSeparateRegimeConserves (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (constitutedDistinctSeparateRegime input) :=
  constituted_distinct_separate_regime_conserves input

/-- The executed regime enters the same class-level `iff` on the same carrier. -/
theorem publicExecutedRegimeUsesSameConstitutedCarrier (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length =
        2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
        (executedConstitutiveObligationRegime input) :=
  executed_regime_exponential_width_iff_separate_preservation input

/-- One stage already supplies its operational decomposition without receiving
any future execution tail as an argument. -/
def stageDecompositionIsPrefixLocal
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    ExecutedStageDecomposition stage :=
  executedStageDecomposition stage

/-- The closed public certificate uses the canonical stagewise decomposition
of its exact executed history. -/
theorem publicCertificateUsesCanonicalStagewiseDecomposition (input : Nat) :
    (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory
        (constitutiveExtensiveSeparationEvidence input).realization.causalRun :=
  (constitutiveExtensiveSeparationEvidence input).stagewiseDecompositionExact

/-- The public obligation package is built from that stagewise history, not
from a separately installable role relation or carry map. -/
theorem publicExecutedPackageComesFromStagewiseDecomposition (input : Nat) :
    (constitutiveExtensiveSeparationEvidence input).executedRegime =
      executedRoleObligationRegimeOfStagewise
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition :=
  (constitutiveExtensiveSeparationEvidence input).executedRegimeFromStagewise

/-- Each public source profile carries its own dependent reduction witness. -/
def publicExecutedCarryHasSourceIndexedDerivation
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    ExecutedCarryDerivation
      (constitutiveExtensiveSeparationEvidence input).executedRegime.reduction
      profile
      ((executedConstitutiveObligationRegime input).carry profile) :=
  executedProfileCarryDerivation input profile

/-- The public carry target is the target produced by that exact trace. -/
theorem publicExecutedCarryTargetIsTraceTarget
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    (carryByExecutedReduction
        (constitutiveExtensiveSeparationEvidence input).executedRegime.reduction
        profile).profile =
      (publicExecutedCarryHasSourceIndexedDerivation input profile).targetProfile :=
  (publicExecutedCarryHasSourceIndexedDerivation input profile).carriedProfileExact

/-- The program action is not a shape-only identity operation: the compiled
atom changes the actually executed source continuation. -/
theorem compiledActionIsMaterial
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage run) :
    ((compileRoleStageAtom role).action run.sourceContinuation).1 ≠
      run.sourceContinuation.1 :=
  compiledRoleStage_action_changes_executed_source run role

/-- The transformed branch consumes the discovered action. -/
theorem transformedOccurrenceUsesDiscoveredAction
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh)) :
    interpretRoleStageAtom (compileRoleStageAtom role)
        (roleOpeningOccurrenceAt role .left) continuation =
      role.reconstructedRelation.mapContinuation continuation :=
  interpretCompiledRoleStage_left role continuation

/-- The causal reduction stores acceptance of the interpreted transformed
output, separately from the total action. -/
theorem reductionConsumesPreservation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      (interpretRoleStageAtom (compileRoleStageAtom role)
        (executedRoleReductionLicense role).transformedOccurrence
        ((executedRoleReductionLicense role).transformedOccurrenceExact ▸
          role.executedInput)) :=
  (executedRoleReductionLicense role).transformedAccepted

/-- The reduction license retains the preservation map independently of one
already accepted executed input. -/
theorem reductionCarriesArbitraryContinuationPreservation
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run)
    (continuation : GeneratedStructuralBranchContinuation
      (causalOpeningLeft source run.selected run.fresh))
    (accepted : GeneratedStructuralBranchAccept
      (causalOpeningLeft source run.selected run.fresh) continuation) :
    GeneratedStructuralBranchAccept
      (causalOpeningRight source run.selected run.fresh)
      ((compileRoleStageAtom role).action continuation) :=
  executedTransformedDecisionPreservesCriterion
    (executedRoleReductionLicense role) continuation accepted

/-- Reduction does not identify the two viable opening occurrences. -/
theorem reductionKeepsOccurrencesDistinct
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (executedRoleReductionLicense role).transformedOccurrence ≠
      (executedRoleReductionLicense role).retainedOccurrence :=
  (executedRoleReductionLicense role).occurrencesRemainDistinct

/-- Local preservation composes globally, and global preservation recovers
every local condition. -/
theorem localGlobalPolicyEquivalence
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    (policy : RolewiseObligationPolicy roles) :
    AllLocalPoliciesPreserve policy ↔
      PreservesIdentitiesSeparately (rolewiseObligationRegime policy) :=
  allLocalPoliciesPreserve_iff_globalPreservation policy

/-- The executed reduction groups rather than destroys source identities. -/
theorem publicExecutedReductionRejectsSeparateObligationStatus
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (publicCertificateExecutedRegime input) :=
  executed_reduction_does_not_preserve_separate_obligations input

/-- Its local width record is computed recursively from the executed
reduction; no literal global trace is accepted as evidence. -/
theorem publicReductionWidthsAreDerived (input : Nat) :
    AllExecutedLocalWidthsExact
      (executedReductionLocalWidths
        (constitutiveExtensiveSeparationEvidence input).executedRegime.reduction) :=
  (constitutiveExtensiveSeparationEvidence input).localReductionWidthsExact

end RelationalPerimeter.Tests.RelationalExtensiveIffRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.classLevelTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.classLevelCapacityTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.independentBinaryMemberIsUnbounded
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.generalClassIsNotOnlyBinary
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicBinaryMemberHasExactSourceWidth
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicSeparateRegimeHasExponentialWidth
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicSeparateRegimeConserves
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedRegimeUsesSameConstitutedCarrier
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.stageDecompositionIsPrefixLocal
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicCertificateUsesCanonicalStagewiseDecomposition
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedPackageComesFromStagewiseDecomposition
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedCarryHasSourceIndexedDerivation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedCarryTargetIsTraceTarget
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.compiledActionIsMaterial
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.transformedOccurrenceUsesDiscoveredAction
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionConsumesPreservation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionCarriesArbitraryContinuationPreservation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionKeepsOccurrencesDistinct
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.localGlobalPolicyEquivalence
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedReductionRejectsSeparateObligationStatus
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicReductionWidthsAreDerived
/- AXIOM_AUDIT_END -/
