import RelationalPerimeter

/-!
# Regression gate for the constitutive extensive separation

The checks protect one dependency direction:

primitive relations -> executed stages -> constituted roles -> source profiles ->
executed reduction -> computed target image -> obligation regime -> width.

No obligation carrier or operational width may be installed independently of the
computed image.
-/

namespace RelationalPerimeter.Tests.RelationalExtensiveIffRegression

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.Extensive
open ConstitutiveSearch.RelationalExtensive
open ConstitutiveSearch.EndogenousDecomposition
open RelationalPerimeter.Computation.EndogenousOperationalDecomposition

set_option maxHeartbeats 800000

/-- The target iff holds for every member of the general binary class. -/
theorem classLevelTarget
    (family : RelationalExtensive.BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        regime :=
  binary_family_exponential_width_iff_distinct_separate_conservation
    family problem regime

/-- Factorized separate capacity is equivalent to the same full-width side. -/
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

theorem independentBinaryMemberIsUnbounded (bound : Nat) :
    bound ≤ abstractBinaryRelationalFamily.stageCount
      (abstractBinaryRelationalFamily.unboundedProblem bound) :=
  abstractBinaryRelationalFamily_unbounded bound

theorem generalClassIsNotOnlyBinary :
    (increasingArityStage 1).occurrenceFrontier.length = 3 :=
  increasingArityRelationalFamily_variable 1

theorem publicBinaryMemberHasExactSourceWidth (input : Nat) :
    (publicBinaryExtensiveFamily.sourceCarrier
        (index := input) ()).frontier.length = 2 ^ (input + 1) :=
  publicBinaryExtensiveFamily.sourceWidth_eq_twoPow ()

/-- The public iff is stated on the carrier constituted by the executed roles. -/
theorem publicTarget
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  constituted_exponential_width_iff_distinct_separate_conservation
    input regime

theorem publicSeparateRegimeHasExponentialWidth (input : Nat) :
    (constitutedDistinctSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  constituted_distinct_separate_regime_has_exponential_width input

theorem publicSeparateRegimeConserves (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (constitutedDistinctSeparateRegime input) :=
  constituted_distinct_separate_regime_conserves input

/-- One stage constructs its decomposition without receiving a future tail. -/
def stageDecompositionIsPrefixLocal
    {source : CausalConstitutiveState}
    (stage : CausalConstitutiveStageExecution source) :
    ExecutedStageDecomposition stage :=
  executedStageDecomposition stage

theorem publicCertificateUsesCanonicalStagewiseDecomposition (input : Nat) :
    (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory
        (constitutiveExtensiveSeparationEvidence input).realization.causalRun :=
  (constitutiveExtensiveSeparationEvidence input).stagewiseDecompositionExact

/-- The public normalizer is the execution of that exact reduction history. -/
theorem publicNormalizationIsCanonical (input : Nat) :
    (constitutiveExtensiveSeparationEvidence input).normalization =
      executedCausalNormalization
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction :=
  (constitutiveExtensiveSeparationEvidence input).normalizationExact

/-- The regime is definitionally pinned to the image of the executed target map. -/
theorem publicOperationalRegimeIsComputedImage (input : Nat) :
    (publicCertificateNormalization input).operationalRegime =
      computedTargetImageRegime
        (roleProfileFiniteCarrier
          (constitutiveExtensiveSeparationEvidence input).roles)
        (roleOccurrenceProfileDecEq
          (constitutiveExtensiveSeparationEvidence input).roles)
        (publicCertificateNormalization input).target :=
  (constitutiveExtensiveSeparationEvidence input).operationalRegimeExact

/-- Each source profile carries the dependent trace producing its target. -/
def publicExecutedTargetHasExactTrace
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    ExecutedRoleProfileReduction
      (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction
      profile
      (executedConstitutiveTarget input profile) :=
  executedConstitutiveTargetTrace input profile

theorem publicExecutedTargetIsExact
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    executedConstitutiveTarget input profile =
      retainedRoleProfile
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction :=
  executed_constitutive_target_exact input profile

/-- The target frontier is computed before its numerical width is read. -/
theorem publicExecutedProducedTargetFrontierIsExact (input : Nat) :
    (publicCertificateNormalization input).producedTargetFrontier =
      [retainedRoleProfile
        (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction] :=
  executed_produced_target_frontier_exact input

theorem publicExecutedWidthComesFromProducedTargetImage (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length =
      (publicCertificateNormalization input).producedTargetFrontier.length :=
  executed_causal_regime_width_eq_produced_target_width input

/-- Regime equality has exactly the fibres produced by execution. -/
theorem publicExecutedCarryFibresAreProducedTargetFibres
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    (executedConstitutiveObligationRegime input).carry left =
        (executedConstitutiveObligationRegime input).carry right ↔
      executedConstitutiveTarget input left =
        executedConstitutiveTarget input right :=
  executed_carry_eq_iff_produced_target_eq input left right

theorem publicExecutedRegimeUsesSameConstitutedCarrier (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length =
        2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
        (executedConstitutiveObligationRegime input) :=
  executed_regime_exponential_width_iff_separate_preservation input

/-- Width one is the terminal readout of the computed singleton image. -/
theorem publicExecutedWidthIsOne (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length = 1 :=
  executed_constitutive_obligation_width_is_one input

/-- The executed grouping changes obligation status without identifying sources. -/
theorem publicExecutedReductionRejectsSeparateObligationStatus
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (executedConstitutiveObligationRegime input) :=
  executed_reduction_does_not_preserve_separate_obligations input

/-- The compiled action materially transforms the executed source. -/
theorem compiledActionIsMaterial
    {source : CausalConstitutiveState}
    (run : CausalConstitutiveStageExecution source)
    (role : RelationalConstitutiveRoleStage run) :
    ((compileRoleStageAtom role).action run.sourceContinuation).1 ≠
      run.sourceContinuation.1 :=
  compiledRoleStage_action_changes_executed_source run role

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

/-- Preservation for arbitrary continuations remains a separate witness. -/
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

theorem reductionKeepsOccurrencesDistinct
    {source : CausalConstitutiveState}
    {run : CausalConstitutiveStageExecution source}
    (role : RelationalConstitutiveRoleStage run) :
    (executedRoleReductionLicense role).transformedOccurrence ≠
      (executedRoleReductionLicense role).retainedOccurrence :=
  (executedRoleReductionLicense role).occurrencesRemainDistinct

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
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.stageDecompositionIsPrefixLocal
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicCertificateUsesCanonicalStagewiseDecomposition
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicNormalizationIsCanonical
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicOperationalRegimeIsComputedImage
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedTargetHasExactTrace
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedTargetIsExact
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedProducedTargetFrontierIsExact
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedWidthComesFromProducedTargetImage
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedCarryFibresAreProducedTargetFibres
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedRegimeUsesSameConstitutedCarrier
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedWidthIsOne
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.publicExecutedReductionRejectsSeparateObligationStatus
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.compiledActionIsMaterial
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.transformedOccurrenceUsesDiscoveredAction
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionCarriesArbitraryContinuationPreservation
#print axioms RelationalPerimeter.Tests.RelationalExtensiveIffRegression.reductionKeepsOccurrencesDistinct
/- AXIOM_AUDIT_END -/
