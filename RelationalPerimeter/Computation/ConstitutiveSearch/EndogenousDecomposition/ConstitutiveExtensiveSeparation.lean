import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PublicRelationalExtensiveFamily
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.CausalOperationalExecution

/-!
# One constitutive chain from primitive roles to operational width

The certificate follows one direction only:

relations and executed stages -> constituted roles -> source profiles ->
executed reduction -> produced targets and traces -> proved convergence ->
obligation regime -> width.

The extensive width is a downstream readout.  No singleton obligation carrier
and no width premise are supplied independently of the executed normalization.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open Extensive

set_option maxHeartbeats 800000

/-- Complete certificate carried by one authoritative public execution. -/
structure ConstitutiveExtensiveSeparationCertificate (input : Nat) where
  private mk ::
  realization : InstrumentedExecutionRealization
    (executeConstitutiveResolution input).constitutiveFeedbackHistory
  realizationExact : realization = publicInstrumentedExecutionRealization input
  causalOperationalExecution :
    CausalOperationalExecutionHistory
      (_count := resolutionLength input)
      (initialThreadedConstitutiveStateFromInitialization
        (initializeConstitutiveHistory input))
  causalOperationalExecutionExact :
    causalOperationalExecution = publicCausalOperationalExecution input
  instrumentedExecutionExact :
    causalOperationalExecution.instrumented =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory
  authoritativeCausalRunExact :
    causalOperationalExecution.causalRun = realization.causalRun
  stagewiseDecomposition :
    StagewiseExecutedDecompositionHistory
      causalOperationalExecution.causalRun
  stagewiseDecompositionExact :
    stagewiseDecomposition =
      causalOperationalExecution.stagewiseDecomposition
  prefixLocalDecompositionExact :
    stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory
        causalOperationalExecution.causalRun
  prefixLocalProductionUnique :
    {source : CausalConstitutiveState} →
      (stage : CausalConstitutiveStageExecution source) →
      (production : ExecutedStageOperationalProduction stage) →
        production = prefixLocalOperationalProducer stage
  rolesExact : stagewiseDecomposition.roles =
    buildRelationalConstitutiveRoleHistory
      causalOperationalExecution.causalRun
  authoritativeRolesExact :
    HEq stagewiseDecomposition.roles
      (publicRelationalConstitutiveRoles input)
  roleConstitutionExact :
    RelationalRoleHistoryConstitutionExact stagewiseDecomposition.roles
  normalization :
    ExecutedCausalNormalization stagewiseDecomposition.reduction
  normalizationExact :
    normalization =
      executedCausalNormalization stagewiseDecomposition.reduction
  normalizationConsumesReductionChain :
    normalization.constitutiveChain =
      executedReductionConstitutiveChain stagewiseDecomposition.reduction
  normalizationChainIsCausallyExact :
    ExecutedReductionCausalExact normalization.constitutiveChain
  normalizationPreservesCriterionAtEveryRole :
    ExecutedReductionPreservationExact normalization.constitutiveChain
  normalizationKeepsOccurrencesDistinctAtEveryRole :
    ExecutedReductionOccurrenceSeparationExact normalization.constitutiveChain
  exactOperationalRegime :
    ExactExecutedOperationalRegime normalization
  exactOperationalRegimeExact :
    exactOperationalRegime = exactExecutedOperationalRegime normalization
  operationalGroupingAuthorizationExact :
    exactOperationalRegime.groupingAuthorization =
      normalization.groupingAuthorization
  operationalRegimeExact :
    normalization.operationalRegime =
      convergedTargetImageRegime
        (roleProfileFiniteCarrier stagewiseDecomposition.roles)
        normalization.target
        (defaultRoleOccurrenceProfile stagewiseDecomposition.roles)
        normalization.targets_converge
  programSizeExact :
    (compileRoleHistory stagewiseDecomposition.roles).atomCount = input + 1
  extensiveWidthExact :
    (roleProfileFiniteCarrier stagewiseDecomposition.roles).frontier.length =
      2 ^ (input + 1)
  separateRegime :
    ObligationRegime (roleProfileFiniteCarrier stagewiseDecomposition.roles)
  separateRegimeExact :
    separateRegime =
      identityObligationRegime
        (roleProfileFiniteCarrier stagewiseDecomposition.roles)
  separateRegimeWidthExact :
    separateRegime.frontier.length = 2 ^ (input + 1)
  separateRegimeConserves :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      separateRegime
  normalizationTargetExact :
    (profile : RoleOccurrenceProfile stagewiseDecomposition.roles) →
      normalization.target profile =
        retainedExecutedOperationalTargetProfile
          stagewiseDecomposition.reduction
  producedTargetFrontierExact :
    normalization.producedTargetFrontier =
      [retainedExecutedOperationalTargetProfile
        stagewiseDecomposition.reduction]
  regimeWidthMatchesProducedTargetWidth :
    normalization.operationalRegime.frontier.length =
      normalization.producedTargetFrontier.length
  retainedOperationalWidthExact :
    normalization.operationalRegime.frontier.length = 1
  carryFibresAreProducedTargetFibres :
    (left right : RoleOccurrenceProfile stagewiseDecomposition.roles) →
      normalization.operationalRegime.carry left =
          normalization.operationalRegime.carry right ↔
        normalization.target left = normalization.target right
  carriedValuesAreProducedTargets :
    (profile : RoleOccurrenceProfile stagewiseDecomposition.roles) →
      (normalization.operationalRegime.carry profile).1 =
        normalization.target profile
  explicitProfilesDistinct :
    stagewiseDecomposition.roles.headTransformedProfile ≠
      stagewiseDecomposition.roles.headRetainedProfile
  explicitProfilesCoDetermined :
    OperationallyCoDetermined normalization
      stagewiseDecomposition.roles.headTransformedProfile
      stagewiseDecomposition.roles.headRetainedProfile
  explicitProfilesCarryTogether :
    normalization.operationalRegime.carry
        stagewiseDecomposition.roles.headTransformedProfile =
      normalization.operationalRegime.carry
        stagewiseDecomposition.roles.headRetainedProfile
  separateConservationIffExponentialWidth :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier stagewiseDecomposition.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime
  carryInjectiveIffExponentialWidth :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier stagewiseDecomposition.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Function.Injective regime.carry
  classTheoremOnAuthoritativeExecutedCarrier :
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Function.Injective regime.carry
  exactRegimeCapacityIff :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier stagewiseDecomposition.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Nonempty
          (ExactRegimeSeparateCapacity regime
            (roleProfileFiniteCarrier
              stagewiseDecomposition.roles).frontier.length)
  executedRegimeDoesNotPreserveSeparately :
    ¬ PreservesIdentitiesSeparately normalization.operationalRegime

/-- The roles remain the history constituted by the execution. -/
def ConstitutiveExtensiveSeparationCertificate.roles
    {input : Nat}
    (certificate : ConstitutiveExtensiveSeparationCertificate input) :
    RelationalConstitutiveRoleHistory
      certificate.causalOperationalExecution.causalRun :=
  certificate.stagewiseDecomposition.roles

/-- Construct the certificate in the same order as its constitutive chain. -/
def constitutiveExtensiveSeparationCertificate
    (input : Nat) : ConstitutiveExtensiveSeparationCertificate input := by
  let realization := publicInstrumentedExecutionRealization input
  let causalOperationalExecution := publicCausalOperationalExecution input
  let stagewise := causalOperationalExecution.stagewiseDecomposition
  let roles := stagewise.roles
  let normalization := executedCausalNormalization stagewise.reduction
  let separateRegime := identityObligationRegime (roleProfileFiniteCarrier roles)
  have extensiveWidth :
      (roleProfileFiniteCarrier roles).frontier.length = 2 ^ (input + 1) :=
    roleProfileFiniteCarrier_width roles
  have executedWidth : normalization.operationalRegime.frontier.length = 1 :=
    normalization.width_exact
  have notPreserving :
      ¬ PreservesIdentitiesSeparately normalization.operationalRegime := by
    intro preserves
    have fullWidth := full_width_of_preserves
      normalization.operationalRegime preserves
    have oneEqualsExponential : 1 = 2 ^ (input + 1) :=
      Eq.trans executedWidth.symm (Eq.trans fullWidth extensiveWidth)
    have strictGrowth : 1 < 2 ^ (input + 1) :=
      Constructive.two_pow_strictly_grows (Nat.zero_lt_succ input)
    exact (Nat.ne_of_lt strictGrowth) oneEqualsExponential
  exact
    { realization := realization
      realizationExact := rfl
      causalOperationalExecution := causalOperationalExecution
      causalOperationalExecutionExact := rfl
      instrumentedExecutionExact :=
        publicCausalOperationalExecution_instrumented_exact input
      authoritativeCausalRunExact :=
        publicCausalOperationalExecution_causalRun_exact input
      stagewiseDecomposition := stagewise
      stagewiseDecompositionExact := rfl
      prefixLocalDecompositionExact :=
        causalOperationalExecution.headsArePrefixLocal
      prefixLocalProductionUnique := fun _ production =>
        ExecutedStageOperationalProduction.unique _ _
      rolesExact :=
        Eq.trans
          (congrArg
            (fun decomposition => decomposition.roles)
            causalOperationalExecution.headsArePrefixLocal)
          (buildStagewiseExecutedDecompositionHistory_roles_exact
            causalOperationalExecution.causalRun)
      authoritativeRolesExact :=
        HEq.trans
          (heq_of_eq
            (Eq.trans
              (congrArg
                (fun decomposition => decomposition.roles)
                causalOperationalExecution.headsArePrefixLocal)
              (buildStagewiseExecutedDecompositionHistory_roles_exact
                causalOperationalExecution.causalRun)))
          (publicCausalOperationalExecution_roles_exact input)
      roleConstitutionExact := stagewise.rolesConstitutionExact
      normalization := normalization
      normalizationExact := rfl
      normalizationConsumesReductionChain := rfl
      normalizationChainIsCausallyExact := normalization.constitutiveChainExact
      normalizationPreservesCriterionAtEveryRole :=
        normalization.constitutivePreservation
      normalizationKeepsOccurrencesDistinctAtEveryRole :=
        normalization.constitutiveOccurrenceSeparation
      exactOperationalRegime := exactExecutedOperationalRegime normalization
      exactOperationalRegimeExact := rfl
      operationalGroupingAuthorizationExact := rfl
      operationalRegimeExact := normalization.operationalRegime_exact
      programSizeExact := compileRoleHistory_atomCount_exact roles
      extensiveWidthExact := extensiveWidth
      separateRegime := separateRegime
      separateRegimeExact := rfl
      separateRegimeWidthExact := extensiveWidth
      separateRegimeConserves :=
        identityObligationRegime_conserves (roleProfileFiniteCarrier roles)
      normalizationTargetExact := normalization.target_exact
      producedTargetFrontierExact := normalization.producedTargetFrontier_exact
      regimeWidthMatchesProducedTargetWidth :=
        normalization.regimeWidth_eq_producedTargetWidth
      retainedOperationalWidthExact := executedWidth
      carryFibresAreProducedTargetFibres :=
        normalization.carry_eq_iff_target_eq
      carriedValuesAreProducedTargets := fun profile =>
        convergedTargetImageRegime_carry_value
          (roleProfileFiniteCarrier roles)
          normalization.target
          (defaultRoleOccurrenceProfile roles)
          normalization.targets_converge
          profile
      explicitProfilesDistinct := stagewise.roles.headProfilesDistinct
        (Nat.zero_lt_succ input)
      explicitProfilesCoDetermined :=
        normalization.coDeterminationOfTargetEq
          stagewise.roles.headTransformedProfile
          stagewise.roles.headRetainedProfile
          (normalization.targets_converge _ _)
      explicitProfilesCarryTogether :=
        (normalization.carry_eq_iff_coDetermined _ _).mpr
          ⟨normalization.coDeterminationOfTargetEq
            stagewise.roles.headTransformedProfile
            stagewise.roles.headRetainedProfile
            (normalization.targets_converge _ _)⟩
      separateConservationIffExponentialWidth :=
        roleConstituted_exponentialWidth_iff_distinctSeparateConservation roles
      carryInjectiveIffExponentialWidth :=
        roleConstituted_exponentialWidth_iff_carry_injective roles
      classTheoremOnAuthoritativeExecutedCarrier :=
        publicBinary_exponentialWidth_iff_carry_injective_on_executedCarrier input
      exactRegimeCapacityIff :=
        roleConstituted_exponentialWidth_iff_exactRegimeCapacity roles
      executedRegimeDoesNotPreserveSeparately := notPreserving }

/-- The canonical normalization produced by the public execution. -/
def publicCertificateNormalization
    (input : Nat) :
    ExecutedCausalNormalization
      (constitutiveExtensiveSeparationCertificate input).stagewiseDecomposition.reduction :=
  (constitutiveExtensiveSeparationCertificate input).normalization

/-- Exact public realization retaining its produced occurrences and traces. -/
def publicCertificateExactExecutedRegime
    (input : Nat) :
    ExactExecutedOperationalRegime (publicCertificateNormalization input) :=
  (constitutiveExtensiveSeparationCertificate input).exactOperationalRegime

/-- Its operational regime is the projection of that exact realization. -/
def publicCertificateExecutedRegime
    (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles) :=
  (publicCertificateNormalization input).operationalRegime

/-- The public facade is pinned to the image computed by the normalization. -/
theorem publicCertificateExecutedRegime_exact
    (input : Nat) :
    publicCertificateExecutedRegime input =
      (publicCertificateNormalization input).operationalRegime :=
  rfl

/-- Every public source exposes the executed trace that produces its target. -/
def publicCertificateCarryTrace
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles) :
    ExecutedRoleProfileReduction
      (constitutiveExtensiveSeparationCertificate input).stagewiseDecomposition.reduction
      profile
      ((publicCertificateNormalization input).target profile) :=
  (publicCertificateNormalization input).trace profile

/-- The computed regime fibres are exactly the executed target fibres. -/
theorem publicCertificate_carry_eq_iff_produced_target_eq
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles) :
    (publicCertificateExecutedRegime input).carry left =
        (publicCertificateExecutedRegime input).carry right ↔
      (publicCertificateNormalization input).target left =
        (publicCertificateNormalization input).target right :=
  publicCertificateExecutedRegime_exact input ▸
    (constitutiveExtensiveSeparationCertificate input).carryFibresAreProducedTargetFibres
      left right

/-- The value carried by the public regime is the target actually produced
for that source, not an independently supplied singleton label. -/
theorem publicCertificate_carry_value_eq_produced_target
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles) :
    ((publicCertificateExecutedRegime input).carry profile).1 =
      (publicCertificateNormalization input).target profile := by
  exact
    (constitutiveExtensiveSeparationCertificate input).carriedValuesAreProducedTargets
      profile

/-- Regime equality is exactly inhabited codetermination by two executed
source-indexed traces. -/
theorem publicCertificate_carry_eq_iff_coDetermined
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles) :
    (publicCertificateExecutedRegime input).carry left =
        (publicCertificateExecutedRegime input).carry right ↔
      Nonempty
        (OperationallyCoDetermined (publicCertificateNormalization input)
          left right) :=
  publicCertificateExecutedRegime_exact input ▸
    (publicCertificateNormalization input).carry_eq_iff_coDetermined left right

/-- First positive source profile, selecting the transformed occurrence. -/
def publicCertificateTransformedProfile
    (input : Nat) :
    RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles :=
  (constitutiveExtensiveSeparationCertificate input).stagewiseDecomposition
    |>.roles.headTransformedProfile

/-- Second positive source profile, selecting the retained occurrence. -/
def publicCertificateRetainedProfile
    (input : Nat) :
    RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles :=
  (constitutiveExtensiveSeparationCertificate input).stagewiseDecomposition
    |>.roles.headRetainedProfile

/-- The two constituted source profiles are explicitly distinct. -/
theorem publicCertificateProfiles_distinct (input : Nat) :
    publicCertificateTransformedProfile input ≠
      publicCertificateRetainedProfile input :=
  (constitutiveExtensiveSeparationCertificate input).explicitProfilesDistinct

/-- Their common operational status is positively witnessed by both traces. -/
def publicCertificateProfiles_coDetermined (input : Nat) :
    OperationallyCoDetermined (publicCertificateNormalization input)
      (publicCertificateTransformedProfile input)
      (publicCertificateRetainedProfile input) :=
  (constitutiveExtensiveSeparationCertificate input).explicitProfilesCoDetermined

/-- The exact executed regime carries both distinct profiles together. -/
theorem publicCertificateProfiles_carryTogether (input : Nat) :
    (publicCertificateExecutedRegime input).carry
        (publicCertificateTransformedProfile input) =
      (publicCertificateExecutedRegime input).carry
        (publicCertificateRetainedProfile input) :=
  publicCertificateExecutedRegime_exact input ▸
    (constitutiveExtensiveSeparationCertificate input).explicitProfilesCarryTogether

/-- Width one is read from executed convergence of the produced targets. -/
theorem publicCertificate_executedRegime_width
    (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
  publicCertificateExecutedRegime_exact input ▸
    (constitutiveExtensiveSeparationCertificate input).retainedOperationalWidthExact

/-- The general target iff is stated on this same constituted source carrier. -/
theorem publicCertificate_exponential_iff_conservation
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  (constitutiveExtensiveSeparationCertificate input).separateConservationIffExponentialWidth
    regime

/-- Literal form of the target on the public role-profile carrier. -/
theorem publicCertificate_exponential_iff_carry_injective
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective regime.carry :=
  (constitutiveExtensiveSeparationCertificate input).carryInjectiveIffExponentialWidth
    regime

/-- Positive full-width regime on the same source identities. -/
def publicCertificateSeparateRegime
    (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles) :=
  (constitutiveExtensiveSeparationCertificate input).separateRegime

theorem publicCertificate_separateRegime_exponentialWidth
    (input : Nat) :
    (publicCertificateSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  (constitutiveExtensiveSeparationCertificate input).separateRegimeWidthExact

theorem publicCertificate_separateRegime_conserves
    (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (publicCertificateSeparateRegime input) :=
  (constitutiveExtensiveSeparationCertificate input).separateRegimeConserves

/-- Distinct source identities are not identified by the computed grouping. -/
theorem publicCertificate_reduction_separates_identity_from_obligation
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately (publicCertificateExecutedRegime input) :=
  (constitutiveExtensiveSeparationCertificate input).executedRegimeDoesNotPreserveSeparately

/--
Closed witness of the immutable scientific target.  Every field is on the one
public role-profile carrier.  The execution and its prefix-local operational
production precede the dependent normalization; the exact regime is then
constructed from the actual target values and their proved convergence, and
width is only a final readout.
-/
structure ExactCausalExponentialTarget (input : Nat) : Type 3 where
  private mk ::
  certificate : ConstitutiveExtensiveSeparationCertificate input
  executionExact :
    certificate.causalOperationalExecution =
      publicCausalOperationalExecution input
  authoritativeRunExact :
    certificate.causalOperationalExecution.causalRun =
      certificate.realization.causalRun
  prefixLocal :
    certificate.stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory
        certificate.causalOperationalExecution.causalRun
  everyHeadProductionIsLocal :
    {source : CausalConstitutiveState} →
      (stage : CausalConstitutiveStageExecution source) →
      (production : ExecutedStageOperationalProduction stage) →
        production = prefixLocalOperationalProducer stage
  rolesConstituted :
    RelationalRoleHistoryConstitutionExact
      certificate.stagewiseDecomposition.roles
  rolesAreAuthoritativePublicRoles :
    HEq certificate.stagewiseDecomposition.roles
      (publicRelationalConstitutiveRoles input)
  normalizationExact :
    certificate.normalization =
      executedCausalNormalization certificate.stagewiseDecomposition.reduction
  normalizationConsumesConstitutiveChain :
    certificate.normalization.constitutiveChain =
      executedReductionConstitutiveChain
        certificate.stagewiseDecomposition.reduction
  constitutiveChainIsCausallyExact :
    ExecutedReductionCausalExact
      certificate.normalization.constitutiveChain
  groupingAuthorizationExact :
    certificate.exactOperationalRegime.groupingAuthorization =
      certificate.normalization.groupingAuthorization
  preservationIsConsumedByGrouping :
    certificate.exactOperationalRegime.groupingAuthorization.preservation =
      certificate.normalization.constitutivePreservation
  occurrenceSeparationIsConsumedByGrouping :
    certificate.exactOperationalRegime.groupingAuthorization.occurrenceSeparation =
      certificate.normalization.constitutiveOccurrenceSeparation
  exactRegimeExact :
    certificate.exactOperationalRegime =
      exactExecutedOperationalRegime certificate.normalization
  carriedValuesAreProducedTargets :
    (profile : RoleOccurrenceProfile
      certificate.stagewiseDecomposition.roles) →
      (certificate.normalization.operationalRegime.carry profile).1 =
        certificate.normalization.target profile
  regimeFibresAreExactlyProducedTargetFibres :
    (left right : RoleOccurrenceProfile
      certificate.stagewiseDecomposition.roles) →
      certificate.exactOperationalRegime.regime.carry left =
          certificate.exactOperationalRegime.regime.carry right ↔
        certificate.normalization.target left =
          certificate.normalization.target right
  regimeFibresAreExactlyExecutedCoDetermination :
    (left right : RoleOccurrenceProfile
      certificate.stagewiseDecomposition.roles) →
      certificate.exactOperationalRegime.regime.carry left =
          certificate.exactOperationalRegime.regime.carry right ↔
        Nonempty
          (OperationallyCoDetermined certificate.normalization left right)
  extensiveWidth :
    (roleProfileFiniteCarrier certificate.roles).frontier.length =
      2 ^ (input + 1)
  executedWidth :
    certificate.exactOperationalRegime.regime.frontier.length = 1
  distinctProfiles :
    certificate.stagewiseDecomposition.roles.headTransformedProfile ≠
      certificate.stagewiseDecomposition.roles.headRetainedProfile
  coDeterminedProfiles :
    OperationallyCoDetermined certificate.normalization
      certificate.stagewiseDecomposition.roles.headTransformedProfile
      certificate.stagewiseDecomposition.roles.headRetainedProfile
  groupedWithoutIdentification :
    certificate.exactOperationalRegime.regime.carry
        certificate.stagewiseDecomposition.roles.headTransformedProfile =
      certificate.exactOperationalRegime.regime.carry
        certificate.stagewiseDecomposition.roles.headRetainedProfile
  exponentialIffIndependentConservation :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier certificate.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime
  exponentialIffCarryInjective :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier certificate.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Function.Injective regime.carry
  classIffIsRealizedOnAuthoritativeExecutedCarrier :
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Function.Injective regime.carry

/-- Construct the complete target from the single authoritative execution. -/
def exactCausalExponentialTarget
    (input : Nat) : ExactCausalExponentialTarget input := by
  let certificate := constitutiveExtensiveSeparationCertificate input
  exact
    { certificate := certificate
      executionExact := certificate.causalOperationalExecutionExact
      authoritativeRunExact := certificate.authoritativeCausalRunExact
      prefixLocal := certificate.prefixLocalDecompositionExact
      everyHeadProductionIsLocal := certificate.prefixLocalProductionUnique
      rolesConstituted := certificate.roleConstitutionExact
      rolesAreAuthoritativePublicRoles := certificate.authoritativeRolesExact
      normalizationExact := certificate.normalizationExact
      normalizationConsumesConstitutiveChain :=
        certificate.normalizationConsumesReductionChain
      constitutiveChainIsCausallyExact :=
        certificate.normalizationChainIsCausallyExact
      groupingAuthorizationExact :=
        certificate.operationalGroupingAuthorizationExact
      preservationIsConsumedByGrouping := rfl
      occurrenceSeparationIsConsumedByGrouping := rfl
      exactRegimeExact := certificate.exactOperationalRegimeExact
      carriedValuesAreProducedTargets := by
        intro profile
        exact certificate.carriedValuesAreProducedTargets profile
      regimeFibresAreExactlyProducedTargetFibres := by
        intro left right
        rw [certificate.exactOperationalRegime.regimeExact]
        exact certificate.carryFibresAreProducedTargetFibres left right
      regimeFibresAreExactlyExecutedCoDetermination := by
        intro left right
        rw [certificate.exactOperationalRegime.regimeExact]
        exact certificate.normalization.carry_eq_iff_coDetermined left right
      extensiveWidth := certificate.extensiveWidthExact
      executedWidth := by
        rw [certificate.exactOperationalRegime.regimeExact]
        exact certificate.retainedOperationalWidthExact
      distinctProfiles := certificate.explicitProfilesDistinct
      coDeterminedProfiles := certificate.explicitProfilesCoDetermined
      groupedWithoutIdentification := by
        rw [certificate.exactOperationalRegime.regimeExact]
        exact certificate.explicitProfilesCarryTogether
      exponentialIffIndependentConservation :=
        certificate.separateConservationIffExponentialWidth
      exponentialIffCarryInjective :=
        certificate.carryInjectiveIffExponentialWidth
      classIffIsRealizedOnAuthoritativeExecutedCarrier :=
        certificate.classTheoremOnAuthoritativeExecutedCarrier }

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate.roles
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateExactExecutedRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateExecutedRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateExecutedRegime_exact
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateCarryTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_carry_eq_iff_produced_target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_carry_value_eq_produced_target
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_carry_eq_iff_coDetermined
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateTransformedProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateRetainedProfile
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateProfiles_distinct
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateProfiles_coDetermined
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateProfiles_carryTogether
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_executedRegime_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_exponential_iff_conservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_exponential_iff_carry_injective
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateSeparateRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_exponentialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_conserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_reduction_separates_identity_from_obligation
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExactCausalExponentialTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.exactCausalExponentialTarget
/- AXIOM_AUDIT_END -/
