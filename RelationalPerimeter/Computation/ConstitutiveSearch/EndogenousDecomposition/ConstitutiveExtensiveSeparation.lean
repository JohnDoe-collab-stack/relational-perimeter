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
      initialOperationalPrefix
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
  rolesExact : stagewiseDecomposition.roles =
    buildRelationalConstitutiveRoleHistory
      causalOperationalExecution.causalRun
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
  normalizationConsumesRelationalConstitution :
    ExecutedReductionRelationalConstitutionExact normalization.constitutiveChain
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
      normalization.authorizedOperationalRegime
        normalization.groupingAuthorization
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
      rolesExact :=
        Eq.trans
          (congrArg
            (fun decomposition => decomposition.roles)
            causalOperationalExecution.headsArePrefixLocal)
          (buildStagewiseExecutedDecompositionHistory_roles_exact
            causalOperationalExecution.causalRun)
      roleConstitutionExact := stagewise.rolesConstitutionExact
      normalization := normalization
      normalizationExact := rfl
      normalizationConsumesReductionChain := rfl
      normalizationChainIsCausallyExact := normalization.constitutiveChainExact
      normalizationConsumesRelationalConstitution :=
        normalization.constitutiveRelationalEvidence
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
        rfl
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

/-- The canonical normalization produced by the public fused execution. -/
def publicCertificateNormalization
    (input : Nat) :
    ExecutedCausalNormalization
      (publicCausalOperationalExecution input).stagewiseDecomposition.reduction :=
  executedCausalNormalization
    (publicCausalOperationalExecution input).stagewiseDecomposition.reduction

/-- Exact public realization retaining its produced occurrences and traces. -/
def publicCertificateExactExecutedRegime
    (input : Nat) :
    ExactExecutedOperationalRegime (publicCertificateNormalization input) :=
  exactExecutedOperationalRegime (publicCertificateNormalization input)

/-- The public regime is formed on the very carrier produced by the fused run. -/
def publicCertificateExecutedRegime
    (input : Nat) :
    ObligationRegime (publicRoleProfileFiniteCarrier input) :=
  (publicCertificateNormalization input).operationalRegime

theorem publicCertificateExecutedRegime_exact
    (input : Nat) :
    publicCertificateExecutedRegime input =
      (publicCertificateNormalization input).operationalRegime :=
  rfl

/-- Every public source exposes the executed trace that produces its target. -/
def publicCertificateCarryTrace
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) :
    ExecutedRoleProfileReduction
      (publicCausalOperationalExecution input).stagewiseDecomposition.reduction
      profile
      ((publicCertificateNormalization input).target profile) :=
  (publicCertificateNormalization input).trace profile

theorem publicCertificate_carry_eq_iff_produced_target_eq
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) :
    (publicCertificateExecutedRegime input).carry left =
        (publicCertificateExecutedRegime input).carry right ↔
      (publicCertificateNormalization input).target left =
        (publicCertificateNormalization input).target right :=
  (publicCertificateNormalization input).carry_eq_iff_target_eq left right

theorem publicCertificate_carry_value_eq_produced_target
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) :
    ((publicCertificateExecutedRegime input).carry profile).1 =
      (publicCertificateNormalization input).target profile :=
  rfl

theorem publicCertificate_carry_eq_iff_coDetermined
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) :
    (publicCertificateExecutedRegime input).carry left =
        (publicCertificateExecutedRegime input).carry right ↔
      Nonempty
        (OperationallyCoDetermined (publicCertificateNormalization input)
          left right) :=
  (publicCertificateNormalization input).carry_eq_iff_coDetermined left right

def publicCertificateTransformedProfile
    (input : Nat) :
    RoleOccurrenceProfile (publicRelationalConstitutiveRoles input) :=
  (publicRelationalConstitutiveRoles input).headTransformedProfile

def publicCertificateRetainedProfile
    (input : Nat) :
    RoleOccurrenceProfile (publicRelationalConstitutiveRoles input) :=
  (publicRelationalConstitutiveRoles input).headRetainedProfile

theorem publicCertificateProfiles_distinct (input : Nat) :
    publicCertificateTransformedProfile input ≠
      publicCertificateRetainedProfile input :=
  (publicRelationalConstitutiveRoles input).headProfilesDistinct
    (Nat.zero_lt_succ input)

def publicCertificateProfiles_coDetermined (input : Nat) :
    OperationallyCoDetermined (publicCertificateNormalization input)
      (publicCertificateTransformedProfile input)
      (publicCertificateRetainedProfile input) :=
  (publicCertificateNormalization input).coDeterminationOfTargetEq _ _
    ((publicCertificateNormalization input).targets_converge _ _)

theorem publicCertificateProfiles_carryTogether (input : Nat) :
    (publicCertificateExecutedRegime input).carry
        (publicCertificateTransformedProfile input) =
      (publicCertificateExecutedRegime input).carry
        (publicCertificateRetainedProfile input) :=
  ((publicCertificateNormalization input).carry_eq_iff_coDetermined _ _).mpr
    ⟨publicCertificateProfiles_coDetermined input⟩

theorem publicCertificate_executedRegime_width
    (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
  (publicCertificateNormalization input).width_exact

theorem publicCertificate_exponential_iff_conservation
    (input : Nat)
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  public_exponentialWidth_iff_distinctSeparateConservation input regime

theorem publicCertificate_exponential_iff_carry_injective
    (input : Nat)
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      Function.Injective regime.carry :=
  publicBinary_exponentialWidth_iff_carry_injective_on_executedCarrier
    input regime

def publicCertificateSeparateRegime
    (input : Nat) :
    ObligationRegime (publicRoleProfileFiniteCarrier input) :=
  identityObligationRegime (publicRoleProfileFiniteCarrier input)

theorem publicCertificate_separateRegime_exponentialWidth
    (input : Nat) :
    (publicCertificateSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  publicRoleProfileFiniteCarrier_width input

theorem publicCertificate_separateRegime_conserves
    (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (publicCertificateSeparateRegime input) :=
  identityObligationRegime_conserves (publicRoleProfileFiniteCarrier input)

theorem publicCertificate_reduction_separates_identity_from_obligation
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately (publicCertificateExecutedRegime input) := by
  intro preserves
  have fullWidth := full_width_of_preserves
    (publicCertificateExecutedRegime input) preserves
  have oneEqualsExponential : 1 = 2 ^ (input + 1) :=
    Eq.trans (publicCertificate_executedRegime_width input).symm
      (Eq.trans fullWidth (publicRoleProfileFiniteCarrier_width input))
  exact (Nat.ne_of_lt
    (Constructive.two_pow_strictly_grows (Nat.zero_lt_succ input)))
      oneEqualsExponential

/-- Two distinct constituted profiles positively grouped by one normalization. -/
structure ExecutedGroupedDistinctProfiles
    {count : Nat} {state : CausalConstitutiveState}
    {run : CausalConstitutiveExecutionHistory count state}
    {roles : RelationalConstitutiveRoleHistory run}
    {program : RoleIndexedProgram roles}
    {reduction : ExecutedRoleReductionHistory program}
    (normalization : ExecutedCausalNormalization reduction) : Type 2 where
  left : RoleOccurrenceProfile roles
  right : RoleOccurrenceProfile roles
  distinct : left ≠ right
  coDetermined : OperationallyCoDetermined normalization left right
  carriedTogether :
    normalization.operationalRegime.carry left =
      normalization.operationalRegime.carry right

/-- Constitution and prefix-local production of the public execution. -/
structure PublicExecutionConstitutionCertificate (input : Nat) : Type 3 where
  private mk ::
  executionErasesExactly :
    (publicCausalOperationalExecution input).instrumented =
      (executeConstitutiveResolution input).constitutiveFeedbackHistory
  prefixLocal :
    (publicCausalOperationalExecution input).stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory
        (publicCausalOperationalExecution input).causalRun
  rolesConstituted :
    RelationalRoleHistoryConstitutionExact
      (publicRelationalConstitutiveRoles input)

/-- The public normalizer eliminates precisely the executed constitutive chain. -/
structure PublicConstitutiveNormalizationCertificate (input : Nat) : Type 3 where
  private mk ::
  normalizationExact :
    publicCertificateNormalization input =
      executedCausalNormalization
        (publicCausalOperationalExecution input).stagewiseDecomposition.reduction
  normalizationConsumesConstitutiveChain :
    (publicCertificateNormalization input).constitutiveChain =
      executedReductionConstitutiveChain
        (publicCausalOperationalExecution input).stagewiseDecomposition.reduction
  constitutiveChainIsCausallyExact :
    ExecutedReductionCausalExact
      (publicCertificateNormalization input).constitutiveChain
  relationalConstitutionIsConsumed :
    ExecutedReductionRelationalConstitutionExact
      (publicCertificateNormalization input).constitutiveChain

/-- Exact incorporation of the normalized target fibres into a regime. -/
structure PublicOperationalRegimeCertificate (input : Nat) : Type 3 where
  private mk ::
  groupingAuthorizationExact :
    (publicCertificateExactExecutedRegime input).groupingAuthorization =
      (publicCertificateNormalization input).groupingAuthorization
  groupingRelationalConstitutionIsChainConstitution :
    (publicCertificateExactExecutedRegime input).groupingAuthorization.relationalConstitution =
      (publicCertificateNormalization input).constitutiveRelationalEvidence
  groupingPreservationIsChainPreservation :
    (publicCertificateExactExecutedRegime input).groupingAuthorization.preservation =
      (publicCertificateNormalization input).constitutivePreservation
  groupingSeparationIsChainSeparation :
    (publicCertificateExactExecutedRegime input).groupingAuthorization.occurrenceSeparation =
      (publicCertificateNormalization input).constitutiveOccurrenceSeparation
  exactRegimeExact :
    publicCertificateExactExecutedRegime input =
      exactExecutedOperationalRegime (publicCertificateNormalization input)
  carriedValuesAreProducedTargets :
    (profile : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) →
      ((publicCertificateExecutedRegime input).carry profile).1 =
        (publicCertificateNormalization input).target profile
  regimeFibresAreExactlyProducedTargetFibres :
    (left right : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) →
      (publicCertificateExecutedRegime input).carry left =
          (publicCertificateExecutedRegime input).carry right ↔
        (publicCertificateNormalization input).target left =
          (publicCertificateNormalization input).target right
  regimeFibresAreExactlyExecutedCoDetermination :
    (left right : RoleOccurrenceProfile
      (publicRelationalConstitutiveRoles input)) →
      (publicCertificateExecutedRegime input).carry left =
          (publicCertificateExecutedRegime input).carry right ↔
        Nonempty
          (OperationallyCoDetermined
            (publicCertificateNormalization input) left right)

/-- Width readouts and their exact conservation characterisation. -/
structure PublicOperationalWidthCertificate (input : Nat) : Type 3 where
  private mk ::
  extensiveWidth :
    (publicRoleProfileFiniteCarrier input).frontier.length =
      2 ^ (input + 1)
  executedWidth :
    (publicCertificateExecutedRegime input).frontier.length = 1
  groupedDistinctProfiles :
    ExecutedGroupedDistinctProfiles (publicCertificateNormalization input)
  exponentialIffIndependentConservation :
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime
  exponentialIffCarryInjective :
    (regime : ObligationRegime (publicRoleProfileFiniteCarrier input)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Function.Injective regime.carry

def publicExecutionConstitutionCertificate
    (input : Nat) : PublicExecutionConstitutionCertificate input :=
  { executionErasesExactly :=
      publicCausalOperationalExecution_instrumented_exact input
    prefixLocal := (publicCausalOperationalExecution input).headsArePrefixLocal
    rolesConstituted :=
      (publicCausalOperationalExecution input).stagewiseDecomposition
        |>.rolesConstitutionExact }

def publicConstitutiveNormalizationCertificate
    (input : Nat) : PublicConstitutiveNormalizationCertificate input :=
  { normalizationExact := rfl
    normalizationConsumesConstitutiveChain := rfl
    constitutiveChainIsCausallyExact :=
      (publicCertificateNormalization input).constitutiveChainExact
    relationalConstitutionIsConsumed :=
      (publicCertificateNormalization input).constitutiveRelationalEvidence }

def publicOperationalRegimeCertificate
    (input : Nat) : PublicOperationalRegimeCertificate input :=
  { groupingAuthorizationExact := rfl
    groupingRelationalConstitutionIsChainConstitution := rfl
    groupingPreservationIsChainPreservation := rfl
    groupingSeparationIsChainSeparation := rfl
    exactRegimeExact := rfl
    carriedValuesAreProducedTargets :=
      publicCertificate_carry_value_eq_produced_target input
    regimeFibresAreExactlyProducedTargetFibres :=
      publicCertificate_carry_eq_iff_produced_target_eq input
    regimeFibresAreExactlyExecutedCoDetermination :=
      publicCertificate_carry_eq_iff_coDetermined input }

def publicOperationalWidthCertificate
    (input : Nat) : PublicOperationalWidthCertificate input :=
  { extensiveWidth := publicRoleProfileFiniteCarrier_width input
    executedWidth := publicCertificate_executedRegime_width input
    groupedDistinctProfiles :=
      { left := publicCertificateTransformedProfile input
        right := publicCertificateRetainedProfile input
        distinct := publicCertificateProfiles_distinct input
        coDetermined := publicCertificateProfiles_coDetermined input
        carriedTogether := publicCertificateProfiles_carryTogether input }
    exponentialIffIndependentConservation :=
      publicCertificate_exponential_iff_conservation input
    exponentialIffCarryInjective :=
      publicCertificate_exponential_iff_carry_injective input }

/--
Closed witness of the immutable scientific target, stratified in the same
order as its constitution.  Every layer refers to the one public carrier.
-/
structure ExactCausalExponentialTarget (input : Nat) : Type 3 where
  private mk ::
  execution : PublicExecutionConstitutionCertificate input
  normalization : PublicConstitutiveNormalizationCertificate input
  regime : PublicOperationalRegimeCertificate input
  width : PublicOperationalWidthCertificate input

/-- Construct the complete target from the single authoritative execution. -/
def exactCausalExponentialTarget
    (input : Nat) : ExactCausalExponentialTarget input :=
  { execution := publicExecutionConstitutionCertificate input
    normalization := publicConstitutiveNormalizationCertificate input
    regime := publicOperationalRegimeCertificate input
    width := publicOperationalWidthCertificate input }

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
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExecutedGroupedDistinctProfiles
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicExecutionConstitutionCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicExecutionConstitutionCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicConstitutiveNormalizationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicConstitutiveNormalizationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicOperationalRegimeCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicOperationalRegimeCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.PublicOperationalWidthCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicOperationalWidthCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ExactCausalExponentialTarget
#print axioms ConstitutiveSearch.EndogenousDecomposition.exactCausalExponentialTarget
/- AXIOM_AUDIT_END -/
