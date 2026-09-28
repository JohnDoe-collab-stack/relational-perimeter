import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PublicRelationalExtensiveFamily

/-!
# One-chain certificate for constitutive extensivity and operational reduction

All components below are indexed by one realization of the existing public
instrumented history.  The roles, profile carrier, program, interpreter,
reduction, extensive theorem, and reduced regime therefore cannot be assembled
from unrelated runs.
-/

namespace ConstitutiveSearch
namespace EndogenousDecomposition

open Extensive

set_option maxHeartbeats 800000

/-- Complete public certificate on one causally connected chain. -/
structure ConstitutiveExtensiveSeparationCertificate (input : Nat) where
  private mk ::
  realization : InstrumentedExecutionRealization
    (executeConstitutiveResolution input).constitutiveFeedbackHistory
  realizationExact : realization = publicInstrumentedExecutionRealization input
  stagewiseDecomposition :
    StagewiseExecutedDecompositionHistory realization.causalRun
  stagewiseDecompositionExact :
    stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory realization.causalRun
  rolesExact : stagewiseDecomposition.roles =
    buildRelationalConstitutiveRoleHistory realization.causalRun
  roleConstitutionExact :
    RelationalRoleHistoryConstitutionExact stagewiseDecomposition.roles
  executedRegime :
    ExecutedRoleObligationRegime stagewiseDecomposition.roles
  executedRegimeFromStagewise :
    executedRegime =
      executedRoleObligationRegimeOfStagewise stagewiseDecomposition
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
  interpreterExact :
    (profile : RoleOccurrenceProfile stagewiseDecomposition.roles) →
      interpretRoleOccurrenceProfile
          (compileRoleHistory stagewiseDecomposition.roles) profile
          (canonicalRoleProfilePayload stagewiseDecomposition.roles profile) =
        completedRoleAssignments stagewiseDecomposition.roles
  executedCarryFromReduction :
    (profile : RoleOccurrenceProfile stagewiseDecomposition.roles) →
      executedRegime.regime.carry profile =
        (executedRegime.reduce profile).1
  executedCarryDerivation :
    (profile : RoleOccurrenceProfile stagewiseDecomposition.roles) →
      ExecutedCarryDerivation executedRegime.reduction profile
        (executedRegime.regime.carry profile)
  localReductionWidthsExact :
    AllExecutedLocalWidthsExact
      (executedReductionLocalWidths executedRegime.reduction)
  separateConservationIffExponentialWidth :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier stagewiseDecomposition.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime
  exactRegimeCapacityIff :
    (regime : ObligationRegime
      (roleProfileFiniteCarrier stagewiseDecomposition.roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Nonempty
          (ExactRegimeSeparateCapacity regime
            (roleProfileFiniteCarrier
              stagewiseDecomposition.roles).frontier.length)
  retainedOperationalWidthExact :
    executedRegime.regime.frontier.length = 1
  executedRegimeDoesNotPreserveSeparately :
    ¬ PreservesIdentitiesSeparately executedRegime.regime

/-- The certificate's roles are the roles produced by its stagewise history. -/
def ConstitutiveExtensiveSeparationCertificate.roles
    {input : Nat}
    (certificate : ConstitutiveExtensiveSeparationCertificate input) :
    RelationalConstitutiveRoleHistory certificate.realization.causalRun :=
  certificate.stagewiseDecomposition.roles

/-- The complete certificate is constructed from the public execution alone. -/
def constitutiveExtensiveSeparationCertificate
    (input : Nat) : ConstitutiveExtensiveSeparationCertificate input := by
  let realization := publicInstrumentedExecutionRealization input
  let stagewiseDecomposition :=
    buildStagewiseExecutedDecompositionHistory realization.causalRun
  let roles := stagewiseDecomposition.roles
  let executedRegime :=
    executedRoleObligationRegimeOfStagewise stagewiseDecomposition
  let separateRegime := identityObligationRegime (roleProfileFiniteCarrier roles)
  have rolesConstitution : RelationalRoleHistoryConstitutionExact roles :=
    stagewiseDecomposition.rolesConstitutionExact
  have programSize : (compileRoleHistory roles).atomCount = input + 1 :=
    compileRoleHistory_atomCount_exact roles
  have extensiveWidth :
      (roleProfileFiniteCarrier roles).frontier.length = 2 ^ (input + 1) :=
    roleProfileFiniteCarrier_width roles
  have separateWidth :
      separateRegime.frontier.length = 2 ^ (input + 1) :=
    extensiveWidth
  have separateConservation :
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        separateRegime :=
    identityObligationRegime_conserves (roleProfileFiniteCarrier roles)
  have retainedWidth :
      executedRegime.regime.frontier.length = 1 :=
    rfl
  have notPreserving :
      ¬ PreservesIdentitiesSeparately executedRegime.regime := by
    intro preserves
    have fullWidth := full_width_of_preserves
      executedRegime.regime preserves
    have oneEqualsExponential : 1 = 2 ^ (input + 1) :=
      Eq.trans retainedWidth.symm (Eq.trans fullWidth extensiveWidth)
    have strictGrowth : 1 < 2 ^ (input + 1) :=
      Constructive.two_pow_strictly_grows (Nat.zero_lt_succ input)
    exact (Nat.ne_of_lt strictGrowth) oneEqualsExponential
  exact
    { realization := realization
      realizationExact := rfl
      stagewiseDecomposition := stagewiseDecomposition
      stagewiseDecompositionExact := rfl
      rolesExact :=
        buildStagewiseExecutedDecompositionHistory_roles_exact
          realization.causalRun
      roleConstitutionExact := rolesConstitution
      executedRegime := executedRegime
      executedRegimeFromStagewise := rfl
      programSizeExact := programSize
      extensiveWidthExact := extensiveWidth
      separateRegime := separateRegime
      separateRegimeExact := rfl
      separateRegimeWidthExact := separateWidth
      separateRegimeConserves := separateConservation
      interpreterExact := interpretCompiledRoleHistory_exact roles
      executedCarryFromReduction :=
        executedRegime.carryFromReduction
      executedCarryDerivation :=
        executedRegime.carryDerivation
      localReductionWidthsExact :=
        executedReductionLocalWidths_exact executedRegime.reduction
      separateConservationIffExponentialWidth :=
        roleConstituted_exponentialWidth_iff_distinctSeparateConservation roles
      exactRegimeCapacityIff :=
        roleConstituted_exponentialWidth_iff_exactRegimeCapacity roles
      retainedOperationalWidthExact := retainedWidth
      executedRegimeDoesNotPreserveSeparately := notPreserving }

/-- The public certificate states the target `iff` on its own source carrier. -/
theorem publicCertificate_exponential_iff_conservation
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  (constitutiveExtensiveSeparationCertificate input).separateConservationIffExponentialWidth
    regime

/-- The conservation side is positively inhabited on the same public chain. -/
def publicCertificateSeparateRegime
    (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles) :=
  (constitutiveExtensiveSeparationCertificate input).separateRegime

/-- The explicit separate regime has the exact exponential width. -/
theorem publicCertificate_separateRegime_exponentialWidth
    (input : Nat) :
    (publicCertificateSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  (constitutiveExtensiveSeparationCertificate input).separateRegimeWidthExact

/-- The explicit exponential regime conserves identities through itself. -/
theorem publicCertificate_separateRegime_conserves
    (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (publicCertificateSeparateRegime input) :=
  (constitutiveExtensiveSeparationCertificate input).separateRegimeConserves

/-- The executed regime is the projection of the same certificate's causal package. -/
def publicCertificateExecutedRegime
    (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles) :=
  (constitutiveExtensiveSeparationCertificate input).executedRegime.regime

/-- Every carried public profile is obtained from its proof-relevant reduction. -/
theorem publicCertificate_carry_from_reduction
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles) :
    (publicCertificateExecutedRegime input).carry profile =
      ((constitutiveExtensiveSeparationCertificate input).executedRegime.reduce
        profile).1 :=
  (constitutiveExtensiveSeparationCertificate input).executedCarryFromReduction
    profile

/-- Public witness of the complete source-indexed reduction behind `carry`. -/
def publicCertificateCarryDerivation
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationCertificate input).roles) :
    ExecutedCarryDerivation
      (constitutiveExtensiveSeparationCertificate input).executedRegime.reduction
      profile
      ((publicCertificateExecutedRegime input).carry profile) :=
  (constitutiveExtensiveSeparationCertificate input).executedCarryDerivation
    profile

/-- The executed regime's width is the readout of its reduction-derived frontier. -/
theorem publicCertificate_executedRegime_width
    (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
  (constitutiveExtensiveSeparationCertificate input).retainedOperationalWidthExact

/-- The public reduction keeps the source identities but does not conserve them
as independent operational obligations. -/
theorem publicCertificate_reduction_separates_identity_from_obligation
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (publicCertificateExecutedRegime input) :=
  (constitutiveExtensiveSeparationCertificate input).executedRegimeDoesNotPreserveSeparately

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate.roles
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_exponential_iff_conservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateSeparateRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_exponentialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_conserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateExecutedRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_carry_from_reduction
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateCarryDerivation
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_executedRegime_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_reduction_separates_identity_from_obligation
/- AXIOM_AUDIT_END -/
