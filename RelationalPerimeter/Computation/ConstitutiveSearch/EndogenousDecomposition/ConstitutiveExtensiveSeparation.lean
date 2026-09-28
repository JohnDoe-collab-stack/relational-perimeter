import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.PublicRelationalExtensiveFamily
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization

/-!
# One constitutive chain from primitive roles to operational width

The certificate follows one direction only:

relations and executed stages -> constituted roles -> source profiles ->
executed reduction -> computed target image -> obligation regime -> width.

The extensive width is a downstream readout.  No singleton obligation carrier
and no width are supplied independently of the executed target image.
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
  stagewiseDecomposition :
    StagewiseExecutedDecompositionHistory realization.causalRun
  stagewiseDecompositionExact :
    stagewiseDecomposition =
      buildStagewiseExecutedDecompositionHistory realization.causalRun
  rolesExact : stagewiseDecomposition.roles =
    buildRelationalConstitutiveRoleHistory realization.causalRun
  roleConstitutionExact :
    RelationalRoleHistoryConstitutionExact stagewiseDecomposition.roles
  normalization :
    ExecutedCausalNormalization stagewiseDecomposition.reduction
  normalizationExact :
    normalization =
      executedCausalNormalization stagewiseDecomposition.reduction
  operationalRegimeExact :
    normalization.operationalRegime =
      computedTargetImageRegime
        (roleProfileFiniteCarrier stagewiseDecomposition.roles)
        (roleOccurrenceProfileDecEq stagewiseDecomposition.roles)
        normalization.target
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
        retainedRoleProfile stagewiseDecomposition.reduction
  producedTargetFrontierExact :
    normalization.producedTargetFrontier =
      [retainedRoleProfile stagewiseDecomposition.reduction]
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
  executedRegimeDoesNotPreserveSeparately :
    ¬ PreservesIdentitiesSeparately normalization.operationalRegime

/-- The roles remain the history constituted by the execution. -/
def ConstitutiveExtensiveSeparationCertificate.roles
    {input : Nat}
    (certificate : ConstitutiveExtensiveSeparationCertificate input) :
    RelationalConstitutiveRoleHistory certificate.realization.causalRun :=
  certificate.stagewiseDecomposition.roles

/-- Construct the certificate in the same order as its constitutive chain. -/
def constitutiveExtensiveSeparationCertificate
    (input : Nat) : ConstitutiveExtensiveSeparationCertificate input := by
  let realization := publicInstrumentedExecutionRealization input
  let stagewise :=
    buildStagewiseExecutedDecompositionHistory realization.causalRun
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
      stagewiseDecomposition := stagewise
      stagewiseDecompositionExact := rfl
      rolesExact :=
        buildStagewiseExecutedDecompositionHistory_roles_exact
          realization.causalRun
      roleConstitutionExact := stagewise.rolesConstitutionExact
      normalization := normalization
      normalizationExact := rfl
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
      separateConservationIffExponentialWidth :=
        roleConstituted_exponentialWidth_iff_distinctSeparateConservation roles
      exactRegimeCapacityIff :=
        roleConstituted_exponentialWidth_iff_exactRegimeCapacity roles
      executedRegimeDoesNotPreserveSeparately := notPreserving }

/-- The canonical normalization produced by the public execution. -/
def publicCertificateNormalization
    (input : Nat) :
    ExecutedCausalNormalization
      (constitutiveExtensiveSeparationCertificate input).stagewiseDecomposition.reduction :=
  (constitutiveExtensiveSeparationCertificate input).normalization

/-- Its operational regime is the direct computed image. -/
def publicCertificateExecutedRegime
    (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationCertificate input).roles) :=
  (publicCertificateNormalization input).operationalRegime

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
  (constitutiveExtensiveSeparationCertificate input).carryFibresAreProducedTargetFibres
    left right

/-- Width one is read from the executed target image. -/
theorem publicCertificate_executedRegime_width
    (input : Nat) :
    (publicCertificateExecutedRegime input).frontier.length = 1 :=
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

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate.roles
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateNormalization
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateExecutedRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateCarryTrace
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_carry_eq_iff_produced_target_eq
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_executedRegime_width
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_exponential_iff_conservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateSeparateRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_exponentialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_conserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_reduction_separates_identity_from_obligation
/- AXIOM_AUDIT_END -/
