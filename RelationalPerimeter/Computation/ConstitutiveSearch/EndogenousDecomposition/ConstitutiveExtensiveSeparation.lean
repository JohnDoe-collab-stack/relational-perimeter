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

/-- Complete public certificate on one causally connected chain. -/
structure ConstitutiveExtensiveSeparationCertificate (input : Nat) where
  private mk ::
  realization : InstrumentedExecutionRealization
    (executeConstitutiveResolution input).constitutiveFeedbackHistory
  realizationExact : realization = publicInstrumentedExecutionRealization input
  roles : RelationalConstitutiveRoleHistory realization.causalRun
  rolesExact : roles =
    buildRelationalConstitutiveRoleHistory realization.causalRun
  roleConstitutionExact : RelationalRoleHistoryConstitutionExact roles
  program : RoleIndexedProgram roles
  programExact : program = compileRoleHistory roles
  reduction : ExecutedRoleReductionHistory program
  programSizeExact : program.atomCount = input + 1
  extensiveWidthExact :
    (roleProfileFiniteCarrier roles).frontier.length = 2 ^ (input + 1)
  separateRegime : ObligationRegime (roleProfileFiniteCarrier roles)
  separateRegimeExact :
    separateRegime = identityObligationRegime (roleProfileFiniteCarrier roles)
  separateRegimeWidthExact :
    separateRegime.frontier.length = 2 ^ (input + 1)
  separateRegimeConserves :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      separateRegime
  interpreterExact :
    (profile : RoleOccurrenceProfile roles) →
      interpretRoleOccurrenceProfile program profile
          (canonicalRoleProfilePayload roles profile) =
        completedRoleAssignments roles
  localReductionWidthsExact :
    AllExecutedLocalWidthsExact (executedReductionLocalWidths reduction)
  separateConservationIffExponentialWidth :
    (regime : ObligationRegime (roleProfileFiniteCarrier roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime
  exactRegimeCapacityIff :
    (regime : ObligationRegime (roleProfileFiniteCarrier roles)) →
      regime.frontier.length = 2 ^ (input + 1) ↔
        Nonempty
          (ExactRegimeSeparateCapacity regime
            (roleProfileFiniteCarrier roles).frontier.length)
  retainedOperationalWidthExact :
    (executedObligationRegimeOfReduction roles reduction).frontier.length = 1
  executedRegimeDoesNotPreserveSeparately :
    ¬ PreservesIdentitiesSeparately
      (executedObligationRegimeOfReduction roles reduction)

/-- The complete certificate is constructed from the public execution alone. -/
def constitutiveExtensiveSeparationCertificate
    (input : Nat) : ConstitutiveExtensiveSeparationCertificate input := by
  let realization := publicInstrumentedExecutionRealization input
  let roles := buildRelationalConstitutiveRoleHistory realization.causalRun
  let program := compileRoleHistory roles
  let reduction := buildExecutedRoleReductionHistory roles
  let separateRegime := identityObligationRegime (roleProfileFiniteCarrier roles)
  have rolesConstitution : RelationalRoleHistoryConstitutionExact roles :=
    buildRelationalConstitutiveRoleHistory_exact realization.causalRun
  have programSize : program.atomCount = input + 1 :=
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
      (executedObligationRegimeOfReduction roles reduction).frontier.length = 1 :=
    rfl
  have notPreserving :
      ¬ PreservesIdentitiesSeparately
        (executedObligationRegimeOfReduction roles reduction) := by
    intro preserves
    have fullWidth := full_width_of_preserves
      (executedObligationRegimeOfReduction roles reduction) preserves
    have oneEqualsExponential : 1 = 2 ^ (input + 1) :=
      Eq.trans retainedWidth.symm (Eq.trans fullWidth extensiveWidth)
    have strictGrowth : 1 < 2 ^ (input + 1) :=
      Constructive.two_pow_strictly_grows (Nat.zero_lt_succ input)
    exact (Nat.ne_of_lt strictGrowth) oneEqualsExponential
  exact
    { realization := realization
      realizationExact := rfl
      roles := roles
      rolesExact := rfl
      roleConstitutionExact := rolesConstitution
      program := program
      programExact := rfl
      reduction := reduction
      programSizeExact := programSize
      extensiveWidthExact := extensiveWidth
      separateRegime := separateRegime
      separateRegimeExact := rfl
      separateRegimeWidthExact := separateWidth
      separateRegimeConserves := separateConservation
      interpreterExact := interpretCompiledRoleHistory_exact roles
      localReductionWidthsExact := executedReductionLocalWidths_exact reduction
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

/-- The public reduction keeps the source identities but does not conserve them
as independent operational obligations. -/
theorem publicCertificate_reduction_separates_identity_from_obligation
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (executedObligationRegimeOfReduction
        (constitutiveExtensiveSeparationCertificate input).roles
        (constitutiveExtensiveSeparationCertificate input).reduction) :=
  (constitutiveExtensiveSeparationCertificate input).executedRegimeDoesNotPreserveSeparately

end EndogenousDecomposition
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.constitutiveExtensiveSeparationCertificate
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_exponential_iff_conservation
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificateSeparateRegime
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_exponentialWidth
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_separateRegime_conserves
#print axioms ConstitutiveSearch.EndogenousDecomposition.publicCertificate_reduction_separates_identity_from_obligation
/- AXIOM_AUDIT_END -/
