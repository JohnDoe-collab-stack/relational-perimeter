import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.MeasuredAccounting
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.EndogenousOperationalStability
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.InstrumentedExecutionRealization
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparation
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.OperationalProjection
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerSuccinctness
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProfiles
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleProfileArityTransport
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProgram
import RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RolewiseObligationRegime
import RelationalPerimeter.Computation.ConstitutiveSearch.FiniteExtensiveAddressing
import RelationalPerimeter.Computation.ConstitutiveSearch.RelationalRoleExtensiveFamily
import RelationalPerimeter.Computation.ConstitutiveSearch.SearchableTransportCodeValidation
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.GrowingDiscoveryBenchmark
import RelationalPerimeter.Computation.ConstitutiveSearch.SAT.TrajectoryDerivedClosure

/-!
# Endogenous operational decomposition

This module is the public statement layer for the computational construction.
It does not replace or summarize away the executed development below it.  It
exposes the exact properties that jointly establish the phenomenon:

1. opening produces two structurally distinct alternatives;
2. the relation between them is reconstructed by an executed search which can
   fail before producing any stage;
3. the reconstructed map acts on arbitrary continuations, independently of an
   acceptance proof;
4. acceptance preservation is proved separately and licenses frontier
   absorption without identifying the alternatives;
5. the executed result supplies both the seed and the provenance consumed by
   the next discovery.

The construction is instantiated on the explicit generated SAT family used by
the implementation.  No classical complexity-class conclusion is stated here.
-/

namespace RelationalPerimeter.Computation.EndogenousOperationalDecomposition

open ConstitutiveSearch
open ConstitutiveSearch.SAT
open ConstitutiveSearch.EndogenousDecomposition
open ConstitutiveSearch.Extensive
open ConstitutiveSearch.RelationalExtensive

set_option maxHeartbeats 800000

/-- The complete closed evidence package produced for every input. -/
abbrev Evidence (input : Nat) : Type 3 :=
  ConstitutiveSearch.EndogenousDecomposition.EndogenousOperationalDecompositionPerInputEvidence input

/-- Construct the complete evidence package; no operational premise is open. -/
def evidence (input : Nat) : Evidence input :=
  endogenousOperationalDecompositionPerInputEvidence input

/-- The uniformly indexed, measured family constructed by the implementation. -/
abbrev Family : Type 3 :=
  ConstitutiveSearch.EndogenousDecomposition.EndogenousOperationalDecompositionFamily

/-- Construct the complete family, including its canonical accounting ledger. -/
def family : Family :=
  endogenousOperationalDecompositionFamily

/--
The causally joined stability certificate for the public execution.  Its
structural, pending, and retained carriers are derived from the same dependent
role history as its measured failed-prefix and feedback evidence.
-/
abbrev OperationalStabilityEvidence (input : Nat) :=
  EndogenousOperationalStabilityEvidence
    (executeConstitutiveResolution input).feedbackRoleHistory

/-- Construct the stability certificate without any external premise. -/
def operationalStabilityEvidence (input : Nat) :
    OperationalStabilityEvidence input :=
  publicEndogenousOperationalStability input

/-- Public type of independent finite addressings of the exact structural
profiles constituted for one input. -/
abbrev IndependentProfileAddressing (input : Nat) :=
  ConstitutiveSearch.EndogenousDecomposition.IndependentProfileAddressing
    (PublicConstitutiveRoles input)

/-- The public typed program constructed from the executed role history. -/
abbrev ConstitutiveNormalizerProgram (input : Nat) :=
  PublicConstitutiveNormalizerProgram input

/-- Independent addressing of the profiles expanded by that exact program. -/
abbrev IndependentProgramProfileAddressing (input : Nat) :=
  ConstitutiveSearch.EndogenousDecomposition.IndependentProgramProfileAddressing
    (PublicConstitutiveRoles input) (ConstitutiveNormalizerProgram input)

/-- Public closed certificate joining exponential independent-profile
addressing with the exact linear-size normalizer program returned by the same
execution. -/
abbrev ConstitutiveNormalizerSuccinctnessEvidence (input : Nat) : Type 3 :=
  ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerSuccinctness input

def constitutiveNormalizerSuccinctnessEvidence (input : Nat) :
    ConstitutiveNormalizerSuccinctnessEvidence input :=
  publicConstitutiveNormalizerSuccinctness input

/-- Public name for the general class of relation-constituted extensive
families with nontrivial, unbounded histories. -/
abbrev RelationalRoleExtensiveFamily :=
  ConstitutiveSearch.RelationalExtensive.RelationalRoleExtensiveFamily

/-- Public name for its general binary subclass. -/
abbrev BinaryRelationalRoleExtensiveFamily :=
  ConstitutiveSearch.RelationalExtensive.BinaryRelationalRoleExtensiveFamily

/-- The existing executed family, viewed through the general binary class. -/
def publicBinaryExtensiveFamily : BinaryRelationalRoleExtensiveFamily :=
  publicBinaryRelationalRoleExtensiveFamily

/--
General target theorem. For every problem in every binary relational extensive
family, exact exponential obligation width occurs if and only if the regime
preserves the constituted identities separately.
-/
theorem binary_family_exponential_width_iff_separate_preservation
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      PreservesIdentitiesSeparately regime :=
  family.exponentialWidth_iff_preservesConstitutedIdentities problem regime

/--
Exact public formulation of the target at class level: the right-hand side
contains both identity distinction and separate addressing through the regime.
-/
theorem binary_family_exponential_width_iff_distinct_separate_conservation
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
        regime :=
  family.exponentialWidth_iff_distinctSeparateConservation problem regime

/-- The same general target through exact factorized address capacity. -/
theorem binary_family_exponential_width_iff_exact_separate_capacity
    (family : BinaryRelationalRoleExtensiveFamily)
    {index : Nat} (problem : family.Problem index)
    (regime : ObligationRegime (family.sourceCarrier problem)) :
    regime.frontier.length = 2 ^ family.stageCount problem ↔
      Nonempty
        (ExactRegimeSeparateCapacity regime
          (family.sourceCarrier problem).frontier.length) :=
  family.exponentialWidth_iff_exactRegimeCapacity problem regime

/-- The complete one-chain certificate on the public executed instance. -/
abbrev ConstitutiveExtensiveSeparationCertificate (input : Nat) :=
  ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate
    input

def constitutiveExtensiveSeparationEvidence (input : Nat) :
    ConstitutiveExtensiveSeparationCertificate input :=
  constitutiveExtensiveSeparationCertificate input

/-- Public-instance target with the stronger role-identity/addressing wording. -/
theorem constituted_exponential_width_iff_distinct_separate_conservation
    (input : Nat)
    (regime : ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles)) :
    regime.frontier.length = 2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable regime :=
  publicCertificate_exponential_iff_conservation input regime

/-- Explicit full-width regime on the same constituted public identities. -/
def constitutedDistinctSeparateRegime (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles) :=
  publicCertificateSeparateRegime input

/--
The executed regime on exactly the same role-constituted profile carrier as
the class-level `iff`; it is projected from the closed causal certificate.
-/
def executedConstitutiveObligationRegime (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles) :=
  publicCertificateExecutedRegime input

/-- The source-indexed reduction witness constructed behind one public carry. -/
def executedProfileCarryDerivation
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    ExecutedCarryDerivation
      (constitutiveExtensiveSeparationEvidence input).executedRegime.reduction
      profile
      ((executedConstitutiveObligationRegime input).carry profile) :=
  publicCertificateCarryDerivation input profile

/--
The causally admitted regime strengthens, without replacing, the original
executed-regime compatibility API.
-/
def causallyAdmittedConstitutiveObligationRegime (input : Nat) :
    ObligationRegime
      (roleProfileFiniteCarrier
        (constitutiveExtensiveSeparationEvidence input).roles) :=
  publicCertificateCausallyAdmittedExecutedRegime input

/-- Exact target produced by the authoritative causal normalizer. -/
def executedConstitutiveTarget
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    RoleOperationalOutputProfile
      (constitutiveExtensiveSeparationEvidence input).roles :=
  (publicCertificateCausallyAdmittedRegime input).normalization.target
    profile

/-- The exact executed trace from one constituted source to its public target. -/
def executedConstitutiveTargetTrace
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    ExecutedRoleProfileOutputReduction
      (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction
      profile
      (executedConstitutiveTarget input profile) :=
  (publicCertificateCausallyAdmittedRegime input).normalization.trace
    profile

/-- Criterion admission retained from every license of the executed reduction. -/
def executedConstitutiveCriterionAdmission
    (input : Nat) :
    ExecutedReductionCriterionAdmission
      (constitutiveExtensiveSeparationEvidence input).stagewiseDecomposition.reduction :=
  (publicCertificateCausallyAdmittedRegime input).criterionAdmission

/-- Every public operational target is exactly the completed typed output profile. -/
theorem executed_constitutive_target_exact
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    executedConstitutiveTarget input profile =
      completedRoleOperationalOutputProfile
        (constitutiveExtensiveSeparationEvidence input).roles :=
  (publicCertificateCausallyAdmittedRegime input).target_exact
    profile

/-- Downstream homogeneous readout of the produced operational target. -/
def executedConstitutiveTargetAssignments
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    List Assignment :=
  roleOperationalOutputAssignments
    (executedConstitutiveTarget input profile)

/-- The public target readout is the compiled interpreter output on that profile. -/
theorem executed_constitutive_targetAssignments_eq_interpreted_profile
    (input : Nat)
    (profile : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    executedConstitutiveTargetAssignments input profile =
      interpretRoleOccurrenceProfile
        (compileRoleHistory
          (constitutiveExtensiveSeparationEvidence input).roles)
        profile
        (canonicalRoleProfilePayload
          (constitutiveExtensiveSeparationEvidence input).roles profile) :=
  (publicCertificateCausallyAdmittedRegime input).targetAssignments_eq_interpreted_profile
    profile

/-- The authoritative carry has exactly the fibres of the produced targets. -/
theorem executed_carry_eq_iff_produced_target_eq
    (input : Nat)
    (left right : RoleOccurrenceProfile
      (constitutiveExtensiveSeparationEvidence input).roles) :
    (causallyAdmittedConstitutiveObligationRegime input).carry left =
        (causallyAdmittedConstitutiveObligationRegime input).carry right ↔
      executedConstitutiveTarget input left =
        executedConstitutiveTarget input right :=
  publicCertificate_causallyAdmitted_carry_eq_iff_target_eq input left right

/-- The complete produced-target image is exposed before its width readout. -/
theorem executed_produced_target_frontier_exact
    (input : Nat) :
    (publicCertificateCausallyAdmittedRegime input).normalization.producedTargetFrontier =
      [()] :=
  publicCertificate_causallyAdmitted_producedTargetFrontier_exact input

/-- The public image has width one exactly when all executed targets converge. -/
theorem executed_produced_target_width_one_iff_targets_converge
    (input : Nat) :
    (publicCertificateCausallyAdmittedRegime input).normalization.producedTargetFrontier.length = 1 ↔
      ∀ left right : RoleOccurrenceProfile
          (constitutiveExtensiveSeparationEvidence input).roles,
        executedConstitutiveTarget input left =
          executedConstitutiveTarget input right :=
  (publicCertificateCausallyAdmittedRegime input).producedTargetWidth_one_iff_targets_converge

/-- The operational regime width is exactly the produced-image width. -/
theorem executed_causal_regime_width_eq_produced_target_width
    (input : Nat) :
    (causallyAdmittedConstitutiveObligationRegime input).frontier.length =
      (publicCertificateCausallyAdmittedRegime input).normalization.producedTargetFrontier.length :=
  publicCertificate_causallyAdmitted_regimeWidth_eq_producedTargetWidth input

/-- The same class-level `iff` applies to the admitted regime on that carrier. -/
theorem executed_causal_regime_exponential_width_iff_separate_preservation
    (input : Nat) :
    (causallyAdmittedConstitutiveObligationRegime input).frontier.length =
        2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
        (causallyAdmittedConstitutiveObligationRegime input) :=
  constituted_exponential_width_iff_distinct_separate_conservation
    input (causallyAdmittedConstitutiveObligationRegime input)

/-- Width one of the admitted regime is derived from its exact target image. -/
theorem executed_causal_obligation_width_is_one (input : Nat) :
    (causallyAdmittedConstitutiveObligationRegime input).frontier.length = 1 :=
  publicCertificate_causallyAdmitted_executedRegime_width input

/-- The executed regime is subject to the same `iff` on the same carrier. -/
theorem executed_regime_exponential_width_iff_separate_preservation
    (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length =
        2 ^ (input + 1) ↔
      ConservesRoleIdentitiesAsDistinctSeparatelyAddressable
        (executedConstitutiveObligationRegime input) :=
  constituted_exponential_width_iff_distinct_separate_conservation
    input (executedConstitutiveObligationRegime input)

/-- Its width-one readout is downstream of the same causal certificate. -/
theorem executed_constitutive_obligation_width_is_one (input : Nat) :
    (executedConstitutiveObligationRegime input).frontier.length = 1 :=
  publicCertificate_executedRegime_width input

/-- The explicit conservative regime realizes the exponential side. -/
theorem constituted_distinct_separate_regime_has_exponential_width
    (input : Nat) :
    (constitutedDistinctSeparateRegime input).frontier.length =
      2 ^ (input + 1) :=
  publicCertificate_separateRegime_exponentialWidth input

/-- Its distinction and separate addressing are positively witnessed. -/
theorem constituted_distinct_separate_regime_conserves
    (input : Nat) :
    ConservesConstitutedIdentitiesDistinctlyAndSeparatelyAddressably
      (constitutedDistinctSeparateRegime input) :=
  publicCertificate_separateRegime_conserves input

/-- The executed reduction acts on that source carrier while refusing the
separate-obligation regime; it groups identities without identifying them. -/
theorem executed_reduction_does_not_preserve_separate_obligations
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (executedConstitutiveObligationRegime input) :=
  publicCertificate_reduction_separates_identity_from_obligation input

/-- The causally admitted regime makes the same separation on the same source. -/
theorem executed_causal_reduction_does_not_preserve_separate_obligations
    (input : Nat) :
    ¬ PreservesIdentitiesSeparately
      (causallyAdmittedConstitutiveObligationRegime input) :=
  publicCertificate_causallyAdmitted_separates_identity_from_obligation input

theorem independent_profile_addressing_requires_exponential_slots
    (input : Nat) (addressing : IndependentProfileAddressing input) :
    2 ^ (input + 1) <= addressing.slotCount :=
  public_independent_profile_slots_exponential input addressing

/-- The public program has one typed instruction per executed stage. -/
theorem constitutive_program_instruction_count_exact (input : Nat) :
    (ConstitutiveNormalizerProgram input).instructionCount = input + 1 :=
  public_constitutive_program_instructionCount_exact input

/-- The historical structural frontier is definitionally the exhaustive
profile expansion of the public program. -/
theorem structural_frontier_is_program_expansion (input : Nat) :
    structuralFrontier (PublicConstitutiveRoles input) =
      (ConstitutiveNormalizerProgram input).profileFrontier :=
  public_structural_frontier_is_program_expansion input

/-- The program-produced exhaustive expansion contains exactly
`2^(input+1)` profiles. -/
theorem constitutive_program_profile_width_exact (input : Nat) :
    (ConstitutiveNormalizerProgram input).profileWidth = 2 ^ (input + 1) :=
  public_constitutive_program_profileWidth_exact input

theorem constitutive_program_profiles_complete (input : Nat)
    (profile : (ConstitutiveNormalizerProgram input).Profile) :
    List.Mem profile (ConstitutiveNormalizerProgram input).profileFrontier :=
  public_constitutive_program_profiles_complete input profile

theorem constitutive_program_profiles_nodup (input : Nat) :
    (ConstitutiveNormalizerProgram input).profileFrontier.Nodup :=
  public_constitutive_program_profiles_nodup input

/-- Positively construct accepted data for every profile generated by the
same public program. -/
def constitutive_program_every_profile_accepted (input : Nat)
    (profile : (ConstitutiveNormalizerProgram input).Profile) :
    (ConstitutiveNormalizerProgram input).AcceptedProfilePayload profile :=
  public_constitutive_program_everyProfileAccepted input profile

/-- The same program interprets every accepted profile that its exhaustive
expansion produces. -/
theorem constitutive_program_profile_interpreter_exact (input : Nat)
    (profile : (ConstitutiveNormalizerProgram input).Profile)
    (payload : (ConstitutiveNormalizerProgram input).AcceptedProfilePayload
      profile) :
    canonicalProgramNormalizedPayloadToOperational
        (PublicConstitutiveRoles input)
        (interpretConstitutiveNormalizerProgramProfile
          (ConstitutiveNormalizerProgram input) profile payload) =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile
        (canonicalProgramAcceptedPayloadToStructural
          (PublicConstitutiveRoles input) profile payload) :=
  public_constitutive_program_profile_interpreter_exact input profile payload

/-- Independent finite addressing of the program-produced profiles requires
at least `2^(input+1)` distinct slots. -/
theorem independent_program_profile_addressing_requires_exponential_slots
    (input : Nat) (addressing : IndependentProgramProfileAddressing input) :
    2 ^ (input + 1) <= addressing.slotCount :=
  public_independent_program_profile_slots_exponential input addressing

/-- The instruction count and transport-atom metric are computed from the
same canonical program and agree exactly. -/
theorem constitutive_program_instruction_count_eq_code_size (input : Nat) :
    (ConstitutiveNormalizerProgram input).instructionCount =
      (ConstitutiveNormalizerProgram input).codeSize :=
  public_constitutive_program_instructionCount_eq_codeSize input

theorem constitutive_program_code_size_exact (input : Nat) :
    (ConstitutiveNormalizerProgram input).codeSize = input + 1 :=
  public_constitutive_program_codeSize_exact input

theorem constitutive_program_returns_executed_codes (input : Nat) :
    authoritativeNormalizerProgramReturnedCodes
        (ConstitutiveNormalizerProgram input)
        (buildConstitutiveNormalizerProgram_isAuthoritative
          (PublicConstitutiveRoles input)) =
      (executeConstitutiveResolution input).history.returnedCodes :=
  public_constitutive_program_returns_executed_codes input

theorem constitutive_normalizer_program_code_size_exact (input : Nat) :
    (constitutiveNormalizerSuccinctnessEvidence input).program.program.codeSize =
      input + 1 :=
  public_constitutive_normalizer_programCodeSize_exact input

theorem constitutive_normalizer_code_metric_exact (input : Nat) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    certificate.program.program.codeSize =
      compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) :=
  public_constitutive_normalizer_codeMetric_exact input

theorem constitutive_normalizer_code_size_exact (input : Nat) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    compiledLocalSize
        (authoritativeNormalizerProgramReturnedCodes
          certificate.program.program certificate.program.authoritative) =
      input + 1 :=
  public_constitutive_normalizer_codeSize_exact input

theorem constitutive_normalizer_interpreter_exact (input : Nat)
    (profile : StructuralObligation (PublicConstitutiveRoles input))
    (payload : StructuralAcceptedPayload
      (PublicConstitutiveRoles input) profile) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    interpretConstitutiveNormalizerProgram certificate.program.program
        profile payload =
      normalizeStructuralAcceptedPayload
        (PublicConstitutiveRoles input) profile payload :=
  public_constitutive_normalizer_interpreter_exact input profile payload

theorem constitutive_normalizer_returns_executed_codes (input : Nat) :
    let certificate := constitutiveNormalizerSuccinctnessEvidence input
    authoritativeNormalizerProgramReturnedCodes
        certificate.program.program certificate.program.authoritative =
      (executeConstitutiveResolution input).history.returnedCodes :=
  public_constitutive_normalizer_returns_executed_codes input

theorem constitutive_normalizer_instrumented_work_bound (input : Nat) :
    (executeConstitutiveResolution input).instrumentedWork <=
      resolutionInstrumentedPolynomial.eval input :=
  public_constitutive_normalizer_instrumentedWork_bound input

/-- The public certificate's reduction history is definitionally the one built
from the authoritative dependent role history. -/
theorem operational_reduction_history_is_exact (input : Nat) :
    (operationalStabilityEvidence input).reductions =
      buildExecutedOperationalReductionHistory
        (executeConstitutiveResolution input).feedbackRoleHistory :=
  (operationalStabilityEvidence input).reductionsExact

/-- The candidate-work history in the public certificate is the executed one. -/
theorem operational_discovery_work_is_exact (input : Nat) :
    (operationalStabilityEvidence input).discoveryWork =
      buildExecutedDiscoveryWorkHistory
        (executeConstitutiveResolution input).feedbackRoleHistory :=
  (operationalStabilityEvidence input).discoveryWorkExact

/-- The certificate cannot carry an arbitrary extensional annotation: its
projection history is exactly the history computed from executed reductions. -/
theorem operational_projection_history_is_exact (input : Nat) :
    (operationalStabilityEvidence input).extensionalProjection =
      buildExtensionalOperationalStabilityHistory
        (executeConstitutiveResolution input).feedbackRoleHistory :=
  (operationalStabilityEvidence input).extensionalProjectionExact

/-- The public normalizer is specified pointwise by the executed transport
history.  A profile-independent replacement does not inhabit this law. -/
theorem operational_normalizer_is_exact (input : Nat)
    (profile : StructuralObligation
      (executeConstitutiveResolution input).feedbackRoleHistory)
    (payload : StructuralAcceptedPayload
      (executeConstitutiveResolution input).feedbackRoleHistory profile) :
    (operationalStabilityEvidence input).normalizeAcceptedPayload
        profile payload =
      normalizeStructuralAcceptedPayload
        (executeConstitutiveResolution input).feedbackRoleHistory
        profile payload :=
  (operationalStabilityEvidence input).normalizeAcceptedPayloadExact
    profile payload

/-- The public causal history contains exactly `input + 1` openings. -/
theorem operational_stage_count_exact (input : Nat) :
    operationalStageCount
        (executeConstitutiveResolution input).feedbackRoleHistory = input + 1 :=
  operationalStageCount_eq_historyCount
    (executeConstitutiveResolution input).feedbackRoleHistory

/-- The structural carrier has exactly one Boolean role per executed opening. -/
theorem structural_width_is_exponential (input : Nat) :
    structuralWidth
        (executeConstitutiveResolution input).feedbackRoleHistory =
      2 ^ operationalStageCount
        (executeConstitutiveResolution input).feedbackRoleHistory :=
  (operationalStabilityEvidence input).structuralExact

/-- Before the discovered transports are applied, every structural role remains
an independent pending operational position. -/
theorem pending_operational_width_is_exponential (input : Nat) :
    pendingWidth
        (executeConstitutiveResolution input).feedbackRoleHistory =
      2 ^ operationalStageCount
        (executeConstitutiveResolution input).feedbackRoleHistory := by
  exact Eq.trans
    (operationalStabilityEvidence input).pendingExact
    (operationalStabilityEvidence input).structuralExact

/-- The retained operational carrier has exactly one profile. -/
theorem retained_operational_width_is_one (input : Nat) :
    executedWidth
        (executeConstitutiveResolution input).feedbackRoleHistory = 1 :=
  (operationalStabilityEvidence input).executedExact

/-- The transient width trace is a derived numerical readout of the executed
history. Its uniform bound is proved directly from that readout, not stored as a
causal premise of the public certificate. -/
theorem transient_operational_width_is_bounded (input : Nat) :
    WidthTraceAtMost 2
      (executedWidthTrace
        (executeConstitutiveResolution input).feedbackRoleHistory) :=
  executedWidthTrace_le_two
    (executeConstitutiveResolution input).feedbackRoleHistory

/-- For every public input, the executed retained carrier is strictly narrower
than the pending carrier generated by the same nonempty causal history. -/
theorem retained_width_is_strictly_below_pending (input : Nat) :
    executedWidth
        (executeConstitutiveResolution input).feedbackRoleHistory <
      pendingWidth
        (executeConstitutiveResolution input).feedbackRoleHistory := by
  apply executedWidth_lt_pendingWidth_of_positiveStageCount
  rw [operational_stage_count_exact]
  exact Nat.zero_lt_succ input

/-- The canonical public evidence supplies both the exact executed normalizer
and the global strict width separation.  Their conjunction is exposed here;
the local type-indexed causal comparison is stated separately by
`discovered_transport_reduces_same_opening_width`. -/
theorem executed_transports_induce_operational_width_reduction (input : Nat) :
    (∀ (profile : StructuralObligation
        (executeConstitutiveResolution input).feedbackRoleHistory)
      (payload : StructuralAcceptedPayload
        (executeConstitutiveResolution input).feedbackRoleHistory profile),
      (operationalStabilityEvidence input).normalizeAcceptedPayload
          profile payload =
        normalizeStructuralAcceptedPayload
          (executeConstitutiveResolution input).feedbackRoleHistory
          profile payload) ∧
    executedWidth
        (executeConstitutiveResolution input).feedbackRoleHistory <
      pendingWidth
        (executeConstitutiveResolution input).feedbackRoleHistory :=
  ⟨operational_normalizer_is_exact input,
    retained_width_is_strictly_below_pending input⟩

/-- On this explicit family the successful discovery is canonical at fixed
depth, although its availability, measured failed prefix, and production as
data are determined by the executed state-dependent search. -/
theorem executed_discovery_value_is_canonical_at_depth {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? =
      some stage.discovery := by
  have found := run.discoveryFound
  have returned := run.relationFromTransmittedState
  have same : run.discovery = stage.discovery :=
    Option.some.inj (found.symm.trans returned)
  rw [← same]
  exact run.discoveryExact

/-- On an actual executed stage, the authoritative extensional view is exactly
the projection of the discovered total transport with the executed numerical
readout. -/
theorem executed_extensional_view_is_discovered_projection {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStepToExtensionalView run =
      transportToExtensionalStabilityView
        (ExecutedExtensionalSeparator.discoveredTransport run)
        stage.sourceContinuation stage.sourceAccepted
        (executedStageWidthTrace run) (executedStageWidthReadoutBound run) :=
  ExecutedExtensionalSeparator.executed_view_is_projection_of_discovered run

/-- The same readout is a projection of the authoritative typed instruction
stored by the constitutive program. -/
theorem executed_extensional_view_is_authoritative_instruction_projection
    {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    executedStepToExtensionalView run =
      ExecutedExtensionalSeparator.executedTransportProjection run
        ((authoritativeNormalizerInstruction run).toAcceptingTransport run) :=
  ExecutedExtensionalSeparator.executed_view_is_projection_of_authoritative_instruction
    run

/-- On an actual executed stage, the comparison transport agrees with the
recorded projection at the observed source while remaining a distinct total
action on another continuation. -/
theorem comparison_transport_matches_executed_observation {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    (ExecutedExtensionalSeparator.observedConstantTransport run).map
        (executedStepToExtensionalView run).observedSource =
      (executedStepToExtensionalView run).observedRetained :=
  ExecutedExtensionalSeparator.comparison_matches_executed_observation run

/-- The public collision statement keeps the authoritative instruction in its
type: the specified projection identifies its total action with a comparison
at the recorded view while their actions differ on another continuation. -/
theorem authoritative_instruction_has_projection_collision {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ∃ comparison argument,
      ExecutedExtensionalSeparator.executedTransportProjection run
          ((authoritativeNormalizerInstruction run).toAcceptingTransport run) =
        ExecutedExtensionalSeparator.executedTransportProjection run comparison ∧
      ExecutedExtensionalSeparator.executedTransportAction run
          ((authoritativeNormalizerInstruction run).toAcceptingTransport run)
          argument ≠
        ExecutedExtensionalSeparator.executedTransportAction run
          comparison argument :=
  ExecutedExtensionalSeparator.authoritative_instruction_projection_collision run

/-- On an actual executed stage, the total operational action does not
factor through the state-and-quantity view. This is the public instance of the
generic projection-collision theorem: the discovered and comparison transports
have equal projections but different total actions. -/
theorem executed_state_width_view_does_not_determine_total_action {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ¬ ActionFactorsThrough
      (ExecutedExtensionalSeparator.executedTransportProjection run)
      (ExecutedExtensionalSeparator.executedTransportAction run) :=
  ExecutedExtensionalSeparator.authoritative_instruction_action_not_factors_on_executed_system
    run

/-- In the canonical initial-origin discovery associated with each input depth,
at least nine tenths of the tested candidates belong to the proved failed
prefix. This statement is scoped to that initial run, not to every stage of the
public history. -/
theorem initial_discovery_has_measured_failed_majority (input : Nat) :
    9 * (nextDiscoveryCommonOrigin input).run.discoveryRun.outcome.attempts ≤
      10 * (executedDiscoveryWorkEvidence
        (nextDiscoveryCommonOrigin input).run).search.failedCandidates.length :=
  initialExecutedDiscovery_failed_candidate_rate input

/-- Opening produces alternatives whose constituted decision histories differ. -/
theorem opening_produces_structurally_distinct_alternatives {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    (state.child discovery.var false discovery.fresh).context.decisions ≠
      (state.child discovery.var true discovery.fresh).context.decisions := by
  intro same
  have head :
      (⟨discovery.var, false⟩ : StructuralBranchDecision) =
        ⟨discovery.var, true⟩ :=
    List.head_eq_of_cons_eq same
  exact Bool.noConfusion (congrArg StructuralBranchDecision.value head)

/-- For the same executed opening, the absence of an operational transport
retains two positions while the transport returned by the executed discovery
retains exactly one.  The width change is therefore indexed by the discovered
status, not supplied as an independent numerical annotation. -/
theorem discovered_transport_reduces_same_opening_width {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    stageOperationalWidth
        (system := generatedStructuralBranchSystem
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex))
        (left := (executedOpening run).left)
        (right := (executedOpening run).right)
        none = 2 ∧
      stageOperationalWidth (executedOperationalStatus run) = 1 :=
  executedDiscovery_reduces_sameOpening_width run

/--
The reconstructed relation supplies a total map on arbitrary continuations.
No acceptance proof is an input to this operation.
-/
def transformContinuation {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation :
      GeneratedStructuralBranchContinuation
        (state.child discovery.var false discovery.fresh)) :
    GeneratedStructuralBranchContinuation
      (state.child discovery.var true discovery.fresh) :=
  discovery.relation.mapContinuation continuation

/-- Acceptance preservation is a theorem separate from the total map. -/
theorem transformContinuation_preserves_acceptance {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (continuation :
      GeneratedStructuralBranchContinuation
        (state.child discovery.var false discovery.fresh))
    (accepted :
      GeneratedStructuralBranchAccept
        (state.child discovery.var false discovery.fresh) continuation) :
    GeneratedStructuralBranchAccept
      (state.child discovery.var true discovery.fresh)
      (transformContinuation discovery continuation) :=
  discovery.relation.mapContinuation_accept continuation accepted

/-- The directed transport makes the first child dispensable for viability. -/
theorem reconstructed_transport_preserves_viability {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    (generatedStructuralBranchSystem root).Viable
        (state.child discovery.var false discovery.fresh) →
      (generatedStructuralBranchSystem root).Viable
        (state.child discovery.var true discovery.fresh) :=
  AcceptingContinuationTransport.preservesViable
    discovery.relation.toAcceptingTransport

/-- Opening and certified absorption preserve frontier viability exactly. -/
theorem opening_then_absorption_preserves_frontier_viability {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state) :
    FrontierViable (generatedStructuralBranchSystem root) [state] ↔
      FrontierViable (generatedStructuralBranchSystem root)
        [state.child discovery.var true discovery.fresh] :=
  AcceptedFrontierPreservation.viable_iff
    (EndogenousFlipDiscovery.fullStepPreservation discovery)

/--
The complete step is already defined on arbitrary continuations.  Its output
does not depend on which proof-relevant continuation witness is supplied once
the input assignments agree.
-/
theorem complete_step_precedes_acceptance {root : Cnf}
    {state : GeneratedStructuralBranchContext root}
    (discovery : EndogenousFlipDiscovery state)
    (left right : GeneratedStructuralBranchContinuation state)
    (same : left.1 = right.1) :
    (applyFullConstitutiveStep discovery left).1 =
      (applyFullConstitutiveStep discovery right).1 := by
  rw [applyFullConstitutiveStep_assignment, applyFullConstitutiveStep_assignment,
    same]

/-- A failed relation discovery admits no operational stage or produced next
state.  This statement applies to every threaded state and does not rely on the
freshness invariant of the successful canonical execution. -/
theorem failed_discovery_constructs_no_stage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (built : ConstructedThreadedStageRun state) : False :=
  failedDiscovery_noConstructedStage state failed built

/-- Failure also excludes every positive-length authoritative descendant
history, rather than merely selecting the `none` branch of a builder. -/
theorem failed_discovery_constructs_no_descendant_history {depth count : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (failed : (runThreadedNextDiscovery state).outcome.discovered? = none)
    (history : ConstitutiveExecutionHistory (count := count + 1) state) : False :=
  failedDiscovery_noPositiveHistory state failed history

/-- Every generated decoy candidate fails to produce the required relation. -/
theorem decoy_relation_candidates_fail
    (input candidate : Nat)
    (member : candidate ∈ distinctDecoyVariables (input + 1)) :
    tryEndogenousFlipCandidate
        (distinctGrowingDiscoveryRoot input) candidate = none :=
  distinctGrowingDiscoveryDecoyCandidate_none input candidate member

/-- Discovery returns a relation only after the exact recorded attempt count. -/
theorem relation_is_reconstructed_after_exact_attempts (depth : Nat) :
    ∃ discovery,
      (stageDiscoveryRun depth).outcome.discovered? = some discovery ∧
      discovery.var =
        growingDiscoverySplitVar (constructStage depth).searchIndex ∧
      (stageDiscoveryRun depth).outcome.attempts =
        (constructStage depth).searchIndex + 2 :=
  stageDiscovery_found_after_exact_attempts depth

/-- The unfiltered stage-local reference effort grows strictly with depth. -/
theorem executed_relation_search_attempts_grow (depth : Nat) :
    (stageRecordedDiscoveryRun depth).outcome.attempts <
      (stageRecordedDiscoveryRun (depth + 1)).outcome.attempts :=
  stageRecordedDiscovery_attempts_strict depth

/-- The total relation-search effort emitted by the authoritative feedback
recursion is exactly the recursively accumulated, provenance-filtered effort. -/
theorem authoritative_relation_search_attempts_exact (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts =
      threadedAttemptTotal (2 * input + 10) (input + 1) :=
  executeConstitutiveResolution_attempts_exact input

/-- The total relation-search effort emitted by the authoritative feedback
recursion grows strictly with successive external inputs.  This is the counter
of the actual provenance-filtered execution, not the unfiltered reference run. -/
theorem authoritative_relation_search_attempts_grow (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts <
      (executeConstitutiveResolution (input + 1)).stats.discoveryAttempts :=
  executeConstitutiveResolution_attempts_strict input

/- The causal execution begins from the endpoint produced by its measured
initialization run, rather than from an independently rebuilt source. -/
theorem initial_state_uses_measured_initialization (input : Nat) :
    let run := executeConstitutiveResolution input
    run.threadedInitialState =
      initialThreadedConstitutiveStateFromInitialization run.initialization := by
  exact (executeConstitutiveResolution input).threadedInitialStateFromInitialization

/--
The seed transmitted to the next stage is read definitionally from the state
produced by the executed application.  It is not a datum of the initial branch.
-/
theorem produced_seed_is_read_from_executed_state {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    executedProducedSearchSeed stage =
      (match stage.execution.producedState.context.decisions with
       | [] => 0
       | decision :: _ => decision.var) :=
  rfl

/-- The next operational state stores exactly that produced-state readout. -/
theorem next_state_stores_produced_seed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
    (realizeNextOperationalState state stage avoid).next.searchSeed =
      executedProducedSearchSeed stage :=
  rfl

/-- The retained branch determination is read from the executed application. -/
theorem retained_decision_reads_executed_output {depth : Nat}
    {assignment : SequentialAssignment depth}
    (stage : SequentialStageRun depth assignment) :
    (executedBranchDecision stage).value =
      stage.application.output.1 (stageSelectedVar (depth + 1)) :=
  rfl

/-- Candidate extraction runs on the operational root built from the seed. -/
theorem extraction_uses_seeded_operational_root {depth : Nat}
    (generation : CanonicalStageGeneration depth)
    (searchSeed : Nat)
    (searchSeedExact : searchSeed = generatedSearchSeed generation) :
    (measuredGeneratedExtractionFromSeed generation searchSeed
      searchSeedExact).extraction =
      runCandidateExtraction
        (measuredGeneratedExtractionFromSeed generation searchSeed
          searchSeedExact).operationalRoot :=
  rfl

/-- The next discovery consumes the bundle built from the transmitted seed. -/
theorem next_discovery_bundle_uses_transmitted_seed {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    (runThreadedNextDiscovery state).generated =
      measuredGeneratedExtractionFromSeed state.generation state.searchSeed
        state.searchSeedExact :=
  rfl

/-- The state produced by one stage supplies the seed consumed by the next. -/
theorem produced_state_seeds_next_discovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    run.nextRun.next.searchSeed = executedProducedSearchSeed stage ∧
      nextDiscovery.generated =
        measuredGeneratedExtractionFromSeed
          run.nextRun.next.generation
          run.nextRun.next.searchSeed
          run.nextRun.next.searchSeedExact :=
  run.nextDiscoveryConsumesRetainedSearchSeed

/-- The provenance produced by one stage filters the next candidate domain. -/
theorem produced_provenance_filters_next_discovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    let nextDiscovery := runThreadedNextDiscovery run.nextRun.next
    nextDiscovery.candidates =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).retained ∧
      nextDiscovery.filtering.visits =
        (filterCandidatesByProvenance
          (stage.schedule.entry.var :: state.provenance)
          nextDiscovery.generated.extraction.candidates).visits :=
  run.nextDiscoveryConsumesProducedProvenance

/-- The next discovery outcome does not factor through the permitted projection. -/
theorem next_discovery_depends_on_constitution (depth : Nat) :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := depth))
        (nextDiscoveryOutcome (depth := depth)) :=
  nextDiscovery_not_factors depth

/-- Erasing the accumulated history yields a vacuously fresh next state. -/
theorem erased_state_is_fresh_for_next (depth : Nat) :
    ThreadedStateFreshForNext (erasedNextDiscoveryState depth).state := by
  intro decision member
  cases member

/--
The same projected discovery reading can arise from differently constituted
searches: the retained candidate traces still record the distinction.
-/
theorem same_reading_can_have_different_constitution (depth : Nat) :
    (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).outcome.discovered? =
        (runThreadedNextDiscovery (erasedNextDiscoveryState depth).state).outcome.discovered? ∧
      (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).candidates ≠
        (runThreadedNextDiscovery (erasedNextDiscoveryState depth).state).candidates := by
  refine ⟨?_, reachableHistory_candidateTraces_different depth⟩
  rw [runThreadedNextDiscovery_discovered_exact _
      (retainedNextDiscoveryState_fresh depth),
    runThreadedNextDiscovery_discovered_exact _
      (erased_state_is_fresh_for_next depth)]

/-- The separator states agree on every permitted projectable state datum. -/
theorem separator_states_share_projectable_data (depth : Nat) :
    (blockedNextDiscoveryState depth).assignment =
        (retainedNextDiscoveryState depth).assignment ∧
      (blockedNextDiscoveryState depth).state.generation =
        (retainedNextDiscoveryState depth).state.generation ∧
      (blockedNextDiscoveryState depth).state.searchSeed =
        (retainedNextDiscoveryState depth).state.searchSeed :=
  ⟨rfl, rfl, rfl⟩

/--
Despite that agreement, their constituted histories and material discovery
outcomes differ.
-/
theorem separator_states_have_different_constitutions_and_outcomes
    (depth : Nat) :
    (blockedNextDiscoveryState depth).state.decisions ≠
        (retainedNextDiscoveryState depth).state.decisions ∧
      (runThreadedNextDiscovery (blockedNextDiscoveryState depth).state).outcome.discovered? ≠
        (runThreadedNextDiscovery (retainedNextDiscoveryState depth).state).outcome.discovered? := by
  refine ⟨?_, ?_⟩
  · intro same
    exact nextDiscovery_histories_distinct depth same.symm
  · intro same
    exact nextDiscovery_outcome_different depth same.symm

end RelationalPerimeter.Computation.EndogenousOperationalDecomposition

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.evidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.family
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.OperationalStabilityEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operationalStabilityEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.IndependentProfileAddressing
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.ConstitutiveNormalizerProgram
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.IndependentProgramProfileAddressing
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.ConstitutiveNormalizerSuccinctnessEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutiveNormalizerSuccinctnessEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.RelationalRoleExtensiveFamily
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.BinaryRelationalRoleExtensiveFamily
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.publicBinaryExtensiveFamily
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.binary_family_exponential_width_iff_separate_preservation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.binary_family_exponential_width_iff_distinct_separate_conservation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.binary_family_exponential_width_iff_exact_separate_capacity
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.ConstitutiveExtensiveSeparationCertificate
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutiveExtensiveSeparationEvidence
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constituted_exponential_width_iff_distinct_separate_conservation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutedDistinctSeparateRegime
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executedConstitutiveObligationRegime
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executedProfileCarryDerivation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.causallyAdmittedConstitutiveObligationRegime
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executedConstitutiveTarget
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executedConstitutiveTargetTrace
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executedConstitutiveCriterionAdmission
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_constitutive_target_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executedConstitutiveTargetAssignments
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_constitutive_targetAssignments_eq_interpreted_profile
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_carry_eq_iff_produced_target_eq
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_produced_target_frontier_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_produced_target_width_one_iff_targets_converge
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_causal_regime_width_eq_produced_target_width
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_causal_regime_exponential_width_iff_separate_preservation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_causal_obligation_width_is_one
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_regime_exponential_width_iff_separate_preservation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_constitutive_obligation_width_is_one
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constituted_distinct_separate_regime_has_exponential_width
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constituted_distinct_separate_regime_conserves
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_reduction_does_not_preserve_separate_obligations
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_causal_reduction_does_not_preserve_separate_obligations
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.independent_profile_addressing_requires_exponential_slots
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_instruction_count_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.structural_frontier_is_program_expansion
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_profile_width_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_profiles_complete
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_profiles_nodup
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_every_profile_accepted
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_profile_interpreter_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.independent_program_profile_addressing_requires_exponential_slots
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_instruction_count_eq_code_size
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_code_size_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_program_returns_executed_codes
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_normalizer_program_code_size_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_normalizer_code_metric_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_normalizer_code_size_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_normalizer_interpreter_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_normalizer_returns_executed_codes
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.constitutive_normalizer_instrumented_work_bound
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_reduction_history_is_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_discovery_work_is_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_projection_history_is_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_normalizer_is_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.operational_stage_count_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.structural_width_is_exponential
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.pending_operational_width_is_exponential
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_operational_width_is_one
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.transient_operational_width_is_bounded
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_width_is_strictly_below_pending
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_transports_induce_operational_width_reduction
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_discovery_value_is_canonical_at_depth
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_extensional_view_is_discovered_projection
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_extensional_view_is_authoritative_instruction_projection
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.comparison_transport_matches_executed_observation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.authoritative_instruction_has_projection_collision
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_state_width_view_does_not_determine_total_action
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.initial_discovery_has_measured_failed_majority
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.opening_produces_structurally_distinct_alternatives
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.discovered_transport_reduces_same_opening_width
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.transformContinuation
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.transformContinuation_preserves_acceptance
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.reconstructed_transport_preserves_viability
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.opening_then_absorption_preserves_frontier_viability
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.complete_step_precedes_acceptance
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.failed_discovery_constructs_no_stage
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.failed_discovery_constructs_no_descendant_history
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.decoy_relation_candidates_fail
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.relation_is_reconstructed_after_exact_attempts
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.executed_relation_search_attempts_grow
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.authoritative_relation_search_attempts_exact
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.authoritative_relation_search_attempts_grow
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.initial_state_uses_measured_initialization
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.produced_seed_is_read_from_executed_state
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.next_state_stores_produced_seed
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.retained_decision_reads_executed_output
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.extraction_uses_seeded_operational_root
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.next_discovery_bundle_uses_transmitted_seed
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.produced_state_seeds_next_discovery
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.produced_provenance_filters_next_discovery
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.next_discovery_depends_on_constitution
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.erased_state_is_fresh_for_next
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.same_reading_can_have_different_constitution
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.separator_states_share_projectable_data
#print axioms RelationalPerimeter.Computation.EndogenousOperationalDecomposition.separator_states_have_different_constitutions_and_outcomes
/- AXIOM_AUDIT_END -/
