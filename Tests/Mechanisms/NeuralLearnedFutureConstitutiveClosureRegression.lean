import RelationalPerimeter.Agents.Neural.LearnedFutureConstitutiveClosure

set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.ContinuationSignatures

theorem learned_future_source_is_installed_successor :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedCertifiedRuntime.current.state =
      learnedCandidateFutureSource learnedAlignedCandidateAtInitial :=
  learnedAlignedRuntime_futureSource_exact

theorem learned_future_source_is_l3_produced_successor :
    learnedAlignedProducedFutureObservation.source =
      learnedCandidateFutureSource learnedAlignedCandidateAtInitial :=
  learnedAlignedProducedFutureSource_exact

theorem learned_runtime_future_source_is_l3_produced_source :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedAlignedCertifiedRuntime.current.state =
      learnedAlignedProducedFutureObservation.source :=
  learnedAlignedRuntimeFutureSource_is_produced

theorem learned_extended_runtime_future_source_is_l3_produced_source :
    LearnedExtendedOperationalContract.futureSourceOfState
        learnedExtendedCertifiedRuntime.current.state =
      learnedExtendedProducedFutureObservation.source :=
  learnedExtendedRuntimeFutureSource_is_produced

theorem learned_future_has_positive_admission :
    independentLearnedFutureContract.enabled
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedAdmittedFutureRequest = true :=
  learnedAdmittedFutureRequest_enabled

theorem learned_future_has_positive_refusal :
    independentLearnedFutureContract.enabled
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedRefusedFutureRequest = false :=
  learnedRefusedFutureRequest_disabled

theorem learned_future_immediate_read_does_not_separate :
    independentLearnedFutureContract.read
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) =
      independentLearnedFutureContract.read
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) :=
  learnedAlignedBypass_immediate_read_equal

theorem learned_future_empty_outcome_does_not_separate :
    independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) [] =
      independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) [] :=
  learnedAlignedBypass_empty_future_equal

theorem learned_future_nonempty_continuation_separates :
    independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedAlignedBypassFutureSeparator.requests ≠
      independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial)
        learnedAlignedBypassFutureSeparator.requests :=
  learnedAlignedBypassFutureSeparator.different

theorem learned_future_separator_is_nonempty :
    learnedAlignedBypassFutureSeparator.requests ≠ [] :=
  learnedAlignedBypass_separator_nonempty

theorem learned_future_universal_exact_separation
    (Memory : Type 3)
    (realization : ExactRealization independentLearnedFutureContract Memory) :
    realization.project
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) ≠
      realization.project
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) :=
  learnedEveryExactRealizationSeparatesAlignedFromBypass Memory realization

theorem learned_future_positive_realization_is_exact
    (source : IndependentLearnedFutureSource)
    (requests : List IndependentLearnedFutureInput) :
    independentLearnedFutureContract.outcome source requests =
      independentLearnedReducedFutureContract.outcome
        (independentLearnedFutureProjection source) requests :=
  learnedBehavioralFutureRealization_preserves_every_finite_future
    source requests

theorem learned_renamed_identity_is_installed :
    submitUpdate learnedInitialCertifiedRuntime
        learnedRenamedIdentityRuntimeUpdate =
      .ok learnedRenamedIdentityCertifiedRuntime :=
  submitUpdate_learned_renamed_identity_exact

theorem learned_forgetting_histories_are_actually_distinct :
    learnedAlignedHistoricalForgettingInput ≠
      learnedRenamedHistoricalForgettingInput :=
  learnedHistoricalForgettingInputs_distinct

theorem learned_forgetting_installed_identities_are_distinct :
    LearnedHistoricalStableOrigin.aligned.firstInputSerial ≠
      LearnedHistoricalStableOrigin.renamed.firstInputSerial :=
  learnedHistoricalStableOrigin_identities_distinct

theorem learned_forgetting_pre_action_identities_are_distinct :
    (executeLearnedHistoricalPreActionState .aligned).installedIdentity ≠
      (executeLearnedHistoricalPreActionState .renamed).installedIdentity :=
  learnedHistoricalPreActionIdentities_distinct

theorem learned_forgetting_pre_action_identity_is_installed
    (origin : LearnedHistoricalStableOrigin) :
    (executeLearnedHistoricalPreActionState origin).installedIdentity =
      origin.runtimeFirstInputSerial :=
  learnedHistoricalPreAction_runtimeIdentity_exact origin

theorem learned_forgetting_consumes_installed_state
    (origin : LearnedHistoricalStableOrigin) :
    origin.runtime.current.state = learnedAlignedState :=
  origin.runtime_state_exact

def learned_forgetting_history_is_admitted
    (origin : LearnedHistoricalStableOrigin) :
    LearnedAdmittedStableNaming origin.serializedNaming :=
  learnedFutureForgettingRC4.historiesAdmitted origin

def learned_forgetting_action_is_indexed_by_installed_state
    (origin : LearnedHistoricalStableOrigin) :
    LearnedActionWitness origin.runtime.current.state :=
  (executeLearnedHistoricalFutureForgettingTrace origin).action

theorem learned_forgetting_effect_is_produced_from_exact_action
    (origin : LearnedHistoricalStableOrigin) :
    (executeLearnedHistoricalFutureForgettingTrace origin).effect =
      produceLearnedEffect
        (executeLearnedHistoricalFutureForgettingTrace origin).action :=
  (executeLearnedHistoricalFutureForgettingTrace origin).effectExact

theorem learned_forgetting_outputs_are_equal :
    learnedAlignedExecutedFutureForgetting.output =
      learnedRenamedExecutedFutureForgetting.output :=
  learnedExecutedFutureForgetting_outputs_equal

theorem learned_forgetting_preserves_all_finite_futures
    (origin : LearnedHistoricalStableOrigin)
    (requests : List IndependentLearnedFutureInput) :
    independentLearnedFutureContract.outcome
        (LearnedAlignedOperationalContract.futureSourceOfState
          learnedAlignedEffect.targetState) requests =
      independentLearnedReducedFutureContract.outcome
        (executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
          { origin := origin }).output requests :=
  learnedExecutedFutureForgetting_preserves_every_finite_future
    origin requests

theorem learned_forgetting_has_no_joint_recoverer
    (recover : IndependentLearnedOperationalMemory ->
      LearnedHistoricalStableOrigin) :
    Not (
      recover learnedAlignedExecutedFutureForgetting.output =
          learnedAlignedHistoricalForgettingInput.origin ∧
        recover learnedRenamedExecutedFutureForgetting.output =
          learnedRenamedHistoricalForgettingInput.origin) := by
  intro recovered
  exact learnedExecutedFutureForgetting_origin_not_recoverable recover
    recovered.1 recovered.2

theorem learned_forgetting_output_is_runtime_reduced_memory :
    learnedAlignedForgottenCurrentAgent.memory =
      learnedAlignedExecutedFutureForgetting.output :=
  learnedAlignedForgottenMemory_is_executedReduction

def learned_post_forgetting_continuation_is_authorized :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent
      (.continueCurrent learnedAdmittedFutureRequest) :=
  learnedPostForgettingContinuationPermission

theorem learned_post_forgetting_refused_future_remains_refused :
    PostForgettingPermission LearnedAlignedCurrentAgent
        learnedAlignedForgottenCurrentAgent
        (.continueCurrent learnedRefusedFutureRequest) -> False :=
  learnedPostForgettingRefusedFuture_stays_refused

def learned_post_forgetting_contract_change_is_justified :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent
      (forgotten := learnedAlignedForgottenCurrentAgent) .extended :=
  learnedJustifiedExtendedTransitionAfterForgetting

def learned_post_forgetting_contract_change_is_authorized :
    PostForgettingPermission LearnedAlignedCurrentAgent
      learnedAlignedForgottenCurrentAgent (.changeContract .extended) :=
  learnedPostForgettingContractChangePermission

def learned_post_forgetting_persistent_intent_is_transported :
    learnedConstitutiveMetaContract.TargetPersistentWitness .aligned .extended
      .admittedIntent :=
  learnedPostForgettingTransportedIntent

def learned_post_forgetting_authorization_is_rechecked :
    learnedConstitutiveMetaContract.RecheckedWitness .aligned .extended
      .authorizationConsumption :=
  learnedPostForgettingRecheckedAuthorization

theorem learned_post_forgetting_historical_return_is_refused :
    JustifiedPostForgettingTransition LearnedAlignedCurrentAgent
      (forgotten := learnedAlignedForgottenCurrentAgent) .initial ->
      False :=
  learnedPostForgettingReturnToInitial_refused

theorem learned_rc4_certificate_uses_nonempty_separator :
    learnedFutureForgettingRC4.separator.requests ≠ [] :=
  learnedFutureForgettingRC4.separatorNonempty

def learned_joint_closure_has_the_exact_dependent_lineage :
    LearnedArtifactExecutionLineage :=
  learnedConstitutiveAlignmentClosure.lineage

theorem learned_joint_closure_lineage_is_canonical :
    learnedConstitutiveAlignmentClosure.lineage =
      learnedArtifactExecutionLineage :=
  learnedConstitutiveAlignmentClosure.lineageExact

theorem learned_joint_closure_installs_both_successors :
    submitUpdate learnedAlignedCertifiedRuntime
      learnedExtendedSubmittedRuntimeUpdate =
      .ok learnedExtendedCertifiedRuntime :=
  learnedConstitutiveAlignmentClosure.extendedInstalled

theorem learned_joint_closure_future_comes_from_installed_runtime :
    LearnedAlignedOperationalContract.futureSourceOfState
        learnedConstitutiveAlignmentClosure.alignedRuntime.current.state =
      learnedCandidateFutureSource
        learnedConstitutiveAlignmentClosure.divergence.alignedCandidate :=
  learnedConstitutiveAlignmentClosure.futureSourceFromInstalledRuntime

theorem learned_joint_closure_forgetting_consumes_aligned_runtime :
    LearnedHistoricalStableOrigin.aligned.runtime =
      learnedConstitutiveAlignmentClosure.alignedRuntime :=
  learnedConstitutiveAlignmentClosure.forgettingConsumesAlignedRuntime

theorem learned_joint_closure_local_reuse_reaches_target :
    learnedConstitutiveAlignmentClosure.localReuse.observations =
      learnedPreCertificateGraph.targetObservations :=
  learnedConstitutiveAlignmentClosure.localReuse.targetExact

theorem learned_joint_closure_uses_frozen_learning_inputs :
    learnedConstitutiveAlignmentClosure.learningData =
        independentLearningDataSha256 ∧
      learnedConstitutiveAlignmentClosure.learningGenerator =
        independentLearningGeneratorSha256 :=
  ⟨learnedConstitutiveAlignmentClosure.learningDataExact,
    learnedConstitutiveAlignmentClosure.learningGeneratorExact⟩

theorem learned_joint_closure_consumes_both_executed_productions :
    learnedConstitutiveAlignmentClosure.firstProduction =
        learnedReferenceTransitionProduction ∧
      learnedConstitutiveAlignmentClosure.secondProduction =
        learnedExtendedReferenceTransitionProduction :=
  ⟨learnedConstitutiveAlignmentClosure.firstProductionExact,
    learnedConstitutiveAlignmentClosure.secondProductionExact⟩

theorem learned_joint_closure_transport_is_source_licensed :
    licensedStructuralEntries
        learnedConstitutiveAlignmentClosure.localReuseLicenses =
      learnedTransportedStructuralFragments :=
  learnedConstitutiveAlignmentClosure.localReusePayloadFromLicenses

theorem learned_joint_closure_installs_the_assembled_certificate :
    HEq learnedConstitutiveAlignmentClosure.alignedRuntime.current.certificate
      (assembleStateConstitution learnedAlignedTargetAnalysis.fragments) :=
  learnedConstitutiveAlignmentClosure.localReuseInstalled

theorem learned_joint_closure_installs_produced_successors :
    learnedConstitutiveAlignmentClosure.firstProduction.targetState =
        learnedConstitutiveAlignmentClosure.alignedRuntime.current.state ∧
      learnedConstitutiveAlignmentClosure.secondProduction.targetState =
        learnedConstitutiveAlignmentClosure.extendedRuntime.current.state :=
  ⟨learnedConstitutiveAlignmentClosure.firstProducedStateInstalled,
    learnedConstitutiveAlignmentClosure.secondProducedStateInstalled⟩

theorem learned_joint_closure_candidates_share_intent_and_current_domain :
    learnedConstitutiveAlignmentClosure.divergence.alignedCandidate.candidate.intent =
        learnedConstitutiveAlignmentClosure.divergence.bypassCandidate.candidate.intent ∧
      learnedRuntimeCurrentTable
          learnedConstitutiveAlignmentClosure.divergence.alignedCandidate =
        learnedRuntimeCurrentTable
          learnedConstitutiveAlignmentClosure.divergence.bypassCandidate :=
  ⟨learnedConstitutiveAlignmentClosure.divergence.sameAdmittedIntent,
    learnedConstitutiveAlignmentClosure.divergence.currentTableExact⟩

theorem learned_joint_closure_discriminating_continuation_is_nonempty :
    learnedConstitutiveAlignmentClosure.divergence.requests ≠ [] :=
  learnedConstitutiveAlignmentClosure.divergence.requestsNonempty

theorem learned_joint_closure_rejects_bypass_before_installation :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
        .ok next) :=
  learnedConstitutiveAlignmentClosure.bypassHasNoInstalledSuccessor

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_source_is_installed_successor
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_source_is_l3_produced_successor
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_runtime_future_source_is_l3_produced_source
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_extended_runtime_future_source_is_l3_produced_source
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_has_positive_admission
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_has_positive_refusal
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_immediate_read_does_not_separate
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_empty_outcome_does_not_separate
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_nonempty_continuation_separates
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_separator_is_nonempty
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_universal_exact_separation
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_positive_realization_is_exact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_renamed_identity_is_installed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_histories_are_actually_distinct
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_installed_identities_are_distinct
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_pre_action_identities_are_distinct
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_pre_action_identity_is_installed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_consumes_installed_state
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_history_is_admitted
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_action_is_indexed_by_installed_state
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_effect_is_produced_from_exact_action
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_outputs_are_equal
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_preserves_all_finite_futures
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_has_no_joint_recoverer
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_continuation_is_authorized
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_output_is_runtime_reduced_memory
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_refused_future_remains_refused
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_contract_change_is_justified
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_contract_change_is_authorized
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_persistent_intent_is_transported
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_authorization_is_rechecked
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_historical_return_is_refused
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_rc4_certificate_uses_nonempty_separator
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_has_the_exact_dependent_lineage
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_lineage_is_canonical
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_installs_both_successors
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_future_comes_from_installed_runtime
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_forgetting_consumes_aligned_runtime
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_local_reuse_reaches_target
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_uses_frozen_learning_inputs
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_consumes_both_executed_productions
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_transport_is_source_licensed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_installs_the_assembled_certificate
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_installs_produced_successors
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_candidates_share_intent_and_current_domain
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_discriminating_continuation_is_nonempty
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_rejects_bypass_before_installation
/- AXIOM_AUDIT_END -/
