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

def learned_post_forgetting_continuation_is_authorized :
    LearnedPostForgettingPermission
      learnedAlignedExecutedFutureForgetting.output
      (.continueFuture learnedAdmittedFutureRequest) :=
  learnedPostForgettingContinuationPermission

theorem learned_post_forgetting_recovery_is_refused :
    LearnedPostForgettingPermission
        learnedAlignedExecutedFutureForgetting.output
        .recoverHistoricalIdentity -> False :=
  learnedPostForgettingRecovery_refused

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
    submitUpdate learnedAlignedCertifiedRuntime learnedExtendedRuntimeUpdate =
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

theorem learned_joint_closure_rejects_bypass_before_installation :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime learnedBypassRuntimeUpdate =
        .ok next) :=
  learnedConstitutiveAlignmentClosure.bypassHasNoInstalledSuccessor

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_future_source_is_installed_successor
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
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_consumes_installed_state
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_history_is_admitted
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_action_is_indexed_by_installed_state
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_outputs_are_equal
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_preserves_all_finite_futures
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_forgetting_has_no_joint_recoverer
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_continuation_is_authorized
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_post_forgetting_recovery_is_refused
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_rc4_certificate_uses_nonempty_separator
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_has_the_exact_dependent_lineage
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_lineage_is_canonical
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_installs_both_successors
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_future_comes_from_installed_runtime
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_forgetting_consumes_aligned_runtime
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_local_reuse_reaches_target
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_joint_closure_rejects_bypass_before_installation
/- AXIOM_AUDIT_END -/
