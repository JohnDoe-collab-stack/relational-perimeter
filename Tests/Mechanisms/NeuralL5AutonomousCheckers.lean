import RelationalPerimeter.Agents.Neural.AutonomousCheckerClosure

/-!
# L5 regression: autonomous incremental and independent complete checkers

The successive checker consumes the serialized aligned-to-extended update.
The complete checker reconstructs the target and reruns the transition without
receiving an incremental verdict or fragment.  After forgetting, continuation
and contract change are decided again from proof-free requests.
-/
namespace Tests.Mechanisms.NeuralL5AutonomousCheckers
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent

theorem successive_incremental_accepts :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
      learnedExtendedSerializedUpdate :=
  learnedSuccessiveIncrementalAccepted

theorem successive_full_recheck_accepts :
    FullRecheckAccepted learnedSuccessiveFullRecheckEngine
      learnedExtendedSerializedUpdate :=
  learnedSuccessiveFullRecheckAccepted

theorem successive_checkers_agree :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate ↔
      FullRecheckAccepted learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate :=
  learnedSuccessiveIncrementalAndFullAcceptance_equivalent

theorem successive_checkers_install_same_successor :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next :=
  learnedSuccessiveIncrementalAndFullSuccessor_exact

theorem successive_checkers_install_same_certificate :
    learnedSuccessiveIncrementalSuccess.checked.next.certificate =
      learnedSuccessiveFullRecheckSuccess.checked.next.certificate :=
  learnedSuccessiveIncrementalAndFullCertificate_exact

theorem successive_runtime_consumes_incremental_assembly :
    learnedExtendedCertifiedRuntime.current.certificate.structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations :=
  learnedExtendedRuntime_certificate_consumes_successiveAssembly

theorem successive_runtime_and_incremental_engine_install_same_successor :
    learnedExtendedDependentResult.checked.next =
      learnedSuccessiveIncrementalSuccess.checked.next := by
  rfl

theorem post_forgetting_continuation_incremental_complete :
    LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingAdmittedContinuationRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest) :=
  learnedPostForgettingRequiredRelativeCompleteness.1

theorem post_forgetting_continuation_installation_complete :
    ExceptAccepted (submitLearnedPostForgettingContinuation
        learnedAdmittedFutureRequest) ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest) :=
  submitLearnedPostForgettingContinuation_complete _

theorem post_forgetting_contract_change_full_complete :
    LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      LearnedPostForgettingFullLocalConditions
        learnedPostForgettingExtendedChangeRequest :=
  learnedPostForgettingRequiredRelativeCompleteness.2.2.2

theorem post_forgetting_refused_incrementally :
    checkLearnedPostForgettingIncremental
        learnedPostForgettingRefusedContinuationRequest =
      .error .futureRefused :=
  learnedPostForgettingRefusedContinuation_rejected_incrementally

theorem post_forgetting_refused_by_full_recheck :
    recheckLearnedPostForgettingCompletely
        learnedPostForgettingRefusedContinuationRequest =
      .error .futureRefused :=
  learnedPostForgettingRefusedContinuation_rejected_by_full_recheck

theorem post_forgetting_continuation_is_installed :
    submitLearnedPostForgettingContinuation learnedAdmittedFutureRequest =
      .ok learnedInstalledPostForgettingContinuation :=
  submitLearnedPostForgettingContinuation_exact

theorem post_forgetting_continuation_consumes_reduced_memory :
    learnedInstalledPostForgettingContinuation.execution.outcome =
      independentLearnedReducedFutureContract.outcome
        learnedAlignedExecutedFutureForgetting.output
        [learnedAdmittedFutureRequest] :=
  learnedInstalledPostForgettingContinuation_consumes_reducedMemory

theorem post_forgetting_refusal_has_no_effectful_result :
    Not (Exists fun installed =>
      submitLearnedPostForgettingContinuation learnedRefusedFutureRequest =
        .ok installed) :=
  learnedPostForgettingRefusal_has_no_continuationResult

theorem post_forgetting_contract_change_is_installed :
    submitUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok learnedPostForgettingExtendedRuntime :=
  submitUpdate_postForgettingExtended_exact

theorem post_forgetting_contract_change_consumes_persistent_transport :
    learnedClosedPostForgettingExtendedChange.transportedIntent =
      learnedPostForgettingExtendedJustification.transportedPersistent
        .admittedIntent :=
  learnedClosedPostForgettingExtendedChange.transportedIntentExact

theorem post_forgetting_contract_change_consumes_authorization_recheck :
    learnedClosedPostForgettingExtendedChange.recheckedAuthorization =
      learnedPostForgettingExtendedJustification.rechecked
        .authorizationConsumption :=
  learnedClosedPostForgettingExtendedChange.recheckedAuthorizationExact

theorem post_forgetting_runtime_checker_consumes_closed_change :
    checkLearnedPostForgettingRuntimeUpdate
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok (dependentCheckedUpdateResult
        learnedClosedPostForgettingExtendedChange.checked) :=
  checkLearnedPostForgettingExtendedRuntimeUpdate_exact

theorem post_forgetting_runtime_starts_from_prior_successor :
    learnedPostForgettingInitialRuntime.current =
      learnedAlignedCertifiedRuntime.current :=
  learnedPostForgettingRuntime_starts_at_installedAlignedState

theorem post_forgetting_runtime_installs_exact_successor :
    learnedPostForgettingExtendedRuntime.current =
      learnedExtendedCertifiedRuntime.current :=
  learnedPostForgettingExtendedRuntime_successor_exact

def post_forgetting_runtime_is_reachable_on_same_lineage :
    CertifiedRuntimeReachable learnedPostForgettingDependentChecker
      LearnedAlignedCurrentAgent learnedPostForgettingExtendedRuntime :=
  learnedPostForgettingExtendedRuntime_reachable

theorem post_forgetting_nonrecoverability_reads_only_reduced_memory
    (recover : IndependentLearnedOperationalMemory ->
      LearnedHistoricalStableOrigin)
    (aligned : recover learnedAlignedExecutedFutureForgetting.output =
      learnedAlignedHistoricalForgettingInput.origin)
    (renamed : recover learnedRenamedExecutedFutureForgetting.output =
      learnedRenamedHistoricalForgettingInput.origin) : False :=
  learnedPostForgettingOperationalClosure.reducedMemoryDoesNotRecoverOrigin
    recover aligned renamed

def post_forgetting_runtime_history_is_checked :
    EveryRuntimeStepSatisfies learnedPostForgettingExtendedRuntime.history :=
  learnedPostForgettingExtendedRuntime_checkedHistory

def post_forgetting_runtime_preserves_contracts :
    EveryRuntimeStepPreservesContracts
      learnedPostForgettingExtendedRuntime.history :=
  learnedPostForgettingExtendedRuntime_preservedContracts

theorem post_forgetting_bad_change_has_no_successor :
    Not (Exists fun next =>
      submitUpdate learnedPostForgettingInitialRuntime
        (LearnedPostForgettingRuntimeUpdate.changeContract
          learnedAlignedSerializedUpdate) = .ok next) :=
  learnedPostForgettingBadChange_rejected_without_successor

def post_forgetting_joint_operational_closure :
    LearnedPostForgettingOperationalClosure :=
  learnedPostForgettingOperationalClosure

end Tests.Mechanisms.NeuralL5AutonomousCheckers
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_incremental_accepts
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_full_recheck_accepts
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_checkers_agree
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_checkers_install_same_successor
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_checkers_install_same_certificate
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_runtime_consumes_incremental_assembly
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_runtime_and_incremental_engine_install_same_successor
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_continuation_incremental_complete
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_continuation_installation_complete
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_contract_change_full_complete
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_refused_incrementally
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_refused_by_full_recheck
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_continuation_is_installed
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_continuation_consumes_reduced_memory
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_refusal_has_no_effectful_result
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_contract_change_is_installed
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_contract_change_consumes_persistent_transport
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_contract_change_consumes_authorization_recheck
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_runtime_checker_consumes_closed_change
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_runtime_starts_from_prior_successor
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_runtime_installs_exact_successor
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_runtime_is_reachable_on_same_lineage
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_nonrecoverability_reads_only_reduced_memory
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_runtime_history_is_checked
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_runtime_preserves_contracts
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_bad_change_has_no_successor
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_joint_operational_closure
/- AXIOM_AUDIT_END -/
