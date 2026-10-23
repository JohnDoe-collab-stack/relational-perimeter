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

theorem post_forgetting_continuation_incremental_complete :
    LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingAdmittedContinuationRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest) :=
  learnedPostForgettingRequiredRelativeCompleteness.1

theorem post_forgetting_contract_change_full_complete :
    LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingExtendedChangeRequest) :=
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

end Tests.Mechanisms.NeuralL5AutonomousCheckers
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_incremental_accepts
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_full_recheck_accepts
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_checkers_agree
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_checkers_install_same_successor
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.successive_checkers_install_same_certificate
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_continuation_incremental_complete
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_contract_change_full_complete
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_refused_incrementally
#print axioms Tests.Mechanisms.NeuralL5AutonomousCheckers.post_forgetting_refused_by_full_recheck
/- AXIOM_AUDIT_END -/
