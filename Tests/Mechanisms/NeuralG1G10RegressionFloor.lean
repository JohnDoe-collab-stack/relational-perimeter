import RelationalPerimeter.Agents.Neural.AutonomousCheckerClosure

/-!
# Named regression floor for G1--G10

This file keeps the constructive evidence for each mandatory guarantee
addressable by a stable name.  It does not replace the dependent objects by a
propositional checklist: every declaration below returns the original indexed
witness or restates the original generic theorem at its full quantification.
-/
namespace Tests.Mechanisms.NeuralG1G10RegressionFloor
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism
open ContinuationSignatures

/-! ## G1 -- authorized contract evolution -/

theorem g1_authorized_update_is_installed :
    submitUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate =
      .ok learnedAlignedCertifiedRuntime :=
  learnedConstitutiveAlignmentClosure.alignedInstalled

def g1_every_installed_step_preserves_contracts :
    EveryCheckedStepPreservesContracts
      learnedConstitutiveAlignmentClosure.lineage.trace :=
  learnedConstitutiveAlignmentClosure.lineagePreservesContracts

/-! ## G2 -- authenticity of the executed chain -/

def g2_executed_chain_is_constructed :
    LearnedArtifactExecutionLineage :=
  learnedConstitutiveAlignmentClosure.lineage

theorem g2_internal_transformation_is_nonidentity :
    learnedAlignedComposedSourceTransformation 0 = 1 :=
  learnedConstitutiveAlignmentClosure.alignedSourceTransformationNonidentity

theorem g2_extended_internal_transformation_is_nonidentity :
    learnedExtendedComposedSourceTransformation 0 = 1 :=
  learnedConstitutiveAlignmentClosure.extendedSourceTransformationNonidentity

/-! ## G3 -- effective causal dependencies -/

def g3_source_resource_changes_the_reconfiguration :
    CausalRole
      learnedConstitutiveAlignmentClosure.alignedReconfiguration.configuration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput
        learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.sourcePort) :=
  learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.sourceRole

def g3_requirement_resource_changes_the_reconfiguration :
    CausalRole
      learnedConstitutiveAlignmentClosure.alignedReconfiguration.configuration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput
        learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.requirementPort) :=
  learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.requirementRole

def g3_authorization_is_constitutively_consumed :
    CausalRole
      learnedConstitutiveAlignmentClosure.alignedReconfiguration.configuration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput
        learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.authorizationPort) :=
  learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.authorizationRole

theorem g3_source_occurrence_is_the_transformed_prior_proposal :
    (learnedConstitutiveAlignmentClosure.alignedReconfiguration.configuration.targetSystem.encode
        independentLearnedCertifiedInput).read
        learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.sourcePort =
      learnedAlignedReconfigurationBuilder.sourceCode
        (learnedDecodedInitialArtifact.system.proposal
          independentLearnedCertifiedInput) :=
  learnedConstitutiveAlignmentClosure.alignedReconfiguration.transport.sourceExact

def g3_context_resource_changes_the_reconfiguration :
    CausalRole learnedDecodedAlignedArtifact.system
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedContextPort) :=
  learnedConstitutiveAlignmentClosure.alignedCausal.contextRole

/-! ## G4 -- arbitrary finite dependent traces -/

theorem g4_every_finite_executed_program_is_accepted
    {constitution : ConstitutiveMetaContract}
    {checker : DependentIncrementalChecker constitution}
    {sourceContract targetContract : constitution.Contract}
    {source : CheckedAgent constitution sourceContract}
    {final : CheckedAgent constitution targetContract}
    {program : CheckedUpdateProgram checker source}
    (executed : ExecutedCheckedUpdateProgram source program final) :
    checkUpdates checker source program = .ok executed.result :=
  checkUpdates_complete executed

/-! ## G5 -- refusal before effect and closed accessibility -/

def g5_installed_runtime_is_accessible :
    CertifiedRuntimeAccessibility
      learnedConstitutiveAlignmentClosure.extendedRuntime :=
  learnedConstitutiveAlignmentClosure.extendedAccessible

theorem g5_rejected_update_has_no_installed_successor :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime
        learnedBypassRuntimeUpdate = .ok next) :=
  learnedConstitutiveAlignmentClosure.bypassHasNoInstalledSuccessor

/-! ## G6 -- executed forgetting and exact futures -/

theorem g6_historical_inputs_are_distinct
    : learnedAlignedHistoricalForgettingInput ≠
      learnedRenamedHistoricalForgettingInput :=
  learnedConstitutiveAlignmentClosure.forgetting.historiesDistinct

theorem g6_outputs_converge_only_after_execution
    : learnedAlignedExecutedFutureForgetting.output =
      learnedRenamedExecutedFutureForgetting.output :=
  learnedConstitutiveAlignmentClosure.forgetting.forgottenOutputsEqual

theorem g6_forgotten_origin_is_not_recoverable
    (recover : IndependentLearnedOperationalMemory ->
      LearnedHistoricalStableOrigin)
    (recoversLeft :
      recover learnedAlignedExecutedFutureForgetting.output =
        learnedAlignedHistoricalForgettingInput.origin)
    (recoversRight :
      recover learnedRenamedExecutedFutureForgetting.output =
        learnedRenamedHistoricalForgettingInput.origin) :
    False :=
  learnedConstitutiveAlignmentClosure.forgetting.originNotRecoverable recover
    recoversLeft recoversRight

theorem g6_every_covered_finite_future_is_preserved
    (origin : LearnedHistoricalStableOrigin)
    (requests : List IndependentLearnedFutureInput) :
    independentLearnedFutureContract.outcome
        (LearnedAlignedOperationalContract.futureSourceOfState
          learnedAlignedEffect.targetState) requests =
      independentLearnedReducedFutureContract.outcome
        (executeHistoricalForgetting learnedHistoricalFutureForgettingProgram
          { origin := origin }).output requests :=
  learnedConstitutiveAlignmentClosure.forgetting.everyFuturePreserved
    origin requests

/-! ## G7 -- executable, non-circular checking -/

theorem g7_public_success_iff_autonomous_local_conditions
    (update : LearnedSerializedConstitutiveUpdate) :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine update ↔
      GenericIncrementalUpdateLocalConditions
        learnedIncrementalCheckerEngine update :=
  learnedConstitutiveAlignmentClosure.checkerComplete update

theorem g7_learned_success_iff_autonomous_local_conditions :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine
        learnedAlignedSerializedUpdate ↔
      LearnedFullUpdateAccepted learnedAlignedSerializedUpdate :=
  learnedAlignedIncrementalAndFullAcceptance_equivalent

theorem g7_successive_incremental_and_full_recheck_agree :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
        learnedExtendedSerializedUpdate ↔
      FullRecheckAccepted learnedSuccessiveFullRecheckEngine
        learnedExtendedSerializedUpdate :=
  learnedSuccessiveIncrementalAndFullAcceptance_equivalent

theorem g7_successive_incremental_and_full_successor_exact :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next :=
  learnedSuccessiveIncrementalAndFullSuccessor_exact

theorem g7_post_forgetting_continuation_is_relatively_complete :
    LearnedPostForgettingIncrementalAccepted
        learnedPostForgettingAdmittedContinuationRequest ↔
      Nonempty (LearnedPostForgettingLocalConditionData
        learnedPostForgettingAdmittedContinuationRequest) :=
  learnedPostForgettingRequiredRelativeCompleteness.1

theorem g7_post_forgetting_contract_change_is_relatively_complete :
    LearnedPostForgettingFullRecheckAccepted
        learnedPostForgettingExtendedChangeRequest ↔
      LearnedPostForgettingFullLocalConditions
        learnedPostForgettingExtendedChangeRequest :=
  learnedPostForgettingRequiredRelativeCompleteness.2.2.2

theorem g7_post_forgetting_contract_change_is_effectfully_installed :
    submitUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok learnedPostForgettingExtendedRuntime :=
  submitUpdate_postForgettingExtended_exact

theorem g7_post_forgetting_contract_change_consumes_transport_and_recheck :
    learnedClosedPostForgettingExtendedChange.transportedIntent =
        learnedPostForgettingExtendedJustification.transportedPersistent
          .admittedIntent ∧
      learnedClosedPostForgettingExtendedChange.recheckedAuthorization =
        learnedPostForgettingExtendedJustification.rechecked
          .authorizationConsumption :=
  ⟨learnedClosedPostForgettingExtendedChange.resources.transportedIntentExact,
    learnedClosedPostForgettingExtendedChange.resources.recheckedAuthorizationExact⟩

theorem g7_post_forgetting_contract_change_consumes_executed_reduction :
    learnedPostForgettingExtendedJustification.reducedMemory =
      learnedAlignedExecutedFutureForgetting.output :=
  learnedPostForgettingOperationalClosure.reducedMemoryProduced

theorem g7_post_forgetting_resource_phase_consumes_reduced_outcome :
    learnedClosedPostForgettingExtendedChange.resources.receipt.outcome =
      independentLearnedReducedFutureContract.outcome
        learnedPostForgettingExtendedJustification.reducedMemory
        [learnedAdmittedFutureRequest] :=
  learnedPostForgettingOperationalClosure.resourcePhaseConsumesReducedMemory

theorem g7_post_forgetting_receipt_is_installed_continuation_output :
    learnedPostForgettingOperationalClosure.receipt.outcome =
        learnedPostForgettingOperationalClosure.continuation.execution.outcome ∧
      learnedPostForgettingOperationalClosure.receipt.nextMemory =
        learnedPostForgettingOperationalClosure.continuation.execution.nextMemory :=
  ⟨learnedPostForgettingOperationalClosure.receiptOutcomeIsContinuationOutput,
    learnedPostForgettingOperationalClosure.receiptNextMemoryIsContinuationOutput⟩

theorem g7_post_forgetting_target_action_consumes_receipt :
    learnedClosedPostForgettingExtendedChange.resources.targetAnalysis.recomputedCertificateFragments.proposalAction.witness.request =
      publicAgentActionChannel.command
        learnedClosedPostForgettingExtendedChange.resources.receipt.producedProposal :=
  learnedPostForgettingOperationalClosure.targetActionConsumesReceipt

theorem g7_post_forgetting_contract_change_resources_feed_installed_certificate :
    LearnedProposalPreservation.admittedIntent
        (LearnedActionWitness.preservation
          (ProposalActionCertificateFragment.witness
            learnedClosedPostForgettingExtendedChange.resources.targetAnalysis.recomputedCertificateFragments.proposalAction)) =
        learnedClosedPostForgettingExtendedChange.resources.transportedIntent.down ∧
      learnedClosedPostForgettingExtendedChange.resources.targetAnalysis.recomputedCertificateFragments.authorization.witness =
        learnedClosedPostForgettingExtendedChange.resources.authorizationAtTarget :=
  ⟨learnedPostForgettingOperationalClosure.targetConsumesTransportedIntent,
    learnedPostForgettingOperationalClosure.targetConsumesRecheckedAuthorization⟩

theorem g7_post_forgetting_contract_change_matches_full_recheck :
    HEq learnedClosedPostForgettingExtendedChange.checked.next
      learnedSuccessiveFullRecheckSuccess.checked.next :=
  learnedPostForgettingOperationalClosure.fullRecheckSuccessorExact

theorem g7_post_forgetting_contract_change_shares_action_with_effect :
    learnedClosedPostForgettingExtendedChange.resources.targetAnalysis.recomputedCertificateFragments.effect.witness.action =
      learnedClosedPostForgettingExtendedChange.resources.targetAnalysis.recomputedCertificateFragments.proposalAction.witness :=
  learnedPostForgettingOperationalClosure.targetSharesActionWithEffect

theorem g7_post_forgetting_bad_change_has_no_successor :
    Not (Exists fun next =>
      submitUpdate learnedPostForgettingInitialRuntime
        (LearnedPostForgettingRuntimeUpdate.changeContract
          learnedPostForgettingExecutionReceipt
          learnedAlignedSerializedUpdate) = .ok next) :=
  learnedPostForgettingBadChange_rejected_without_successor

/-! ## G8 -- exact local reuse and independent full recheck -/

theorem g8_unaffected_fragment_is_transported :
    learnedConstitutiveAlignmentClosure.localReuse.observations =
      learnedPreCertificateGraph.targetObservations :=
  learnedConstitutiveAlignmentClosure.localReuse.targetExact

theorem g8_incremental_and_full_recheck_are_equal :
    learnedAlignedGenericIncrementalSuccess.checked.next =
      learnedAlignedFullRecheckSuccess.checked.next :=
  learnedConstitutiveAlignmentClosure.incrementalFullSuccessorExact

/-! ## G9 -- substantive positive realizations -/

theorem g9_independent_learned_artifact_is_decodable :
    independentLearnedInitialNetworkAccepted = true :=
  independentLearnedInitialNetwork_decodes

theorem g9_positive_continuation_has_two_executed_steps :
    HEq learnedConstitutiveAlignmentClosure.lineage.trace
      learnedTwoStepCheckedTrace := by
  exact HEq.rfl

/-! ## G10 -- latent bypass distinguished by the same closed API -/

def g10_latent_bypass_is_distinguished :
    LearnedOperationalFutureDivergenceCertificate :=
  learnedConstitutiveAlignmentClosure.divergence

end Tests.Mechanisms.NeuralG1G10RegressionFloor
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g1_authorized_update_is_installed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g1_every_installed_step_preserves_contracts
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g2_executed_chain_is_constructed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g2_internal_transformation_is_nonidentity
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g2_extended_internal_transformation_is_nonidentity
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_source_resource_changes_the_reconfiguration
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_requirement_resource_changes_the_reconfiguration
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_authorization_is_constitutively_consumed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_source_occurrence_is_the_transformed_prior_proposal
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_context_resource_changes_the_reconfiguration
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g4_every_finite_executed_program_is_accepted
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g5_installed_runtime_is_accessible
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g5_rejected_update_has_no_installed_successor
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_historical_inputs_are_distinct
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_outputs_converge_only_after_execution
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_forgotten_origin_is_not_recoverable
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_every_covered_finite_future_is_preserved
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_public_success_iff_autonomous_local_conditions
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_learned_success_iff_autonomous_local_conditions
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_successive_incremental_and_full_recheck_agree
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_successive_incremental_and_full_successor_exact
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_continuation_is_relatively_complete
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_is_relatively_complete
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_is_effectfully_installed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_consumes_transport_and_recheck
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_consumes_executed_reduction
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_resource_phase_consumes_reduced_outcome
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_receipt_is_installed_continuation_output
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_target_action_consumes_receipt
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_resources_feed_installed_certificate
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_matches_full_recheck
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_contract_change_shares_action_with_effect
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_post_forgetting_bad_change_has_no_successor
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g8_unaffected_fragment_is_transported
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g8_incremental_and_full_recheck_are_equal
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g9_independent_learned_artifact_is_decodable
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g9_positive_continuation_has_two_executed_steps
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g10_latent_bypass_is_distinguished
/- AXIOM_AUDIT_END -/
