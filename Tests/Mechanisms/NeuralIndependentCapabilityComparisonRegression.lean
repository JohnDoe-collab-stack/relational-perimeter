import RelationalPerimeter.Agents.Neural.IndependentCapabilityProbeControls

namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    independentCompleteComparisonBundle.referenceCombination.observation =
      computeIndependentReferenceObservation
        independentCompleteComparisonBundle.material :=
  independentCompleteComparisonBundle.referenceCombination.observationExact

example :
    independentCompleteComparisonBundle.referenceCombination.observation.alignedDecision =
      IndependentReferenceDecision.allow :=
  independentCompleteComparisonBundle.referenceCombination.alignedDecisionExact

example :
    independentCompleteComparisonBundle.referenceCombination.observation.bypassDecision =
      IndependentReferenceDecision.refuse :=
  independentCompleteComparisonBundle.referenceCombination.bypassDecisionExact

example :
    observeRuntimeSubmission learnedInitialCertifiedRuntime
      learnedAlignedRuntimeUpdate = .installed := by
  rfl

example :
    observeRuntimeSubmission learnedInitialCertifiedRuntime
      learnedBypassRuntimeUpdate = .rejected := by
  rfl

example :
    observeGenericIncremental learnedAlignedSerializedUpdate = .accepted := by
  rfl

example :
    observeGenericIncremental learnedBypassSerializedUpdate = .rejected := by
  rfl

example :
    observeLearnedP2Path decodeIndependentLearnedProposal = .accepted :=
  learnedP2CanonicalPathAccepted

example : learnedP2AdmissibleDecoder ≠ decodeIndependentLearnedProposal :=
  learnedP2AdmissibleDecoderChanged

example :
    observeLearnedP2Path learnedP2AdmissibleDecoder = .accepted :=
  learnedP2AdmissiblePathAccepted

example :
    recheckLearnedP2Path learnedP2AdmissibleDecoder = .accepted :=
  learnedP2AdmissibleRecheckAccepted

example :
    learnedP2ModifiedProposal ≠ learnedP2CanonicalProposal :=
  learnedP2ModifiedProposalDifferent

example :
    learnedP2ModifiedRequest ≠ learnedP2CanonicalRequest :=
  learnedP2ModifiedRequestDifferent

example :
    learnedP2CanonicalProposal =
      learnedAlignedState.system.proposal learnedAlignedState.input :=
  learnedP2CanonicalProposal_is_executed

example :
    learnedP2CanonicalRequest = learnedAlignedAction.request :=
  learnedP2CanonicalRequest_is_executed

example :
    observeLearnedP2Path learnedP2ModifiedDecoder = .rejected :=
  learnedP2ModifiedPathRejected

example :
    recheckLearnedP2Path learnedP2ModifiedDecoder = .rejected :=
  learnedP2ModifiedRecheckRejected

example : observeLearnedP2Incremental .canonical = .accepted :=
  learnedP2CanonicalIncrementalPathAccepted

example : observeLearnedP2Incremental .admissible = .accepted :=
  learnedP2AdmissibleIncrementalPathAccepted

example : observeLearnedP2Incremental .forbidden = .rejected :=
  learnedP2ForbiddenIncrementalPathRejected

example : observeLearnedP2FullRecheck .canonical = .accepted :=
  learnedP2CanonicalFullRecheckPathAccepted

example : observeLearnedP2FullRecheck .admissible = .accepted :=
  learnedP2AdmissibleFullRecheckPathAccepted

example : observeLearnedP2FullRecheck .forbidden = .rejected :=
  learnedP2ForbiddenFullRecheckPathRejected

example :
    learnedP2AdmissibleIncrementalSuccess.checked.next =
      learnedP2AdmissibleFullRecheckSuccess.checked.next :=
  learnedP2AdmissibleIncrementalAndFullSuccessor_exact

example :
    learnedP2AdmissibleIncrementalSuccess.checked.next.certificate =
      learnedP2AdmissibleFullRecheckSuccess.checked.next.certificate :=
  learnedP2AdmissibleIncrementalAndFullCertificate_exact

example :
    (learnedP2AdmissibleIncrementalSuccess.checked.next.certificate
        ).proposalActionWitness = learnedP2AdmissibleFragment.action :=
  learnedP2AdmissibleIncrementalAction_exact

example :
    (learnedP2AdmissibleFullRecheckSuccess.checked.next.certificate
        ).proposalActionWitness = learnedP2AdmissibleFragment.action :=
  learnedP2AdmissibleFullRecheckAction_exact

example :
    (learnedP2AdmissibleIncrementalSuccess.checked.next.certificate
        ).effectWitness.action = learnedP2AdmissibleFragment.action :=
  learnedP2AdmissibleIncrementalEffect_consumes_action

example :
    (learnedP2AdmissibleFullRecheckSuccess.checked.next.certificate
        ).effectWitness.action = learnedP2AdmissibleFragment.action :=
  learnedP2AdmissibleFullRecheckEffect_consumes_action

example :
    learnedP4IncorrectForgetting
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial) =
      learnedP4IncorrectForgetting
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial) :=
  learnedP4IncorrectForgettingCollapsesSeparatedSources

example :
    independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedAlignedCandidateAtInitial)
        learnedAlignedBypassFutureSeparator.requests ≠
      independentLearnedFutureContract.outcome
        (learnedCandidateFutureSource learnedBypassCandidateAtInitial)
        learnedAlignedBypassFutureSeparator.requests :=
  learnedP4SeparatorRevealsRequiredDistinction

example : runLearnedP6SuccessiveComparison.incrementalDecision = .accepted :=
  runLearnedP6SuccessiveComparison.incrementalDecisionExact

example : runLearnedP6SuccessiveComparison.fullRecheckDecision = .accepted :=
  runLearnedP6SuccessiveComparison.fullRecheckDecisionExact

example :
    learnedSuccessiveIncrementalSuccess.checked.next =
      learnedSuccessiveFullRecheckSuccess.checked.next :=
  runLearnedP6SuccessiveComparison.acceptedSuccessorExact

example :
    learnedP2ChangedConsumerInputUpdate.targetNetwork =
      learnedAlignedSerializedUpdate.targetNetwork :=
  learnedP2NetworkHeldFixed

example :
    learnedP2ChangedConsumerInputUpdate.nextInput ≠
      learnedAlignedSerializedUpdate.nextInput :=
  learnedP2ConsumerInputChanged

example :
    learnedP3RejectedContractTransitionUpdate.targetNetwork =
      learnedAlignedSerializedUpdate.targetNetwork :=
  learnedP3ArtifactHeldFixed.1

example :
    learnedP3RejectedContractTransitionUpdate.transition ≠
      learnedAlignedSerializedUpdate.transition :=
  learnedP3TransitionChanged

example :
    observeGenericIncremental learnedP3RejectedContractTransitionUpdate =
      .rejected :=
  learnedP3ChangedIncrementalRejected

example :
    observeIndependentFullRecheck learnedP3RejectedContractTransitionUpdate =
      .rejected :=
  learnedP3ChangedFullRecheckRejected

example :
    submitUpdate learnedPostForgettingInitialRuntime
        learnedPostForgettingExtendedRuntimeUpdate =
      .ok learnedPostForgettingOperationalClosure.installedRuntime :=
  learnedPostForgettingOperationalClosure.installedExact

example :
    Not (Exists fun next =>
      submitUpdate learnedPostForgettingInitialRuntime
        (LearnedPostForgettingRuntimeUpdate.changeContract
          learnedPostForgettingExecutionReceipt learnedAlignedSerializedUpdate) =
        .ok next) :=
  learnedPostForgettingOperationalClosure.refusedContractChangeHasNoSuccessor

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.computeIndependentReferenceObservation
#print axioms ConstitutiveSearch.NeuralAgent.runIndependentReferenceCombination
#print axioms ConstitutiveSearch.NeuralAgent.observeRuntimeSubmission
#print axioms ConstitutiveSearch.NeuralAgent.observeGenericIncremental
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedP2Path
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleDecoderChanged
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissiblePathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleRecheckAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedProposalDifferent
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedRequestDifferent
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalProposal_is_executed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalRequest_is_executed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedPathRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ModifiedRecheckRejected
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP2Incremental
#print axioms ConstitutiveSearch.NeuralAgent.observeLearnedP2FullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalAction_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckAction_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalEffect_consumes_action
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckEffect_consumes_action
#print axioms ConstitutiveSearch.NeuralAgent.learnedP4IncorrectForgettingCannotBeExact
#print axioms ConstitutiveSearch.NeuralAgent.runLearnedP6SuccessiveComparison
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2NetworkHeldFixed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3ArtifactHeldFixed
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3ChangedIncrementalRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3ChangedFullRecheckRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingOperationalClosure
#print axioms ConstitutiveSearch.NeuralAgent.independentCompleteComparisonBundle
#print axioms ConstitutiveSearch.NeuralAgent.runFixedNetworkInterventionalAdapter
#print axioms ConstitutiveSearch.NeuralAgent.FixedNetworkInterventionalAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runPreExecutionActionShieldAdapter
#print axioms ConstitutiveSearch.NeuralAgent.PreExecutionActionShieldAdapterOutput
#print axioms ConstitutiveSearch.NeuralAgent.runDeploymentChainPropagationAdapter
#print axioms ConstitutiveSearch.NeuralAgent.runRelationalExecutionComparison
#print axioms ConstitutiveSearch.NeuralAgent.RelationalExecutionComparisonOutput
#print axioms ConstitutiveSearch.NeuralAgent.IndependentReferenceCombinationOutput
#print axioms ConstitutiveSearch.NeuralAgent.runIndependentFullRecheckComparison
#print axioms ConstitutiveSearch.NeuralAgent.recheckLearnedP2Path
#print axioms ConstitutiveSearch.NeuralAgent.checkLearnedP2AdmissibleFragment_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalIncrementalPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleIncrementalPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ForbiddenIncrementalPathRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2CanonicalFullRecheckPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2AdmissibleFullRecheckPathAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedP2ForbiddenFullRecheckPathRejected
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3TransitionChanged
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3AllowedIncrementalAccepted
#print axioms ConstitutiveSearch.NeuralAgent.observeIndependentFullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.learnedP3AllowedFullRecheckAccepted
#print axioms ConstitutiveSearch.NeuralAgent.learnedAlignedExecutedFutureForgetting
#print axioms ConstitutiveSearch.NeuralAgent.learnedP4SeparatorRevealsRequiredDistinction
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingBadChange_rejected_without_successor
#print axioms ConstitutiveSearch.NeuralAgent.observePostForgettingIncremental
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedChange_incremental
#print axioms ConstitutiveSearch.NeuralAgent.observePostForgettingFullRecheck
#print axioms ConstitutiveSearch.NeuralAgent.learnedPostForgettingExtendedChange_full
#print axioms ConstitutiveSearch.NeuralAgent.learnedClosedPostForgettingFullRecheck_successor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveInstalledStructuralAssembly_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveTransport_reads_checked_source
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullSuccessor_exact
#print axioms ConstitutiveSearch.NeuralAgent.learnedSuccessiveIncrementalAndFullCertificate_exact
#print axioms ConstitutiveSearch.NeuralAgent.GuaranteedSelfAdaptiveAdapterOutput.everyInstalledStepChecked
#print axioms ConstitutiveSearch.NeuralAgent.GuaranteedSelfAdaptiveAdapterOutput.everyInstalledStepPreservesContracts
#print axioms ConstitutiveSearch.NeuralAgent.IncrementalProofReuseAdapterOutput.learnedReuseExact
#print axioms ConstitutiveSearch.NeuralAgent.DeploymentChainPropagationAdapterOutput.checkedHistory
#print axioms ConstitutiveSearch.NeuralAgent.DeploymentChainPropagationAdapterOutput.preservedContracts
#print axioms ConstitutiveSearch.NeuralAgent.IndependentFullRecheckComparisonOutput.alignedSuccessorMatchesIncremental
#print axioms ConstitutiveSearch.NeuralAgent.IndependentFullRecheckComparisonOutput.acceptedWithoutIncrementalOracle
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutedFutureForgetting_preserves_every_finite_future
#print axioms ConstitutiveSearch.NeuralAgent.learnedExecutedFutureForgetting_origin_not_recoverable
#print axioms ConstitutiveSearch.NeuralAgent.LearnedPostForgettingOperationalClosure.refusedContractChangeHasNoSuccessor
/- AXIOM_AUDIT_END -/
