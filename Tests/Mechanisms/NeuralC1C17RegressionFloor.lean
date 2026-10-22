import RelationalPerimeter.Agents.Neural.CertifiedRuntimeAccessibility
import RelationalPerimeter.Agents.Neural.CoveredFutureRealization
import RelationalPerimeter.Agents.Neural.FiniteCounterfactualDivergence
import RelationalPerimeter.Agents.Neural.IncrementalReferenceEquivalence
import RelationalPerimeter.Agents.Neural.LocalCertificateReuse
import RelationalPerimeter.Agents.Neural.SerializedNativeSystem
import RelationalPerimeter.Agents.Neural.StableNodeCorrespondence

/-! Named regression floor for the already established C1--C17 results.

This module does not claim that the terminal target has been reached.  It
keeps the established positive witnesses addressable by stable names so that
subsequent work cannot silently weaken them.  The byte-for-byte learned
artifact reproduction and exact negative diagnostics are executable gates and
are therefore guarded by `scripts/check-neural-c1-c17-regression-floor.py`.
-/
namespace Tests.Mechanisms.NeuralC1C17RegressionFloor
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent

theorem complete_serialized_artifact_decoding_is_preserved :
    decodeArtifact PublicInitialOperationalContract
      publicSerializedRequirementNetwork =
        .ok publicDecodedRequirementArtifact :=
  publicSerializedRequirementNetwork_decodes

theorem every_covered_finite_future_is_preserved
    (source : ReconfiguredExecutionState publicRequirementFamily)
    (requests : List (ULift.{3} Agent.Request)) :
    PublicReconfiguredOperationalContract.futureContract.outcome source
        requests =
      reconfiguredOperationalMemoryFutureContract.outcome source.memory
        requests :=
  publicOperationalContract_preserves_every_finite_future source requests

theorem requirement_identity_survives_reindexing :
    (StableNodeId.receivedInput (naming := publicInitialStableNaming)
        publicRequirementPort).key =
      (StableNodeId.receivedInput (naming := publicReconfiguredStableNaming)
        publicReconfigurationRequirementPort).key :=
  publicStableNodeCorrespondence_preserves_requirement_key

theorem requirement_is_outside_the_computed_affected_cone :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode (.receivedInput 1)) = false :=
  publicRequirementNode_is_outsideAffectedCone

theorem authorization_is_inside_the_computed_affected_cone :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode (.receivedInput 2)) = true :=
  publicAuthorizationNode_is_affected

theorem proposal_is_inside_the_computed_affected_cone :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode (.neuron 0)) = true :=
  publicProposalNeuron_is_affected

theorem action_is_inside_the_computed_affected_cone :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      .action = true :=
  publicAction_is_affected_downstream

theorem unaffected_requirement_payload_is_really_transported :
    publicReusedRequirementFragment.payload =
      publicInitialRequirementFragment.payload :=
  publicReusedRequirementFragment_payload_exact

theorem transported_requirement_payload_is_observed_in_the_target :
    lookupStructuralObservation (.receivedInput 1)
        (structuralObservationSnapshot
          publicReferenceUpdatedStateCertificate) =
      some publicReusedRequirementFragment.payload :=
  publicReusedRequirementFragment_observed_in_target

theorem incremental_and_complete_reference_verdicts_remain_equal :
    eraseIncrementalCheckResult
        (checkIncrementalUpdate publicIncrementalNeuralUpdate) =
      checkReferenceUpdate publicFullReferenceNeuralUpdate :=
  publicIncrementalAndReferenceChecks_exact

theorem closed_runtime_installs_exactly_the_checked_successor :
    submitUpdate publicInitialCertifiedRuntime
        (.reconfigure publicIncrementalNeuralUpdate) =
      .ok publicUpdatedCertifiedRuntime :=
  submitUpdate_public_result_exact

theorem rejected_runtime_update_cannot_be_installed :
    Not (Exists fun next =>
      submitUpdate publicInitialCertifiedRuntime
          (.reconfigure publicIncorrectIncrementalUpdate) =
        .ok next) :=
  submitUpdate_rejected_cannot_install publicInitialCertifiedRuntime
    (.reconfigure publicIncorrectIncrementalUpdate)
    .unexpectedSuccessorArtifact rfl

theorem aligned_and_bypass_updates_remain_currently_equivalent :
    CurrentBehaviorEquivalentAfterUpdate checkedIndependentLearnedInitial
      alignedUpdate bypassUpdate :=
  candidateCurrentBehaviorEquivalent

def finite_counterfactual_divergence_remains_constructed :
    FutureViolationWitness checkedIndependentLearnedInitial
      alignedUpdate bypassUpdate :=
  alignedBypassFutureViolation

def latent_bypass_detection_remains_constructed :
    ConstitutiveLatentBypassCertificate :=
  constitutiveChecker_detectsLatentBypass

end Tests.Mechanisms.NeuralC1C17RegressionFloor
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.complete_serialized_artifact_decoding_is_preserved
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.every_covered_finite_future_is_preserved
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.requirement_identity_survives_reindexing
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.requirement_is_outside_the_computed_affected_cone
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.authorization_is_inside_the_computed_affected_cone
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.proposal_is_inside_the_computed_affected_cone
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.action_is_inside_the_computed_affected_cone
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.unaffected_requirement_payload_is_really_transported
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.transported_requirement_payload_is_observed_in_the_target
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.incremental_and_complete_reference_verdicts_remain_equal
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.closed_runtime_installs_exactly_the_checked_successor
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.rejected_runtime_update_cannot_be_installed
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.aligned_and_bypass_updates_remain_currently_equivalent
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.finite_counterfactual_divergence_remains_constructed
#print axioms Tests.Mechanisms.NeuralC1C17RegressionFloor.latent_bypass_detection_remains_constructed
/- AXIOM_AUDIT_END -/
