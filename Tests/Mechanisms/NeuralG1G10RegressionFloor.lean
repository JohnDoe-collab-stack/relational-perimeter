import RelationalPerimeter.Agents.Neural.CertifiedRuntimeAccessibility
import RelationalPerimeter.Agents.Neural.ConstitutiveAlignment
import RelationalPerimeter.Agents.Neural.IncrementalReferenceEquivalence
import RelationalPerimeter.Agents.Neural.LearnedContractFutureDivergence

/-!
# Named regression floor for G1--G10

This file keeps the constructive evidence for each mandatory guarantee
addressable by a stable name.  It does not replace the dependent objects by a
propositional checklist: every declaration below returns the original indexed
witness or restates the original generic theorem at its full quantification.
-/
namespace Tests.Mechanisms.NeuralG1G10RegressionFloor
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ContinuationSignatures

/-! ## G1 -- authorized contract evolution -/

theorem g1_authorized_update_is_installed :
    submitUpdate learnedInitialCertifiedRuntime
        learnedAlignedRuntimeUpdate =
      .ok learnedAlignedCertifiedRuntime :=
  submitUpdate_learned_aligned_exact

def g1_every_installed_step_preserves_contracts :
    EveryRuntimeStepPreservesContracts learnedAlignedCertifiedRuntime.history :=
  learnedAlignedRuntime_preservedContracts

/-! ## G2 -- authenticity of the executed chain -/

def g2_executed_chain_is_constructed :
    PublicConstitutiveAlignmentCertificate publicSubstantiveSource
      publicSubstantiveNext [publicSubstantiveContextualNext] :=
  publicSubstantiveAlignment

theorem g2_internal_transformation_is_nonidentity :
    publicRequirementEncoding.code publicSubstantiveSource.requirement
        publicSubstantiveSource.context ≠
      publicRequirementDecoder.terminalRepresentation
        publicSubstantiveSource.requirement publicSubstantiveSource.context :=
  publicSubstantiveInstance.signalTransformationNonidentity

/-! ## G3 -- effective causal dependencies -/

theorem g3_source_resource_changes_the_reconfiguration :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeOne, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ :=
  publicSubstantiveInstance.sourceStateChangesReconfiguration

theorem g3_requirement_resource_changes_the_reconfiguration :
    (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeZero, .direct⟩).targetSystem.outputValues
        ⟨.scopeZero, .direct⟩ ≠
      (publicReconfiguration ⟨.scopeZero, .direct⟩
        ⟨.scopeOne, .direct⟩).targetSystem.outputValues
        ⟨.scopeOne, .direct⟩ :=
  publicSubstantiveInstance.nextRequirementChangesReconfiguration

theorem g3_authorization_is_constitutively_consumed :
    ((publicReconfiguration publicSubstantiveSource
        publicSubstantiveNext).targetSystem.encode
        publicSubstantiveNext).read
        (publicRequiredMechanismTransport publicSubstantiveSource
          publicSubstantiveNext).authorizationPort =
      publicReconfigurationBuilder.authorizationCode
        publicSubstantiveNext
        (publicReconfiguration publicSubstantiveSource
          publicSubstantiveNext).permission :=
  publicSubstantiveInstance.authorizationConsumed

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
    CertifiedRuntimeAccessibility learnedAlignedCertifiedRuntime :=
  learnedAlignedCertifiedRuntime_accessibility

theorem g5_rejected_update_has_no_installed_successor :
    Not (Exists fun next =>
      submitUpdate learnedInitialCertifiedRuntime
        learnedBypassRuntimeUpdate = .ok next) :=
  learned_bypass_rejected_without_successor

/-! ## G6 -- executed forgetting and exact futures -/

theorem g6_historical_inputs_are_distinct
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    publicLeftHistoricalForgettingInput source future ≠
      publicRightHistoricalForgettingInput source future :=
  public_historical_forgetting_inputs_distinct source future

theorem g6_outputs_converge_only_after_execution
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput) :
    (publicLeftExecutedForgetting source future).output =
      (publicRightExecutedForgetting source future).output :=
  public_executed_forgetting_outputs_equal source future

theorem g6_forgotten_origin_is_not_recoverable
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput)
    (recover : Agent.Memory -> PublicHistoricalOrigin)
    (recoversLeft :
      recover (publicLeftExecutedForgetting source future).output =
        (publicLeftHistoricalForgettingInput source future).origin.origin)
    (recoversRight :
      recover (publicRightExecutedForgetting source future).output =
        (publicRightHistoricalForgettingInput source future).origin.origin) :
    False :=
  public_executed_forgetting_origin_not_recoverable source future recover
    recoversLeft recoversRight

theorem g6_every_covered_finite_future_is_preserved
    (source : PublicRequirementInput)
    (future : List PublicRequirementInput)
    (requests : List (ULift.{3} Agent.Request)) :
    (reconfiguredOperationalStateFutureContract
        (family := publicRequirementFamily)).outcome
        (publicReconfiguredInteractionHistory source future).finalState requests =
      reconfiguredOperationalMemoryFutureContract.outcome
        (publicReconfiguredInteractionHistory source future).finalState.memory
        requests :=
  public_terminal_memory_preserves_every_future source future requests

/-! ## G7 -- executable, non-circular checking -/

theorem g7_public_success_iff_autonomous_local_conditions
    (update : IncrementalNeuralUpdate) :
    GenericIncrementalUpdateAccepted publicIncrementalCheckerEngine update ↔
      GenericIncrementalUpdateLocalConditions
        publicIncrementalCheckerEngine update :=
  checkGenericIncrementalUpdate_complete_for_local_conditions
    publicIncrementalCheckerEngine update

theorem g7_learned_success_iff_autonomous_local_conditions
    (update : LearnedSerializedConstitutiveUpdate) :
    GenericIncrementalUpdateAccepted learnedIncrementalCheckerEngine update ↔
      GenericIncrementalUpdateLocalConditions
        learnedIncrementalCheckerEngine update :=
  checkGenericIncrementalUpdate_complete_for_local_conditions
    learnedIncrementalCheckerEngine update

/-! ## G8 -- exact local reuse and independent full recheck -/

theorem g8_unaffected_fragment_is_transported :
    publicReusedRequirementFragment.payload =
      publicInitialRequirementFragment.payload :=
  publicReusedRequirementFragment_payload_exact

theorem g8_incremental_and_full_recheck_are_equal :
    eraseIncrementalCheckResult
        (checkIncrementalUpdate publicIncrementalNeuralUpdate) =
      checkReferenceUpdate publicFullReferenceNeuralUpdate :=
  publicIncrementalAndReferenceChecks_exact

/-! ## G9 -- substantive positive realizations -/

theorem g9_independent_learned_artifact_is_decodable :
    independentLearnedInitialNetworkAccepted = true :=
  independentLearnedInitialNetwork_decodes

theorem g9_positive_continuation_has_two_executed_steps :
    publicSubstantiveAlignment.continuation.requests.length = 2 :=
  publicSubstantiveInstance.continuationHasTwoSteps

/-! ## G10 -- latent bypass distinguished by the same closed API -/

def g10_latent_bypass_is_distinguished :
    ConstitutiveLatentBypassCertificate :=
  constitutiveChecker_detectsLatentBypass

end Tests.Mechanisms.NeuralG1G10RegressionFloor
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g1_authorized_update_is_installed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g1_every_installed_step_preserves_contracts
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g2_executed_chain_is_constructed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g2_internal_transformation_is_nonidentity
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_source_resource_changes_the_reconfiguration
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_requirement_resource_changes_the_reconfiguration
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g3_authorization_is_constitutively_consumed
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g4_every_finite_executed_program_is_accepted
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g5_installed_runtime_is_accessible
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g5_rejected_update_has_no_installed_successor
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_historical_inputs_are_distinct
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_outputs_converge_only_after_execution
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_forgotten_origin_is_not_recoverable
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g6_every_covered_finite_future_is_preserved
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_public_success_iff_autonomous_local_conditions
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g7_learned_success_iff_autonomous_local_conditions
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g8_unaffected_fragment_is_transported
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g8_incremental_and_full_recheck_are_equal
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g9_independent_learned_artifact_is_decodable
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g9_positive_continuation_has_two_executed_steps
#print axioms Tests.Mechanisms.NeuralG1G10RegressionFloor.g10_latent_bypass_is_distinguished
/- AXIOM_AUDIT_END -/
