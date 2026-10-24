import RelationalPerimeter

/-!
# L3 regression: causal production and shared action/effect/successor

These checks expose the learned path through its generic reconfiguration
interfaces and through the exact transition production consumed by the
runtime.  They do not reconstruct either a target certificate or a successor.
-/
namespace Tests.Mechanisms.NeuralL3CausalProduction
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent
open ConstitutiveSearch.NativeMechanism

theorem aligned_reconfiguration_is_produced_target :
    learnedAlignedReconfiguration.targetSystem =
      learnedDecodedAlignedArtifact.system :=
  learnedAlignedReconfiguration_target_exact

theorem extended_reconfiguration_is_produced_target :
    learnedExtendedReconfiguration.targetSystem =
      learnedDecodedExtendedArtifact.system :=
  learnedExtendedReconfiguration_target_exact

theorem aligned_state_configuration_is_exact_producer_output
    (source : ReconfiguredExecutionState independentLearnedRequirementFamily)
    (encoding : LearnedRequirementEncodingWitness source)
    (sourceAction : LearnedActionWitness source) :
    (executeLearnedAlignedReconfigurationFromState source encoding
        sourceAction).certificate.configuration =
      learnedAlignedRawReconfigurationForState source :=
  executeLearnedAlignedReconfigurationFromState_configuration_is_produced
    source encoding sourceAction

theorem aligned_state_successor_uses_exact_producer_target
    (source : ReconfiguredExecutionState independentLearnedRequirementFamily)
    (encoding : LearnedRequirementEncodingWitness source)
    (sourceAction : LearnedActionWitness source) :
    (executeLearnedAlignedReconfigurationFromState source encoding
        sourceAction).targetState.system =
      (learnedAlignedRawReconfigurationForState source).targetSystem :=
  executeLearnedAlignedReconfigurationFromState_target_is_produced
    source encoding sourceAction

theorem extended_state_configuration_is_exact_producer_output
    (source : ReconfiguredExecutionState independentLearnedRequirementFamily)
    (encoding : LearnedRequirementEncodingWitness source)
    (sourceAction : LearnedActionWitness source) :
    (executeLearnedExtendedReconfigurationFromState source encoding
        sourceAction).certificate.configuration =
      learnedExtendedRawReconfigurationForState source :=
  executeLearnedExtendedReconfigurationFromState_configuration_is_produced
    source encoding sourceAction

theorem extended_state_successor_uses_exact_producer_target
    (source : ReconfiguredExecutionState independentLearnedRequirementFamily)
    (encoding : LearnedRequirementEncodingWitness source)
    (sourceAction : LearnedActionWitness source) :
    (executeLearnedExtendedReconfigurationFromState source encoding
        sourceAction).targetState.system =
      (learnedExtendedRawReconfigurationForState source).targetSystem :=
  executeLearnedExtendedReconfigurationFromState_target_is_produced
    source encoding sourceAction

theorem aligned_proposal_is_derived_from_same_execution :
    learnedAlignedReconfiguration.targetSystem.proposal
        independentLearnedCertifiedInput =
      independentLearnedRequirementFamily.requiredProposal
        independentLearnedCertifiedInput.requirement
        independentLearnedCertifiedInput.context :=
  learnedAlignedReconfiguredProposalDerivation.proposal_exact

theorem extended_proposal_is_derived_from_same_execution :
    learnedExtendedReconfiguration.targetSystem.proposal
        independentLearnedCertifiedInput =
      independentLearnedRequirementFamily.requiredProposal
        independentLearnedCertifiedInput.requirement
        independentLearnedCertifiedInput.context :=
  learnedExtendedReconfiguredProposalDerivation.proposal_exact

theorem aligned_local_composition_is_nonidentity :
    learnedAlignedComposedSourceTransformation 0 = 1 :=
  learnedAlignedComposedSourceTransformation_nonidentity

theorem extended_local_composition_is_nonidentity :
    learnedExtendedComposedSourceTransformation 0 = 1 :=
  learnedExtendedComposedSourceTransformation_nonidentity

theorem aligned_source_occurrence_is_composed_output :
    (ActivationOccurrence.neuronOutput learnedAlignedPrimaryNeuron :
        ActivationOccurrence
          (learnedDecodedAlignedArtifact.system.run
            independentLearnedCertifiedInput)).value =
      learnedAlignedComposedSourceTransformation
        (ActivationOccurrence.receivedInput learnedAlignedContextPort :
          ActivationOccurrence
            (learnedDecodedAlignedArtifact.system.run
              independentLearnedCertifiedInput)).value :=
  learnedAlignedComposedSourceTransformation_output_exact

theorem extended_source_occurrence_is_composed_output :
    (ActivationOccurrence.neuronOutput learnedExtendedPrimaryNeuron :
        ActivationOccurrence
          (learnedDecodedExtendedArtifact.system.run
            independentLearnedCertifiedInput)).value =
      learnedExtendedComposedSourceTransformation
        (ActivationOccurrence.receivedInput learnedExtendedContextPort :
          ActivationOccurrence
            (learnedDecodedExtendedArtifact.system.run
              independentLearnedCertifiedInput)).value :=
  learnedExtendedComposedSourceTransformation_output_exact

def aligned_source_role_is_consumed :
    CausalRole learnedAlignedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedRequiredMechanismTransport.sourcePort) :=
  learnedAlignedRequiredMechanismTransport.sourceRole

def aligned_requirement_role_is_consumed :
    CausalRole learnedAlignedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedRequiredMechanismTransport.requirementPort) :=
  learnedAlignedRequiredMechanismTransport.requirementRole

def aligned_authorization_role_is_consumed :
    CausalRole learnedAlignedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedAlignedRequiredMechanismTransport.authorizationPort) :=
  learnedAlignedRequiredMechanismTransport.authorizationRole

def extended_source_role_is_consumed :
    CausalRole learnedExtendedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedRequiredMechanismTransport.sourcePort) :=
  learnedExtendedRequiredMechanismTransport.sourceRole

def extended_requirement_role_is_consumed :
    CausalRole learnedExtendedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedRequiredMechanismTransport.requirementPort) :=
  learnedExtendedRequiredMechanismTransport.requirementRole

def extended_authorization_role_is_consumed :
    CausalRole learnedExtendedReconfiguration.targetSystem
      independentLearnedCertifiedInput
      (.receivedInput learnedExtendedRequiredMechanismTransport.authorizationPort) :=
  learnedExtendedRequiredMechanismTransport.authorizationRole

def alignedProduction := learnedReferenceTransitionProduction.production

theorem aligned_production_action_is_exact :
    alignedProduction.action =
      executeLearnedAlignedReconfigurationFromState
        learnedInitialCheckedAgent.state
        learnedInitialCheckedAgent.certificate.requirementEncodingWitness
        learnedInitialCheckedAgent.certificate.proposalActionWitness :=
  alignedProduction.actionExact

theorem aligned_production_event_memory_are_same_effect :
    alignedProduction.action.result =
      Agent.executeInput learnedInitialCheckedAgent.state.memory
        alignedProduction.action.request :=
  alignedProduction.action.resultExact

theorem aligned_production_successor_is_same_effect :
    learnedProducedTransitionTarget learnedInitialCheckedAgent
        learnedOperationalTransition .installAligned alignedProduction =
      alignedProduction.action.targetState := by
  rfl

def extendedProduction := learnedExtendedReferenceTransitionProduction.production

theorem extended_production_action_is_exact :
    extendedProduction.action =
      executeLearnedExtendedReconfigurationFromState
        LearnedAlignedCheckedAgent.state
        LearnedAlignedCheckedAgent.certificate.requirementEncodingWitness
        LearnedAlignedCheckedAgent.certificate.proposalActionWitness :=
  extendedProduction.actionExact

theorem extended_production_event_memory_are_same_effect :
    extendedProduction.action.result =
      Agent.executeInput LearnedAlignedCheckedAgent.state.memory
        extendedProduction.action.request :=
  extendedProduction.action.resultExact

theorem extended_production_successor_is_same_effect :
    learnedProducedTransitionTarget LearnedAlignedCheckedAgent
        learnedExtendedOperationalTransition
        learnedExtendedReferenceTransitionMaterial
        extendedProduction =
      extendedProduction.action.targetState := by
  rfl

/-! ## F2 regression: the successive path consumes received data -/

theorem successive_analysis_installs_received_artifact
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.artifact analysis.executed.decoded.target :=
  analysis.receivedDecodedArtifact_installed

theorem successive_analysis_installs_received_naming
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.targetNaming analysis.executed.decoded.stable.naming :=
  analysis.receivedDecodedStableNaming_installed

theorem successive_analysis_installs_received_production
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.state analysis.executed.production.targetState :=
  analysis.receivedProductionTarget_installed

theorem successive_analysis_installs_received_assembly
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedSuccessiveEngineAnalysis source) :
    HEq analysis.target.structuralAssembly analysis.structuralAssembly :=
  analysis.receivedStructuralAssembly_installed

theorem successive_checker_consumes_returned_analysis
    (source : LearnedSerializedConstitutiveUpdate)
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (decodedExact : decodeLearnedSuccessiveUpdate source = .ok decoded)
    (analysis : LearnedSuccessiveEngineAnalysis source)
    (accepted : analyzeDecodedLearnedSuccessiveUpdate source decoded decodedExact =
      .ok analysis) :
    checkDecodedLearnedExtendedSerializedUpdate source decoded decodedExact =
      .ok (dependentCheckedUpdateResult
        (buildIncrementalCheckedUpdate analysis.target)) :=
  checkDecodedLearnedExtendedSerializedUpdate_of_analysis source decoded
    decodedExact analysis accepted

theorem successive_declared_domain_acceptance_agrees
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    GenericIncrementalUpdateAccepted learnedSuccessiveIncrementalCheckerEngine
        source ↔
      FullRecheckAccepted learnedSuccessiveFullRecheckEngine source :=
  learnedSuccessiveIncrementalAndFullAcceptance_equivalent_on_declared_domain
    source conditions

theorem successive_declared_domain_successors_agree
    (source : LearnedSerializedConstitutiveUpdate)
    (conditions : LearnedSuccessiveLocalConditionData source) :
    Exists fun incrementalSuccess : GenericIncrementalCheckSuccess
        learnedSuccessiveIncrementalCheckerEngine source =>
      checkGenericIncrementalUpdate learnedSuccessiveIncrementalCheckerEngine
          source = .ok incrementalSuccess ∧
      Exists fun fullSuccess : FullRecheckSuccess
          learnedSuccessiveFullRecheckEngine source =>
        checkFullUpdate learnedSuccessiveFullRecheckEngine source =
            .ok fullSuccess ∧
        HEq incrementalSuccess.checked.next fullSuccess.checked.next :=
  learnedSuccessiveIncrementalAndFullSuccessor_exact_on_declared_domain
    source conditions

theorem successive_runtime_installs_calculated_assembly :
    learnedExtendedCertifiedRuntime.current.certificate.structuralObservations =
      learnedSuccessiveCalculatedStructuralAssembly.observations :=
  learnedExtendedRuntime_certificate_consumes_successiveAssembly

/-- The named first runtime is the material payload retained by its executed
submission receipt, not a separately reconstructed equal runtime. -/
theorem aligned_named_runtime_is_submitted_payload :
    learnedAlignedCertifiedRuntime = learnedAlignedRuntimeSubmission.next := by
  rfl

/-- The named successive runtime is likewise the exact payload retained from
the second executed submission. -/
theorem successive_named_runtime_is_submitted_payload :
    learnedExtendedCertifiedRuntime = learnedExtendedRuntimeSubmission.next := by
  rfl

end Tests.Mechanisms.NeuralL3CausalProduction
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_reconfiguration_is_produced_target
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_reconfiguration_is_produced_target
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_state_configuration_is_exact_producer_output
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_state_successor_uses_exact_producer_target
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_state_configuration_is_exact_producer_output
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_state_successor_uses_exact_producer_target
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_proposal_is_derived_from_same_execution
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_proposal_is_derived_from_same_execution
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_local_composition_is_nonidentity
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_local_composition_is_nonidentity
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_source_occurrence_is_composed_output
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_source_occurrence_is_composed_output
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_source_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_requirement_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_authorization_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_source_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_requirement_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_authorization_role_is_consumed
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_action_is_exact
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_event_memory_are_same_effect
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_production_successor_is_same_effect
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_production_action_is_exact
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_production_event_memory_are_same_effect
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.extended_production_successor_is_same_effect
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_analysis_installs_received_artifact
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_analysis_installs_received_naming
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_analysis_installs_received_production
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_analysis_installs_received_assembly
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_checker_consumes_returned_analysis
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_declared_domain_acceptance_agrees
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_declared_domain_successors_agree
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_runtime_installs_calculated_assembly
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.aligned_named_runtime_is_submitted_payload
#print axioms Tests.Mechanisms.NeuralL3CausalProduction.successive_named_runtime_is_submitted_payload
/- AXIOM_AUDIT_END -/
