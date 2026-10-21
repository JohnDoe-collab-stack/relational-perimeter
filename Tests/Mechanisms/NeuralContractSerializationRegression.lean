import RelationalPerimeter.Agents.Neural.SerializedNativeSystem

namespace Tests.Mechanisms.NeuralContractSerializationRegression
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent

def fixedMetaContract : ConstitutiveMetaContract :=
  publicConstitutiveMetaContract

def admittedOperationalTransition : OperationalContractTransition
    publicConstitutiveMetaContract .initial .reconfigured :=
  publicOperationalTransition

def transportedActionDistinction :
    PublicActionDistinctionWitness :=
  publicTransition_preservesActionDistinction

def recheckedAuthorization : PublicAuthorizationWitness
    (RequirementInput.mk .scopeOne .direct) :=
  publicTransition_rechecksAuthorization

def producedReconfiguredHistoricalState :
    PublicProducedReconfiguredStateWitness
      publicContractTransitionProduction.targetState :=
  publicContractTransitionHistoricalWitness

theorem serializedArtifact_decodes_to_complete_system :
    decodeArtifact PublicInitialOperationalContract
      publicSerializedRequirementNetwork =
        .ok publicDecodedRequirementArtifact :=
  publicSerializedRequirementNetwork_decodes

theorem decoded_program_is_exactly_serialized_program :
    serializeProgram publicDecodedRequirementArtifact.system.program =
      publicSerializedRequirementNetwork.neurons :=
  publicDecodedRequirementArtifact.decodingExact.neuronsExact

theorem decoded_outputs_are_exactly_serialized_outputs :
    publicDecodedRequirementArtifact.system.outputs.sources.map Fin.val =
      publicSerializedRequirementNetwork.outputs :=
  publicDecodedRequirementArtifact.decodingExact.outputsExact

theorem decoded_system_executes_public_proposal
    (input : PublicRequirementInput) :
    publicDecodedRequirementArtifact.system.proposal input =
      publicRequirementFamily.requiredProposal input.requirement input.context :=
  publicDecodedRequirementArtifact_proposal_exact input

theorem future_reference_is_rejected_before_system_construction :
    decodeArtifact PublicInitialOperationalContract
      invalidForwardReferenceNetwork = .error .invalidPriorNeuron :=
  invalidForwardReferenceNetwork_rejected

theorem mismatched_input_count_is_rejected_before_system_construction :
    decodeArtifact PublicInitialOperationalContract
      mismatchedInputCountNetwork = .error .inputCountMismatch :=
  mismatchedInputCountNetwork_rejected

theorem invalid_received_input_is_rejected_before_system_construction :
    decodeArtifact PublicInitialOperationalContract
      invalidReceivedInputNetwork = .error .invalidReceivedInput :=
  invalidReceivedInputNetwork_rejected

theorem invalid_output_is_rejected_before_system_construction :
    decodeArtifact PublicInitialOperationalContract invalidOutputNetwork =
      .error .invalidOutput :=
  invalidOutputNetwork_rejected

theorem empty_outputs_are_rejected_before_system_construction :
    decodeArtifact PublicInitialOperationalContract emptyOutputNetwork =
      .error .emptyOutputs :=
  emptyOutputNetwork_rejected

end Tests.Mechanisms.NeuralContractSerializationRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.fixedMetaContract
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.admittedOperationalTransition
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.transportedActionDistinction
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.recheckedAuthorization
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.producedReconfiguredHistoricalState
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.serializedArtifact_decodes_to_complete_system
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.decoded_program_is_exactly_serialized_program
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.decoded_outputs_are_exactly_serialized_outputs
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.decoded_system_executes_public_proposal
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.future_reference_is_rejected_before_system_construction
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.mismatched_input_count_is_rejected_before_system_construction
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.invalid_received_input_is_rejected_before_system_construction
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.invalid_output_is_rejected_before_system_construction
#print axioms Tests.Mechanisms.NeuralContractSerializationRegression.empty_outputs_are_rejected_before_system_construction
/- AXIOM_AUDIT_END -/
