import RelationalPerimeter

namespace Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression
open ConstitutiveSearch ConstitutiveSearch.NeuralAgent

theorem public_contract_names_decode_distinctly :
    SerializedOperationalContractName.initial.decode ≠
      SerializedOperationalContractName.reconfigured.decode := by
  intro same
  cases same

theorem public_transition_name_decodes_exactly :
    decodeOperationalContractTransition publicSerializedOperationalTransition =
      .ok publicOperationalTransition :=
  publicSerializedOperationalTransition_decodes

theorem reversed_transition_name_is_rejected :
    decodeOperationalContractTransition
        { source := .reconfigured, target := .initial } =
      .error .transitionNotAdmitted :=
  reversedSerializedOperationalTransition_rejected

theorem public_initial_artifact_decodes_with_stable_keys :
    decodeSerializedConstitutiveArtifact
        publicSerializedInitialConstitutiveArtifact =
      .ok publicDecodedInitialConstitutiveArtifact :=
  publicSerializedInitialConstitutiveArtifact_decodes

theorem public_reconfigured_artifact_decodes_with_stable_keys :
    decodeSerializedConstitutiveArtifact
        publicSerializedReconfiguredConstitutiveArtifact =
      .ok publicDecodedReconfiguredConstitutiveArtifact :=
  publicSerializedReconfiguredConstitutiveArtifact_decodes

def duplicateInputKeysArtifact : SerializedConstitutiveArtifact :=
  { contract := .reconfigured
    network := publicSerializedReconfiguredNetwork
    stableNaming :=
      { inputKeys := [0, 0, 2]
        neuronKeys := [0, 1]
        outputKeys := [0, 1] } }

theorem duplicate_input_keys_are_rejected :
    decodeSerializedConstitutiveArtifact duplicateInputKeysArtifact =
      .error (.naming .duplicateInputKey) := by
  rfl

def missingInputKeyArtifact : SerializedConstitutiveArtifact :=
  { contract := .reconfigured
    network := publicSerializedReconfiguredNetwork
    stableNaming :=
      { inputKeys := [0, 1]
        neuronKeys := [0, 1]
        outputKeys := [0, 1] } }

theorem missing_input_key_is_rejected :
    decodeSerializedConstitutiveArtifact missingInputKeyArtifact =
      .error (.naming .inputCountMismatch) := by
  rfl

def duplicateNeuronKeysArtifact : SerializedConstitutiveArtifact :=
  { contract := .reconfigured
    network := publicSerializedReconfiguredNetwork
    stableNaming :=
      { inputKeys := [0, 1, 2]
        neuronKeys := [0, 0]
        outputKeys := [0, 1] } }

theorem duplicate_neuron_keys_are_rejected :
    decodeSerializedConstitutiveArtifact duplicateNeuronKeysArtifact =
      .error (.naming .duplicateNeuronKey) := by
  rfl

def duplicateOutputKeysArtifact : SerializedConstitutiveArtifact :=
  { contract := .reconfigured
    network := publicSerializedReconfiguredNetwork
    stableNaming :=
      { inputKeys := [0, 1, 2]
        neuronKeys := [0, 1]
        outputKeys := [0, 0] } }

theorem duplicate_output_keys_are_rejected :
    decodeSerializedConstitutiveArtifact duplicateOutputKeysArtifact =
      .error (.naming .duplicateOutputKey) := by
  rfl

theorem requirement_key_is_read_from_initial_serialized_data :
    publicInitialStableNaming.inputSerial ⟨0, by decide⟩ = 1 := by
  rfl

theorem requirement_key_survives_serialized_reindexing :
    publicReconfiguredStableNaming.inputSerial ⟨1, by decide⟩ = 1 := by
  rfl

theorem public_update_names_the_reconfigured_contract :
    publicSerializedConstitutiveUpdate.targetArtifact.contract =
      .reconfigured := by
  rfl

theorem public_key_changes_detect_insertions_and_reindexing :
    serializedStableArtifactChanges publicSerializedInitialStableNaming
        publicSerializedReconfiguredStableNaming =
      { inputs :=
          [ .reindexed 1 0 1,
            .inserted 0 0,
            .inserted 2 2 ]
        neurons := [ .preserved 0 0, .inserted 1 1 ]
        outputs := [ .preserved 0 0, .inserted 1 1 ] } :=
  publicSerializedStableArtifactChanges_exact

theorem stable_key_changes_detect_deletion :
    serializedStableKeyChanges [0, 1] [1] =
      [ .deleted 0 0, .reindexed 1 1 0 ] := by
  rfl

end Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression
/- AXIOM_AUDIT_BEGIN -/
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.public_contract_names_decode_distinctly
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.public_transition_name_decodes_exactly
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.reversed_transition_name_is_rejected
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.public_initial_artifact_decodes_with_stable_keys
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.public_reconfigured_artifact_decodes_with_stable_keys
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.duplicate_input_keys_are_rejected
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.missing_input_key_is_rejected
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.duplicate_neuron_keys_are_rejected
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.duplicate_output_keys_are_rejected
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.requirement_key_is_read_from_initial_serialized_data
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.requirement_key_survives_serialized_reindexing
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.public_update_names_the_reconfigured_contract
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.public_key_changes_detect_insertions_and_reindexing
#print axioms Tests.Mechanisms.NeuralSerializedConstitutiveArtifactRegression.stable_key_changes_detect_deletion
/- AXIOM_AUDIT_END -/
