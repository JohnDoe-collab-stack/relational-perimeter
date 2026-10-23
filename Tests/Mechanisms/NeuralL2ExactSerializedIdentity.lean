import RelationalPerimeter

/-!
# L2 regression: exact serialized material and stable identities

The runtime decoder is indexed by the exact checked source.  Successful
incremental analysis retains the artifact returned by decoding the received
network and the naming decoded from the received stable serials.  The second
version follows the same discipline instead of discarding its decoder result.
-/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

def learnedInitialCurrentDecodedReceipt :
    DecodedLearnedRuntimeUpdateAtCurrent learnedInitialCheckedAgent
      learnedAlignedRuntimeUpdate :=
  match exact : decodeLearnedRuntimeUpdateAtCurrent
      learnedAlignedRuntimeUpdate with
  | .ok decoded => decoded
  | .error _ => False.elim (by cases exact)

def learnedAlignedCurrentDecodedReceipt :
    DecodedLearnedRuntimeUpdateAtCurrent LearnedAlignedCheckedAgent
      learnedExtendedRuntimeUpdate :=
  match exact : decodeLearnedRuntimeUpdateAtCurrent
      learnedExtendedRuntimeUpdate with
  | .ok decoded => decoded
  | .error _ => False.elim (by cases exact)

def learnedRenamedExecutableDecodedReceipt :
    LearnedExecutableDecodedArtifact learnedReceivedRenamedArtifact :=
  match exact : decodeLearnedExecutableArtifact learnedReceivedRenamedArtifact with
  | .ok decoded => decoded
  | .error _ => False.elim (by cases exact)

theorem initial_current_decoder_accepts_exact_received_update :
    decodeLearnedRuntimeUpdateAtCurrent learnedAlignedRuntimeUpdate =
      .ok learnedInitialCurrentDecodedReceipt := by
  rfl

theorem aligned_current_decoder_accepts_exact_successive_update :
    decodeLearnedRuntimeUpdateAtCurrent learnedExtendedRuntimeUpdate =
      .ok learnedAlignedCurrentDecodedReceipt := by
  rfl

theorem current_decoder_rejects_wrong_successor_version :
    decodeLearnedRuntimeUpdateAtCurrent learnedWrongSuccessiveRuntimeUpdate =
      .error .unexpectedTransition := by
  rfl

theorem full_decoder_accepts_exact_renamed_received_artifact :
    decodeLearnedExecutableArtifact learnedReceivedRenamedArtifact =
      .ok learnedRenamedExecutableDecodedReceipt := by
  rfl

theorem full_decoder_preserves_received_renamed_input_identity :
    learnedRenamedExecutableDecodedReceipt.stableNaming.naming.inputSerial
        ⟨0, by decide⟩ = 1100 := by
  rfl

theorem learned_full_checker_retains_received_artifact_decoder_receipt
    {source : LearnedReceivedArtifact}
    (decoded : LearnedExecutableDecodedArtifact source) :
    decodeArtifact (learnedOperationalContract decoded.contract)
        source.network = .ok decoded.artifact :=
  decoded.artifact_decoded_exact

theorem learned_full_checker_retains_received_naming_decoder_receipt
    {source : LearnedReceivedArtifact}
    (decoded : LearnedExecutableDecodedArtifact source) :
    decodeStableArtifactNaming decoded.artifact source.stableNaming =
      .ok decoded.stableNaming :=
  decoded.stable_naming_decoded_exact

theorem learned_analysis_installs_received_decoded_artifact
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    HEq analysis.target.artifact analysis.executed.decoded.target :=
  analysis.receivedDecodedArtifact_installed

theorem learned_analysis_installs_received_decoded_naming
    {source : LearnedSerializedConstitutiveUpdate}
    (analysis : LearnedIncrementalEngineAnalysis source) :
    HEq analysis.target.targetNaming
      analysis.executed.decoded.stable.naming :=
  analysis.receivedDecodedStableNaming_installed

theorem learned_second_update_installs_received_decoded_artifact
    {source : LearnedSerializedConstitutiveUpdate}
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (targetExact :
      source.targetNetwork = independentLearnedSecondSuccessorNetwork) :
    HEq (learnedReceivedExtendedCheckedUpdate decoded
      targetExact).next.artifact decoded.target :=
  learnedReceivedExtendedCheckedUpdate_artifact_exact decoded targetExact

theorem learned_second_update_installs_received_decoded_naming
    {source : LearnedSerializedConstitutiveUpdate}
    (decoded : DecodedLearnedSuccessiveUpdate source)
    (targetExact :
      source.targetNetwork = independentLearnedSecondSuccessorNetwork) :
    HEq (learnedReceivedExtendedCheckedUpdate decoded
      targetExact).next.certificate.basis.naming decoded.stable.naming :=
  learnedReceivedExtendedCheckedUpdate_naming_exact decoded targetExact

theorem learned_renamed_serialized_identity_remains_installed :
    learnedRenamedIdentityCertifiedRuntime.current.certificate.basis.naming.inputSerial
        ⟨0, by decide⟩ = 1100 :=
  by rfl

def learnedAlignedToExtendedCorrespondence :
    ValidatedStableNodeCorrespondence learnedAlignedStableNaming
      learnedExtendedStableNaming :=
  calculateStableNodeCorrespondence learnedAlignedStableNaming
    learnedExtendedStableNaming

theorem learned_preserved_identity_maps_independently_of_position_type :
    learnedAlignedToExtendedCorrespondence.neuronMap ⟨0, by decide⟩ =
      some ⟨0, by decide⟩ := by
  rfl

theorem learned_same_position_with_renamed_identity_is_not_transportable :
    (learnedPreCertificateGraphFor
      learnedRenamedStableNaming).correspondence.inputMap ⟨0, by decide⟩ =
        none := by
  rfl

theorem learned_insert_delete_reindex_are_distinguished :
    serializedStableKeyChanges [110, 111] [111, 117] =
      [ .deleted 110 0, .reindexed 111 1 0, .inserted 117 1 ] := by
  rfl

theorem learned_nontransportable_renamed_fragments_are_invalidated :
    learnedRenamedTransportedStructuralFragments = [] := by
  rfl

theorem learned_invalidated_renamed_fragments_are_recomputed :
    learnedRenamedRecomputedStructuralFragments =
      learnedRenamedPreCertificateGraph.targetObservations := by
  rfl

theorem learned_inserted_identity_has_no_old_position :
    serializedStableKeyChanges learnedAlignedSerializedNaming.neuronKeys
        learnedExtendedSerializedNaming.neuronKeys =
      [ .preserved 110 0,
        .preserved 111 1,
        .preserved 112 2,
        .preserved 113 3,
        .preserved 114 4,
        .preserved 115 5,
        .preserved 116 6,
        .inserted 117 7 ] := by
  rfl

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.initial_current_decoder_accepts_exact_received_update
#print axioms ConstitutiveSearch.NeuralAgent.Tests.aligned_current_decoder_accepts_exact_successive_update
#print axioms ConstitutiveSearch.NeuralAgent.Tests.current_decoder_rejects_wrong_successor_version
#print axioms ConstitutiveSearch.NeuralAgent.Tests.full_decoder_accepts_exact_renamed_received_artifact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.full_decoder_preserves_received_renamed_input_identity
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_full_checker_retains_received_artifact_decoder_receipt
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_full_checker_retains_received_naming_decoder_receipt
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_analysis_installs_received_decoded_artifact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_analysis_installs_received_decoded_naming
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_second_update_installs_received_decoded_artifact
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_second_update_installs_received_decoded_naming
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_renamed_serialized_identity_remains_installed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_preserved_identity_maps_independently_of_position_type
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_same_position_with_renamed_identity_is_not_transportable
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_insert_delete_reindex_are_distinguished
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_nontransportable_renamed_fragments_are_invalidated
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_invalidated_renamed_fragments_are_recomputed
#print axioms ConstitutiveSearch.NeuralAgent.Tests.learned_inserted_identity_has_no_old_position
/- AXIOM_AUDIT_END -/
