import RelationalPerimeter.Agents.Neural.IncrementalChecker

/-! Regression checks for the computed affected cone and positive local
certificate-fragment transport. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    publicPreCertificateConstitutiveGraph.correspondence =
      calculateStableNodeCorrespondence
        publicInitialStateConstitutiveCertificate.basis.naming
        publicReconfiguredStableNaming :=
  publicPreCertificateConstitutiveGraph.correspondenceExact

example :
    publicPreCertificateConstitutiveGraph.targetObservations =
      stableStructuralObservationSnapshot publicReconfiguredStableNaming :=
  publicPreCertificateConstitutiveGraph.targetObservationsExact

example :
    materializeIncrementalConstitutiveArtifact publicIncrementalNeuralUpdate =
      publicSerializedReconfiguredConstitutiveArtifact :=
  publicIncrementalConstitutiveArtifact_exact

example :
    calculateIncrementalPreCertificateResult publicIncrementalNeuralUpdate =
      .ok publicIncrementalPreCertificateResult :=
  calculateIncrementalPreCertificateResult_public_exact

example :
    publicIncrementalCheckedUpdate.affectedCone =
      publicIncrementalCertificateAssembly.affectedCone :=
  publicIncrementalCheckedUpdate.affectedConeExact

def wrongStableNamingUpdate : IncrementalNeuralUpdate :=
  { publicIncrementalNeuralUpdate with
    targetStableNaming := publicSerializedInitialStableNaming }

example :
    checkIncrementalUpdate wrongStableNamingUpdate =
      .error (.malformedConstitutiveArtifact (.naming .inputCountMismatch)) := by
  rfl

def reversedTransitionUpdate : IncrementalNeuralUpdate :=
  { publicIncrementalNeuralUpdate with
    transition := { source := .reconfigured, target := .initial } }

example :
    checkIncrementalUpdate reversedTransitionUpdate =
      .error .noAdmittedTransition := by
  rfl

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism (.receivedInput publicReconfigurationRequirementPort))
      (.mechanism (.neuron publicReconfigurationProposalOutput)) :=
  publicReferenceEffectiveRequirementRead

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode (.receivedInput 1)) = false :=
  publicRequirementNode_is_outsideAffectedCone

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode (.receivedInput 2)) = true :=
  publicAuthorizationNode_is_affected

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.artifactNode (.neuron 0)) = true :=
  publicProposalNeuron_is_affected

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      .action = true :=
  publicAction_is_affected_downstream

example :
    publicReusedRequirementFragment.payload =
      publicInitialRequirementFragment.payload :=
  publicReusedRequirementFragment_payload_exact

example :
    lookupStructuralObservation (.receivedInput 1)
        (structuralObservationSnapshot
          publicReferenceUpdatedStateCertificate) =
      some publicReusedRequirementFragment.payload :=
  publicReusedRequirementFragment_observed_in_target

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.affectedConstitutiveNode
#print axioms ConstitutiveSearch.NeuralAgent.calculatePreCertificateConstitutiveGraph
#print axioms ConstitutiveSearch.NeuralAgent.calculateIncrementalPreCertificateResult
#print axioms ConstitutiveSearch.NeuralAgent.outsideAffectedCone_unchanged
#print axioms ConstitutiveSearch.NeuralAgent.transportCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_payload_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_observed_in_target
/- AXIOM_AUDIT_END -/
