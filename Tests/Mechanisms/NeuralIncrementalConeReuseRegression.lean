import RelationalPerimeter.Agents.Neural.LocalCertificateReuse

/-! Regression checks for the computed affected cone and positive local
certificate-fragment transport. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism (.receivedInput publicReconfigurationRequirementPort))
      (.mechanism (.neuron publicReconfigurationProposalOutput)) :=
  publicReferenceEffectiveRequirementRead

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode (.receivedInput 1)) = false :=
  publicRequirementNode_is_outsideAffectedCone

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode (.receivedInput 2)) = true :=
  publicAuthorizationNode_is_affected

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.artifactNode (.neuron 0)) = true :=
  publicProposalNeuron_is_affected

example :
    affectedConstitutiveNode publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
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
#print axioms ConstitutiveSearch.NeuralAgent.outsideAffectedCone_unchanged
#print axioms ConstitutiveSearch.NeuralAgent.transportCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_payload_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_observed_in_target
/- AXIOM_AUDIT_END -/
