import RelationalPerimeter.Agents.Neural.HeterogeneousCausalGraph

/-! Regression checks for stable cross-version identities and the complete
heterogeneous constitutive graph. -/
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

example : publicRequirementPort.val ≠
    publicReconfigurationRequirementPort.val :=
  publicRequirementStableLocation_changes

example :
    (StableNodeId.receivedInput (naming := publicInitialStableNaming)
        publicRequirementPort).key =
      (StableNodeId.receivedInput (naming := publicReconfiguredStableNaming)
        publicReconfigurationRequirementPort).key :=
  publicStableNodeCorrespondence_preserves_requirement_key

example :
    Option.map (TransportedStableNode.target
      (newNaming := publicReconfiguredStableNaming))
        (publicStableNodeCorrespondence.transportNode
          (.receivedInput publicRequirementPort)) =
      some (.receivedInput publicReconfigurationRequirementPort) :=
  publicStableNodeCorrespondence_reindexes_requirement

example : PublicAuthorizationHasOldInputAntecedent -> False :=
  publicAuthorization_has_no_old_input_antecedent

example :
    publicReferenceUpdatedStateCertificate.basis.naming =
      publicReconfiguredStableNaming :=
  publicReferenceGraphNaming_exact

example :
    Option.map (TransportedConstitutiveNode.target
      (newNaming := publicReconfiguredStableNaming))
        (publicStableNodeCorrespondence.transportConstitutiveNode
          (.mechanism (.receivedInput publicRequirementPort))) =
      some (.mechanism
        (.receivedInput publicReconfigurationRequirementPort)) :=
  publicStableConstitutiveCorrespondence_reindexes_requirement

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate
      (.mechanism
        publicReferenceUpdatedStateCertificate.causalCoverage.node)
      (.mechanism (.neuron
        (publicDecodedReconfiguredArtifact.system.outputs.sources.get
          publicReferenceUpdatedStateCertificate.causalCoverage.role.output))) :=
  publicReferenceCausalPropagation

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .decoder .proposal :=
  publicReferenceDecodedProposal

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .proposal .action :=
  publicReferenceProposalInterpreted

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .action .effect :=
  publicReferenceActionEffectuated

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .effect .successor :=
  publicReferenceEffectProducesSuccessor

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .successor .memoryProjection :=
  publicReferenceSuccessorProjectsMemory

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .memoryProjection
      (.contractObservation .coveredFuture) :=
  publicReferenceFutureObserved

example :
    HeterogeneousConstitutiveCausalGraph
      publicReferenceUpdatedStateCertificate .successor
      (.contractObservation .historicalPolicy) :=
  publicReferenceHistoryObserved

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.ValidatedStableNodeCorrespondence
#print axioms ConstitutiveSearch.NeuralAgent.publicStableNodeCorrespondence
#print axioms ConstitutiveSearch.NeuralAgent.ConstitutiveDependency
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceGraphNaming_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicStableConstitutiveCorrespondence_reindexes_requirement
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceCausalPropagation
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceDecodedProposal
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceProposalInterpreted
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceActionEffectuated
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceEffectProducesSuccessor
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceSuccessorProjectsMemory
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceFutureObserved
#print axioms ConstitutiveSearch.NeuralAgent.publicReferenceHistoryObserved
/- AXIOM_AUDIT_END -/
