import RelationalPerimeter.Agents.Neural.ExecutableMetaContract

/-!
# Regression: reflected executable meta-contract interface

The generic interface returns exact dependent witnesses from positive
decisions and assembles a state certificate without recognizing a privileged
public artifact.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent.Tests
open ConstitutiveSearch.NeuralAgent

def reflectedAdmission
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (contract : constitution.Contract)
    (accepted : (interface.admissionDecision contract).result = true) :
    constitution.Admits contract :=
  (interface.admissionDecision contract).accept accepted

def reflectedTransition
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    (request : ContractTransitionRequest constitution)
    (accepted : (interface.transitionDecision request).result = true) :
    OperationalContractTransition constitution request.current request.next :=
  (interface.transitionDecision request).accept accepted

def reflectedBasis
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    (decoded : interface.DecodedArtifact source)
    (accepted : (interface.basisDecision decoded).result = true) :
    FiniteCausalBasis
      (constitution.operational (interface.decodedContract decoded))
      (interface.decodedNeuralArtifact decoded) :=
  (interface.basisDecision decoded).accept accepted

def reflectedStateCertificate
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    {decoded : interface.DecodedArtifact source}
    (accepted : ExecutableStateAcceptance interface decoded) :
    StateConstitutiveCertificate
      (constitution.operational (interface.decodedContract decoded))
      (interface.decodedNeuralArtifact decoded)
      (interface.stateOfArtifact decoded) :=
  interface.certifyState accepted

theorem reflectedArtifactNetwork
    {constitution : ConstitutiveMetaContract}
    (interface : ExecutableMetaContractInterface constitution)
    {source : interface.ReceivedArtifact}
    (decoded : interface.DecodedArtifact source)
    (accepted : interface.decodeReceivedArtifact source = .ok decoded) :
    (interface.decodedNeuralArtifact decoded).source =
      interface.artifactNetwork source :=
  interface.artifactNetwork_reflects decoded accepted

end ConstitutiveSearch.NeuralAgent.Tests
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.Tests.reflectedAdmission
#print axioms ConstitutiveSearch.NeuralAgent.Tests.reflectedTransition
#print axioms ConstitutiveSearch.NeuralAgent.Tests.reflectedBasis
#print axioms ConstitutiveSearch.NeuralAgent.Tests.reflectedStateCertificate
#print axioms ConstitutiveSearch.NeuralAgent.Tests.reflectedArtifactNetwork
/- AXIOM_AUDIT_END -/
