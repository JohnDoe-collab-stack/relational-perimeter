import RelationalPerimeter.Agents.Neural.AffectedConstitutiveCone

/-!
# Positive local certificate reuse

Reuse transports the old fragment itself.  It is available only through a
validated stable-node correspondence and only when the executable affected
cone excludes the transported key.  The new fragment retains the old payload;
no history is replayed and no new observation is substituted for it.
-/
set_option genInjectivity false
namespace ConstitutiveSearch.NeuralAgent

/-- One old structural certificate fragment, indexed by its exact stable key.
The payload is retained as data and its observation equation ties it to the
exact source certificate. -/
structure LocalCertificateFragment
    {contract : ConstitutiveContract}
    {artifact : DecodedNeuralArtifact contract}
    {state : ReconfiguredExecutionState contract.family}
    (certificate : StateConstitutiveCertificate contract artifact state)
    (key : StableNodeKey) : Type where
  payload : StableArtifactObservation
  observed : lookupStructuralObservation key
    (structuralObservationSnapshot certificate) = some payload

/-- Positive evidence that one particular old fragment has a validated target
and that this target lies outside the computed cone. -/
structure Unaffected
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    (newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState)
    (correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming)
    (source : StableNodeId oldCertificate.basis.naming)
    (_fragment : LocalCertificateFragment oldCertificate source.key) : Type where
  transported : TransportedStableNode newCertificate.basis.naming source
  transportedExact : correspondence.transportNode source = some transported
  outside : affectedConstitutiveNode oldCertificate newCertificate
    correspondence (.artifactNode source.key) = false

/-- Reuse consumes the old payload and transports it to the exact stable target.
The target observation equation follows from the computed cone theorem. -/
def transportCertificateFragment
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    {newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState}
    {correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming}
    {source : StableNodeId oldCertificate.basis.naming}
    {fragment : LocalCertificateFragment oldCertificate source.key}
    (unaffected : Unaffected oldCertificate newCertificate correspondence
      source fragment) :
    LocalCertificateFragment newCertificate source.key :=
  { payload := fragment.payload
    observed :=
      (outsideAffectedCone_unchanged oldCertificate newCertificate
        correspondence source.key unaffected.outside).symm.trans
          fragment.observed }

/-- The transported fragment contains the old payload definitionally. -/
theorem transportCertificateFragment_reuses_payload
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    {newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState}
    {correspondence : ValidatedStableNodeCorrespondence
      oldCertificate.basis.naming newCertificate.basis.naming}
    {source : StableNodeId oldCertificate.basis.naming}
    {fragment : LocalCertificateFragment oldCertificate source.key}
    (unaffected : Unaffected oldCertificate newCertificate correspondence
      source fragment) :
    (transportCertificateFragment unaffected).payload = fragment.payload := by
  rfl

def publicInitialRequirementFragment :
    LocalCertificateFragment publicInitialStateConstitutiveCertificate
      (.receivedInput 1) where
  payload := .receivedInput
  observed := rfl

def publicRequirementNodeTransport :
    TransportedStableNode publicReferenceUpdatedStateCertificate.basis.naming
      (StableNodeId.receivedInput
        (naming := publicInitialStateConstitutiveCertificate.basis.naming)
        publicRequirementPort) :=
  { target := .receivedInput publicReconfigurationRequirementPort
    keyExact := rfl }

def publicRequirementFragmentUnaffected :
    Unaffected publicInitialStateConstitutiveCertificate
      publicReferenceUpdatedStateCertificate publicStableNodeCorrespondence
      (.receivedInput publicRequirementPort)
      publicInitialRequirementFragment where
  transported := publicRequirementNodeTransport
  transportedExact := rfl
  outside := publicRequirementNode_is_outsideAffectedCone

/-- Closed evidence of actual local reuse: the returned target fragment carries
the source fragment's data, transported through the validated correspondence. -/
def publicReusedRequirementFragment :
    LocalCertificateFragment publicReferenceUpdatedStateCertificate
      (.receivedInput 1) :=
  transportCertificateFragment publicRequirementFragmentUnaffected

theorem publicReusedRequirementFragment_payload_exact :
    publicReusedRequirementFragment.payload =
      publicInitialRequirementFragment.payload := by
  rfl

theorem publicReusedRequirementFragment_observed_in_target :
    lookupStructuralObservation (.receivedInput 1)
        (structuralObservationSnapshot
          publicReferenceUpdatedStateCertificate) =
      some publicReusedRequirementFragment.payload :=
  publicReusedRequirementFragment.observed

end ConstitutiveSearch.NeuralAgent
/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NeuralAgent.LocalCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.Unaffected
#print axioms ConstitutiveSearch.NeuralAgent.transportCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.transportCertificateFragment_reuses_payload
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialRequirementFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementFragmentUnaffected
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_payload_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_observed_in_target
/- AXIOM_AUDIT_END -/
