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

/-- A transported observation before target-certificate assembly.  Its
observation equation is stated on the pre-certificate graph calculated from
the delta, so reuse can be licensed before the target certificate exists. -/
structure PreCertificateLocalFragment
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldNaming : StableArtifactNaming oldArtifact}
    {newNaming : StableArtifactNaming newArtifact}
    (graph : PreCertificateConstitutiveGraph oldNaming newNaming)
    (key : StableNodeKey) : Type where
  payload : StableArtifactObservation
  observed : lookupStructuralObservation key graph.targetObservations =
    some payload

/-- Positive evidence that one particular old fragment has a validated target
and that this target lies outside the computed cone. -/
structure Unaffected
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    {newNaming : StableArtifactNaming newArtifact}
    (graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming)
    (source : StableNodeId oldCertificate.basis.naming)
    (_fragment : LocalCertificateFragment oldCertificate source.key) : Type where
  transported : TransportedStableNode newNaming source
  transportedExact : graph.correspondence.transportNode source = some transported
  outside : affectedConstitutiveNode oldCertificate graph
    (.artifactNode source.key) = false

/-- Reuse consumes the old payload and transports it to the exact stable target.
The target observation equation follows from the computed cone theorem. -/
def transportCertificateFragment
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    {newNaming : StableArtifactNaming newArtifact}
    {graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming}
    {source : StableNodeId oldCertificate.basis.naming}
    {fragment : LocalCertificateFragment oldCertificate source.key}
    (unaffected : Unaffected oldCertificate graph source fragment) :
    PreCertificateLocalFragment graph source.key :=
  { payload := fragment.payload
    observed :=
      (outsideAffectedCone_unchanged oldCertificate graph
        source.key unaffected.outside).symm.trans
          fragment.observed }

/-- The transported fragment contains the old payload definitionally. -/
theorem transportCertificateFragment_reuses_payload
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    {newNaming : StableArtifactNaming newArtifact}
    {graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming}
    {source : StableNodeId oldCertificate.basis.naming}
    {fragment : LocalCertificateFragment oldCertificate source.key}
    (unaffected : Unaffected oldCertificate graph source fragment) :
    (transportCertificateFragment unaffected).payload = fragment.payload := by
  rfl

/-- A pre-certificate fragment becomes a target-certificate fragment only
after certificate assembly.  Exactness follows from the common decoded target
naming; no affected-cone decision is recomputed at this later boundary. -/
def realizePreCertificateFragment
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {newState : ReconfiguredExecutionState newContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    (newCertificate :
      StateConstitutiveCertificate newContract newArtifact newState)
    (graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newCertificate.basis.naming)
    (key : StableNodeKey)
    (fragment : PreCertificateLocalFragment graph key) :
    LocalCertificateFragment newCertificate key :=
  { payload := fragment.payload
    observed := by
      rw [structuralObservationSnapshot_exact newCertificate]
      rw [← graph.targetObservationsExact]
      exact fragment.observed }

/-- A target fragment whose provenance is the licensed transport of one exact
source fragment.  The constructor is private so a freshly recomputed target
observation cannot be relabelled as transported. -/
structure LicensedTransportedCertificateFragment
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    (oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState)
    {newNaming : StableArtifactNaming newArtifact}
    (graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming)
    (source : StableNodeId oldCertificate.basis.naming)
    (sourceFragment :
      LocalCertificateFragment oldCertificate source.key) : Type where
  private mk ::
  license : Unaffected oldCertificate graph source sourceFragment
  target : PreCertificateLocalFragment graph source.key
  targetExact : target = transportCertificateFragment license

/-- The sole public construction of a licensed transported fragment consumes
the computed outside-cone witness and performs the actual transport. -/
def licenseTransportedCertificateFragment
    {oldContract newContract : ConstitutiveContract}
    {oldArtifact : DecodedNeuralArtifact oldContract}
    {newArtifact : DecodedNeuralArtifact newContract}
    {oldState : ReconfiguredExecutionState oldContract.family}
    {oldCertificate :
      StateConstitutiveCertificate oldContract oldArtifact oldState}
    {newNaming : StableArtifactNaming newArtifact}
    {graph : PreCertificateConstitutiveGraph
      oldCertificate.basis.naming newNaming}
    {source : StableNodeId oldCertificate.basis.naming}
    {sourceFragment :
      LocalCertificateFragment oldCertificate source.key}
    (license : Unaffected oldCertificate graph source sourceFragment) :
    LicensedTransportedCertificateFragment oldCertificate graph
      source sourceFragment :=
  .mk license (transportCertificateFragment license) rfl

def publicInitialRequirementFragment :
    LocalCertificateFragment publicInitialStateConstitutiveCertificate
      (.receivedInput 1) where
  payload := .receivedInput
  observed := rfl

def publicRequirementNodeTransport :
    TransportedStableNode publicReconfiguredStableNaming
      (StableNodeId.receivedInput
        (naming := publicInitialStateConstitutiveCertificate.basis.naming)
        publicRequirementPort) :=
  { target := .receivedInput publicReconfigurationRequirementPort
    keyExact := rfl }

def publicRequirementFragmentUnaffected :
    Unaffected publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.receivedInput publicRequirementPort)
      publicInitialRequirementFragment where
  transported := publicRequirementNodeTransport
  transportedExact := rfl
  outside := publicRequirementNode_is_outsideAffectedCone

def publicLicensedReusedRequirementFragment :
    LicensedTransportedCertificateFragment
      publicInitialStateConstitutiveCertificate
      publicPreCertificateConstitutiveGraph
      (.receivedInput publicRequirementPort)
      publicInitialRequirementFragment :=
  licenseTransportedCertificateFragment publicRequirementFragmentUnaffected

/-- Closed evidence of actual local reuse: the returned target fragment carries
the source fragment's data, transported through the validated correspondence. -/
def publicReusedRequirementFragment :
    LocalCertificateFragment publicReferenceUpdatedStateCertificate
      (.receivedInput 1) :=
  realizePreCertificateFragment publicReferenceUpdatedStateCertificate
    publicPreCertificateConstitutiveGraph (.receivedInput 1)
    publicLicensedReusedRequirementFragment.target

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
#print axioms ConstitutiveSearch.NeuralAgent.PreCertificateLocalFragment
#print axioms ConstitutiveSearch.NeuralAgent.Unaffected
#print axioms ConstitutiveSearch.NeuralAgent.transportCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.transportCertificateFragment_reuses_payload
#print axioms ConstitutiveSearch.NeuralAgent.realizePreCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.LicensedTransportedCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.licenseTransportedCertificateFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicInitialRequirementFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicRequirementFragmentUnaffected
#print axioms ConstitutiveSearch.NeuralAgent.publicLicensedReusedRequirementFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_payload_exact
#print axioms ConstitutiveSearch.NeuralAgent.publicReusedRequirementFragment_observed_in_target
/- AXIOM_AUDIT_END -/
